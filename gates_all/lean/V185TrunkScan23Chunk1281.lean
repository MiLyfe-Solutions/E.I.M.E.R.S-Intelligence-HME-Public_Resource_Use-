import V185TrunkScan23Chunk1280

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7589209 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 4]
def baseStart_7589209 : Nat := 118140960795 + 7589209 * 2 ^ 59
def prefixEnd_7589209 : Nat := 4983230072969 + 3 ^ 40 * 7589209 * 2
def baseEnd_7589209 : Nat := 3896912004427702918585369

theorem tailTrace_7589209 : CollatzResearch.WordTrace tailWord_7589209 prefixEnd_7589209 3896912004427702918585369 := by
  unfold tailWord_7589209
  simp only [CollatzResearch.WordTrace]
  refine ⟨276801192362599401551834681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184534128241732934367889787 276801192362599401551834681)
  ·
    refine ⟨207600894271949551163876011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276801192362599401551834681 207600894271949551163876011)
    ·
      refine ⟨311401341407924326745814017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207600894271949551163876011 311401341407924326745814017)
      ·
        refine ⟨233551006055943245059360513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311401341407924326745814017 233551006055943245059360513)
        ·
          refine ⟨175163254541957433794520385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233551006055943245059360513 175163254541957433794520385)
          ·
            refine ⟨131372440906468075345890289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175163254541957433794520385 131372440906468075345890289)
            ·
              refine ⟨98529330679851056509417717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131372440906468075345890289 98529330679851056509417717)
              ·
                refine ⟨9237124751236036547757911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98529330679851056509417717 9237124751236036547757911)
                ·
                  refine ⟨13855687126854054821636867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9237124751236036547757911 13855687126854054821636867)
                  ·
                    refine ⟨20783530690281082232455301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13855687126854054821636867 20783530690281082232455301)
                    ·
                      refine ⟨3896912004427702918585369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20783530690281082232455301 3896912004427702918585369)
                      ·
                        rfl

theorem cell23_7589209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_7589209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589209 prefixEnd_7589209 := by exact prefixLift 7589209
  have htrace : WordTrace (prefixWord ++ tailWord_7589209) baseStart_7589209 baseEnd_7589209 := by
    simpa [prefixWord, tailWord_7589209, baseEnd_7589209] using wordTrace_append hprefix tailTrace_7589209
  have hstable : (prefixWord ++ tailWord_7589209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589209).length < 2 ^ (prefixWord ++ tailWord_7589209).sum := by decide
  have hdescent : baseEnd_7589209 < baseStart_7589209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589220 : List Nat := [2, 3, 1, 1, 3, 2, 4, 2, 1, 1, 3]
def baseStart_7589220 : Nat := 118140960795 + 7589220 * 2 ^ 59
def prefixEnd_7589220 : Nat := 4983230072969 + 3 ^ 40 * 7589220 * 2
def baseEnd_7589220 : Nat := 3896917652714902375547819

theorem tailTrace_7589220 : CollatzResearch.WordTrace tailWord_7589220 prefixEnd_7589220 3896917652714902375547819 := by
  unfold tailWord_7589220
  simp only [CollatzResearch.WordTrace]
  refine ⟨138400796782779775215242557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184534395710373033620323409 138400796782779775215242557)
  ·
    refine ⟨51900298793542415705715959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138400796782779775215242557 51900298793542415705715959)
    ·
      refine ⟨77850448190313623558573939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51900298793542415705715959 77850448190313623558573939)
      ·
        refine ⟨116775672285470435337860909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77850448190313623558573939 116775672285470435337860909)
        ·
          refine ⟨43790877107051413251697841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116775672285470435337860909 43790877107051413251697841)
          ·
            refine ⟨32843157830288559938773381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43790877107051413251697841 32843157830288559938773381)
            ·
              refine ⟨6158092093179104988520009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32843157830288559938773381 6158092093179104988520009)
              ·
                refine ⟨4618569069884328741390007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6158092093179104988520009 4618569069884328741390007)
                ·
                  refine ⟨6927853604826493112085011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618569069884328741390007 6927853604826493112085011)
                  ·
                    refine ⟨10391780407239739668127517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6927853604826493112085011 10391780407239739668127517)
                    ·
                      refine ⟨3896917652714902375547819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10391780407239739668127517 3896917652714902375547819)
                      ·
                        rfl

theorem cell23_7589220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_7589220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589220 prefixEnd_7589220 := by exact prefixLift 7589220
  have htrace : WordTrace (prefixWord ++ tailWord_7589220) baseStart_7589220 baseEnd_7589220 := by
    simpa [prefixWord, tailWord_7589220, baseEnd_7589220] using wordTrace_append hprefix tailTrace_7589220
  have hstable : (prefixWord ++ tailWord_7589220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589220).length < 2 ^ (prefixWord ++ tailWord_7589220).sum := by decide
  have hdescent : baseEnd_7589220 < baseStart_7589220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589239 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 4]
def baseStart_7589239 : Nat := 118140960795 + 7589239 * 2 ^ 59
def prefixEnd_7589239 : Nat := 4983230072969 + 3 ^ 40 * 7589239 * 2
def baseEnd_7589239 : Nat := 3896927408847337801210231

theorem tailTrace_7589239 : CollatzResearch.WordTrace tailWord_7589239 prefixEnd_7589239 3896927408847337801210231 := by
  unfold tailWord_7589239
  simp only [CollatzResearch.WordTrace]
  refine ⟨276802286552490716675426771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184534857701660477783617847 276802286552490716675426771)
  ·
    refine ⟨415203429828736075013140157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276802286552490716675426771 415203429828736075013140157)
    ·
      refine ⟨155701286185776028129927559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415203429828736075013140157 155701286185776028129927559)
      ·
        refine ⟨233551929278664042194891339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155701286185776028129927559 233551929278664042194891339)
        ·
          refine ⟨350327893917996063292337009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233551929278664042194891339 350327893917996063292337009)
          ·
            refine ⟨262745920438497047469252757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350327893917996063292337009 262745920438497047469252757)
            ·
              refine ⟨12316215020554549100121223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 262745920438497047469252757 12316215020554549100121223)
              ·
                refine ⟨18474322530831823650181835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12316215020554549100121223 18474322530831823650181835)
                ·
                  refine ⟨27711483796247735475272753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18474322530831823650181835 27711483796247735475272753)
                  ·
                    refine ⟨20783612847185801606454565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27711483796247735475272753 20783612847185801606454565)
                    ·
                      refine ⟨3896927408847337801210231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20783612847185801606454565 3896927408847337801210231)
                      ·
                        rfl

theorem cell23_7589239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_7589239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589239 prefixEnd_7589239 := by exact prefixLift 7589239
  have htrace : WordTrace (prefixWord ++ tailWord_7589239) baseStart_7589239 baseEnd_7589239 := by
    simpa [prefixWord, tailWord_7589239, baseEnd_7589239] using wordTrace_append hprefix tailTrace_7589239
  have hstable : (prefixWord ++ tailWord_7589239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589239).length < 2 ^ (prefixWord ++ tailWord_7589239).sum := by decide
  have hdescent : baseEnd_7589239 < baseStart_7589239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589259 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 3]
def baseStart_7589259 : Nat := 118140960795 + 7589259 * 2 ^ 59
def prefixEnd_7589259 : Nat := 4983230072969 + 3 ^ 40 * 7589259 * 2
def baseEnd_7589259 : Nat := 3896937678460427722960139

theorem tailTrace_7589259 : CollatzResearch.WordTrace tailWord_7589259 prefixEnd_7589259 3896937678460427722960139 := by
  unfold tailWord_7589259
  simp only [CollatzResearch.WordTrace]
  refine ⟨276803016012418260091154831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184535344008278840060769887 276803016012418260091154831)
  ·
    refine ⟨415204524018627390136732247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276803016012418260091154831 415204524018627390136732247)
    ·
      refine ⟨622806786027941085205098371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415204524018627390136732247 622806786027941085205098371)
      ·
        refine ⟨934210179041911627807647557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622806786027941085205098371 934210179041911627807647557)
        ·
          refine ⟨175164408570358430213933917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 934210179041911627807647557 175164408570358430213933917)
          ·
            refine ⟨65686653213884411330225219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175164408570358430213933917 65686653213884411330225219)
            ·
              refine ⟨98529979820826616995337829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65686653213884411330225219 98529979820826616995337829)
              ·
                refine ⟨18474371216404990686625843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98529979820826616995337829 18474371216404990686625843)
                ·
                  refine ⟨27711556824607486029938765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18474371216404990686625843 27711556824607486029938765)
                  ·
                    refine ⟨10391833809227807261227037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27711556824607486029938765 10391833809227807261227037)
                    ·
                      refine ⟨3896937678460427722960139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10391833809227807261227037 3896937678460427722960139)
                      ·
                        rfl

theorem cell23_7589259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 3].length) (baseStart_7589259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589259 prefixEnd_7589259 := by exact prefixLift 7589259
  have htrace : WordTrace (prefixWord ++ tailWord_7589259) baseStart_7589259 baseEnd_7589259 := by
    simpa [prefixWord, tailWord_7589259, baseEnd_7589259] using wordTrace_append hprefix tailTrace_7589259
  have hstable : (prefixWord ++ tailWord_7589259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589259).length < 2 ^ (prefixWord ++ tailWord_7589259).sum := by decide
  have hdescent : baseEnd_7589259 < baseStart_7589259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589260 : List Nat := [2, 2, 1, 2, 1, 3, 4, 3, 1, 2, 2]
def baseStart_7589260 : Nat := 118140960795 + 7589260 * 2 ^ 59
def prefixEnd_7589260 : Nat := 4983230072969 + 3 ^ 40 * 7589260 * 2
def baseEnd_7589260 : Nat := 3896938191941082219047635

theorem tailTrace_7589260 : CollatzResearch.WordTrace tailWord_7589260 prefixEnd_7589260 3896938191941082219047635 := by
  unfold tailWord_7589260
  simp only [CollatzResearch.WordTrace]
  refine ⟨138401526242707318630970617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184535368323609758174627489 138401526242707318630970617)
  ·
    refine ⟨103801144682030488973227963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138401526242707318630970617 103801144682030488973227963)
    ·
      refine ⟨155701717023045733459841945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103801144682030488973227963 155701717023045733459841945)
      ·
        refine ⟨116776287767284300094881459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155701717023045733459841945 116776287767284300094881459)
        ·
          refine ⟨175164431650926450142322189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116776287767284300094881459 175164431650926450142322189)
          ·
            refine ⟨65686661869097418803370821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175164431650926450142322189 65686661869097418803370821)
            ·
              refine ⟨12316249100455766025632029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65686661869097418803370821 12316249100455766025632029)
              ·
                refine ⟨4618593412670912259612011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12316249100455766025632029 4618593412670912259612011)
                ·
                  refine ⟨6927890119006368389418017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618593412670912259612011 6927890119006368389418017)
                  ·
                    refine ⟨5195917589254776292063513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6927890119006368389418017 5195917589254776292063513)
                    ·
                      refine ⟨3896938191941082219047635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195917589254776292063513 3896938191941082219047635)
                      ·
                        rfl

theorem cell23_7589260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_7589260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589260 prefixEnd_7589260 := by exact prefixLift 7589260
  have htrace : WordTrace (prefixWord ++ tailWord_7589260) baseStart_7589260 baseEnd_7589260 := by
    simpa [prefixWord, tailWord_7589260, baseEnd_7589260] using wordTrace_append hprefix tailTrace_7589260
  have hstable : (prefixWord ++ tailWord_7589260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589260).length < 2 ^ (prefixWord ++ tailWord_7589260).sum := by decide
  have hdescent : baseEnd_7589260 < baseStart_7589260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589266 : List Nat := [3, 2, 3, 3, 1, 1, 10]
def baseStart_7589266 : Nat := 118140960795 + 7589266 * 2 ^ 59
def prefixEnd_7589266 : Nat := 4983230072969 + 3 ^ 40 * 7589266 * 2
def baseEnd_7589266 : Nat := 48110386084259372784847

theorem tailTrace_7589266 : CollatzResearch.WordTrace tailWord_7589266 prefixEnd_7589266 48110386084259372784847 := by
  unfold tailWord_7589266
  simp only [CollatzResearch.WordTrace]
  refine ⟨69200817830848225071664913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184535514215595266857773101 69200817830848225071664913)
  ·
    refine ⟨51900613373136168803748685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69200817830848225071664913 51900613373136168803748685)
    ·
      refine ⟨19462730014926063301405757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51900613373136168803748685 19462730014926063301405757)
      ·
        refine ⟨7298523755597273738027159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19462730014926063301405757 7298523755597273738027159)
        ·
          refine ⟨10947785633395910607040739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7298523755597273738027159 10947785633395910607040739)
          ·
            refine ⟨16421678450093865910561109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10947785633395910607040739 16421678450093865910561109)
            ·
              refine ⟨48110386084259372784847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16421678450093865910561109 48110386084259372784847)
              ·
                rfl

theorem cell23_7589266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 10].length) (baseStart_7589266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589266 prefixEnd_7589266 := by exact prefixLift 7589266
  have htrace : WordTrace (prefixWord ++ tailWord_7589266) baseStart_7589266 baseEnd_7589266 := by
    simpa [prefixWord, tailWord_7589266, baseEnd_7589266] using wordTrace_append hprefix tailTrace_7589266
  have hstable : (prefixWord ++ tailWord_7589266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589266).length < 2 ^ (prefixWord ++ tailWord_7589266).sum := by decide
  have hdescent : baseEnd_7589266 < baseStart_7589266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589293 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_7589293 : Nat := 118140960795 + 7589293 * 2 ^ 59
def prefixEnd_7589293 : Nat := 4983230072969 + 3 ^ 40 * 7589293 * 2
def baseEnd_7589293 : Nat := 3896955136802680589934983

theorem tailTrace_7589293 : CollatzResearch.WordTrace tailWord_7589293 prefixEnd_7589293 3896955136802680589934983 := by
  unfold tailWord_7589293
  simp only [CollatzResearch.WordTrace]
  refine ⟨276804256094295083897892533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184536170729530055931928355 276804256094295083897892533)
  ·
    refine ⟨25950399008840164115427425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276804256094295083897892533 25950399008840164115427425)
    ·
      refine ⟨19462799256630123086570569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25950399008840164115427425 19462799256630123086570569)
      ·
        refine ⟨14597099442472592314927927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19462799256630123086570569 14597099442472592314927927)
        ·
          refine ⟨21895649163708888472391891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14597099442472592314927927 21895649163708888472391891)
          ·
            refine ⟨32843473745563332708587837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21895649163708888472391891 32843473745563332708587837)
            ·
              refine ⟨12316302654586249765720439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32843473745563332708587837 12316302654586249765720439)
              ·
                refine ⟨18474453981879374648580659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12316302654586249765720439 18474453981879374648580659)
                ·
                  refine ⟨27711680972819061972870989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18474453981879374648580659 27711680972819061972870989)
                  ·
                    refine ⟨10391880364807148239826621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27711680972819061972870989 10391880364807148239826621)
                    ·
                      refine ⟨3896955136802680589934983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10391880364807148239826621 3896955136802680589934983)
                      ·
                        rfl

theorem cell23_7589293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_7589293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589293 prefixEnd_7589293 := by exact prefixLift 7589293
  have htrace : WordTrace (prefixWord ++ tailWord_7589293) baseStart_7589293 baseEnd_7589293 := by
    simpa [prefixWord, tailWord_7589293, baseEnd_7589293] using wordTrace_append hprefix tailTrace_7589293
  have hstable : (prefixWord ++ tailWord_7589293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589293).length < 2 ^ (prefixWord ++ tailWord_7589293).sum := by decide
  have hdescent : baseEnd_7589293 < baseStart_7589293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589303 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 1, 3, 2]
def baseStart_7589303 : Nat := 118140960795 + 7589303 * 2 ^ 59
def prefixEnd_7589303 : Nat := 4983230072969 + 3 ^ 40 * 7589303 * 2
def baseEnd_7589303 : Nat := 3896960271609225550809937

theorem tailTrace_7589303 : CollatzResearch.WordTrace tailWord_7589303 prefixEnd_7589303 3896960271609225550809937 := by
  unfold tailWord_7589303
  simp only [CollatzResearch.WordTrace]
  refine ⟨276804620824258855605756563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184536413882839237070504375 276804620824258855605756563)
  ·
    refine ⟨415206931236388283408634845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276804620824258855605756563 415206931236388283408634845)
    ·
      refine ⟨155702599213645606278238067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415206931236388283408634845 155702599213645606278238067)
      ·
        refine ⟨233553898820468409417357101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155702599213645606278238067 233553898820468409417357101)
        ·
          refine ⟨87582712057675653531508913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233553898820468409417357101 87582712057675653531508913)
          ·
            refine ⟨65687034043256740148631685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87582712057675653531508913 65687034043256740148631685)
            ·
              refine ⟨12316318883110638777868441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65687034043256740148631685 12316318883110638777868441)
              ·
                refine ⟨9237239162332979083401331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12316318883110638777868441 9237239162332979083401331)
                ·
                  refine ⟨13855858743499468625101997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9237239162332979083401331 13855858743499468625101997)
                  ·
                    refine ⟨5195947028812300734413249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13855858743499468625101997 5195947028812300734413249)
                    ·
                      refine ⟨3896960271609225550809937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195947028812300734413249 3896960271609225550809937)
                      ·
                        rfl

theorem cell23_7589303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 3, 2].length) (baseStart_7589303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589303 prefixEnd_7589303 := by exact prefixLift 7589303
  have htrace : WordTrace (prefixWord ++ tailWord_7589303) baseStart_7589303 baseEnd_7589303 := by
    simpa [prefixWord, tailWord_7589303, baseEnd_7589303] using wordTrace_append hprefix tailTrace_7589303
  have hstable : (prefixWord ++ tailWord_7589303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589303).length < 2 ^ (prefixWord ++ tailWord_7589303).sum := by decide
  have hdescent : baseEnd_7589303 < baseStart_7589303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589319 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_7589319 : Nat := 118140960795 + 7589319 * 2 ^ 59
def prefixEnd_7589319 : Nat := 4983230072969 + 3 ^ 40 * 7589319 * 2
def baseEnd_7589319 : Nat := 3896968487299697488209863

theorem tailTrace_7589319 : CollatzResearch.WordTrace tailWord_7589319 prefixEnd_7589319 3896968487299697488209863 := by
  unfold tailWord_7589319
  simp only [CollatzResearch.WordTrace]
  refine ⟨276805204392200890338339011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184536802928133926892226007 276805204392200890338339011)
  ·
    refine ⟨415207806588301335507508517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276805204392200890338339011 415207806588301335507508517)
    ·
      refine ⟨77851463735306500407657847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415207806588301335507508517 77851463735306500407657847)
      ·
        refine ⟨116777195602959750611486771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77851463735306500407657847 116777195602959750611486771)
        ·
          refine ⟨175165793404439625917230157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116777195602959750611486771 175165793404439625917230157)
          ·
            refine ⟨65687172526664859718961309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175165793404439625917230157 65687172526664859718961309)
            ·
              refine ⟨24632689697499322394610491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65687172526664859718961309 24632689697499322394610491)
              ·
                refine ⟨36949034546248983591915737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24632689697499322394610491 36949034546248983591915737)
                ·
                  refine ⟨27711775909686737693936803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36949034546248983591915737 27711775909686737693936803)
                  ·
                    refine ⟨41567663864530106540905205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27711775909686737693936803 41567663864530106540905205)
                    ·
                      refine ⟨3896968487299697488209863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41567663864530106540905205 3896968487299697488209863)
                      ·
                        rfl

theorem cell23_7589319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_7589319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589319 prefixEnd_7589319 := by exact prefixLift 7589319
  have htrace : WordTrace (prefixWord ++ tailWord_7589319) baseStart_7589319 baseEnd_7589319 := by
    simpa [prefixWord, tailWord_7589319, baseEnd_7589319] using wordTrace_append hprefix tailTrace_7589319
  have hstable : (prefixWord ++ tailWord_7589319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589319).length < 2 ^ (prefixWord ++ tailWord_7589319).sum := by decide
  have hdescent : baseEnd_7589319 < baseStart_7589319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589333 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 4, 2, 2]
def baseStart_7589333 : Nat := 118140960795 + 7589333 * 2 ^ 59
def prefixEnd_7589333 : Nat := 4983230072969 + 3 ^ 40 * 7589333 * 2
def baseEnd_7589333 : Nat := 3896975676028860433434799

theorem tailTrace_7589333 : CollatzResearch.WordTrace tailWord_7589333 prefixEnd_7589333 3896975676028860433434799 := by
  unfold tailWord_7589333
  simp only [CollatzResearch.WordTrace]
  refine ⟨276805715014150170729348653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184537143342766780486232435 276805715014150170729348653)
  ·
    refine ⟨103802143130306314023505745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276805715014150170729348653 103802143130306314023505745)
    ·
      refine ⟨77851607347729735517629309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103802143130306314023505745 77851607347729735517629309)
      ·
        refine ⟨29194352755398650819110991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77851607347729735517629309 29194352755398650819110991)
        ·
          refine ⟨43791529133097976228666487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29194352755398650819110991 43791529133097976228666487)
          ·
            refine ⟨65687293699646964342999731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43791529133097976228666487 65687293699646964342999731)
            ·
              refine ⟨98530940549470446514499597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65687293699646964342999731 98530940549470446514499597)
              ·
                refine ⟨36949102706051417442937349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98530940549470446514499597 36949102706051417442937349)
                ·
                  refine ⟨6927956757384640770550753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36949102706051417442937349 6927956757384640770550753)
                  ·
                    refine ⟨5195967568038480577913065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6927956757384640770550753 5195967568038480577913065)
                    ·
                      refine ⟨3896975676028860433434799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5195967568038480577913065 3896975676028860433434799)
                      ·
                        rfl

theorem cell23_7589333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_7589333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589333 prefixEnd_7589333 := by exact prefixLift 7589333
  have htrace : WordTrace (prefixWord ++ tailWord_7589333) baseStart_7589333 baseEnd_7589333 := by
    simpa [prefixWord, tailWord_7589333, baseEnd_7589333] using wordTrace_append hprefix tailTrace_7589333
  have hstable : (prefixWord ++ tailWord_7589333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589333).length < 2 ^ (prefixWord ++ tailWord_7589333).sum := by decide
  have hdescent : baseEnd_7589333 < baseStart_7589333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589386 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_7589386 : Nat := 118140960795 + 7589386 * 2 ^ 59
def prefixEnd_7589386 : Nat := 4983230072969 + 3 ^ 40 * 7589386 * 2
def baseEnd_7589386 : Nat := 1299000963501182908690685

theorem tailTrace_7589386 : CollatzResearch.WordTrace tailWord_7589386 prefixEnd_7589386 1299000963501182908690685 := by
  unfold tailWord_7589386
  simp only [CollatzResearch.WordTrace]
  refine ⟨69201912020739540195257003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184538432055305440520685341 69201912020739540195257003)
  ·
    refine ⟨103802868031109310292885505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69201912020739540195257003 103802868031109310292885505)
    ·
      refine ⟨77852151023331982719664129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103802868031109310292885505 77852151023331982719664129)
      ·
        refine ⟨58389113267498987039748097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77852151023331982719664129 58389113267498987039748097)
        ·
          refine ⟨43791834950624240279811073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58389113267498987039748097 43791834950624240279811073)
          ·
            refine ⟨32843876212968180209858305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43791834950624240279811073 32843876212968180209858305)
            ·
              refine ⟨24632907159726135157393729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32843876212968180209858305 24632907159726135157393729)
              ·
                refine ⟨18474680369794601368045297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24632907159726135157393729 18474680369794601368045297)
                ·
                  refine ⟨13856010277345951026033973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18474680369794601368045297 13856010277345951026033973)
                  ·
                    refine ⟨1299000963501182908690685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13856010277345951026033973 1299000963501182908690685)
                    ·
                      rfl

theorem cell23_7589386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_7589386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589386 prefixEnd_7589386 := by exact prefixLift 7589386
  have htrace : WordTrace (prefixWord ++ tailWord_7589386) baseStart_7589386 baseEnd_7589386 := by
    simpa [prefixWord, tailWord_7589386, baseEnd_7589386] using wordTrace_append hprefix tailTrace_7589386
  have hstable : (prefixWord ++ tailWord_7589386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589386).length < 2 ^ (prefixWord ++ tailWord_7589386).sum := by decide
  have hdescent : baseEnd_7589386 < baseStart_7589386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589463 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 6]
def baseStart_7589463 : Nat := 118140960795 + 7589463 * 2 ^ 59
def prefixEnd_7589463 : Nat := 4983230072969 + 3 ^ 40 * 7589463 * 2
def baseEnd_7589463 : Nat := 433004714279327213867689

theorem tailTrace_7589463 : CollatzResearch.WordTrace tailWord_7589463 prefixEnd_7589463 433004714279327213867689 := by
  unfold tailWord_7589463
  simp only [CollatzResearch.WordTrace]
  refine ⟨276810456503679202931581043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184540304335786135287720695 276810456503679202931581043)
  ·
    refine ⟨415215684755518804397371565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276810456503679202931581043 415215684755518804397371565)
    ·
      refine ⟨155705881783319551649014337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415215684755518804397371565 155705881783319551649014337)
      ·
        refine ⟨116779411337489663736760753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155705881783319551649014337 116779411337489663736760753)
        ·
          refine ⟨87584558503117247802570565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116779411337489663736760753 87584558503117247802570565)
          ·
            refine ⟨16422104719334483962981981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87584558503117247802570565 16422104719334483962981981)
            ·
              refine ⟨6158289269750431486118243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16422104719334483962981981 6158289269750431486118243)
              ·
                refine ⟨9237433904625647229177365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6158289269750431486118243 9237433904625647229177365)
                ·
                  refine ⟨433004714279327213867689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9237433904625647229177365 433004714279327213867689)
                  ·
                    rfl

theorem cell23_7589463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 6].length) (baseStart_7589463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589463 prefixEnd_7589463 := by exact prefixLift 7589463
  have htrace : WordTrace (prefixWord ++ tailWord_7589463) baseStart_7589463 baseEnd_7589463 := by
    simpa [prefixWord, tailWord_7589463, baseEnd_7589463] using wordTrace_append hprefix tailTrace_7589463
  have hstable : (prefixWord ++ tailWord_7589463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589463).length < 2 ^ (prefixWord ++ tailWord_7589463).sum := by decide
  have hdescent : baseEnd_7589463 < baseStart_7589463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589473 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_7589473 : Nat := 118140960795 + 7589473 * 2 ^ 59
def prefixEnd_7589473 : Nat := 4983230072969 + 3 ^ 40 * 7589473 * 2
def baseEnd_7589473 : Nat := 3897047563320489885684155

theorem tailTrace_7589473 : CollatzResearch.WordTrace tailWord_7589473 prefixEnd_7589473 3897047563320489885684155 := by
  unfold tailWord_7589473
  simp only [CollatzResearch.WordTrace]
  refine ⟨276810821233642974639445073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184540547489095316426296715 276810821233642974639445073)
  ·
    refine ⟨207608115925232230979583805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276810821233642974639445073 207608115925232230979583805)
    ·
      refine ⟨77853043471962086617343927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207608115925232230979583805 77853043471962086617343927)
      ·
        refine ⟨116779565207943129926015891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77853043471962086617343927 116779565207943129926015891)
        ·
          refine ⟨175169347811914694889023837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116779565207943129926015891 175169347811914694889023837)
          ·
            refine ⟨65688505429468010583383939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175169347811914694889023837 65688505429468010583383939)
            ·
              refine ⟨98532758144202015875075909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65688505429468010583383939 98532758144202015875075909)
              ·
                refine ⟨18474892152037877976576733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98532758144202015875075909 18474892152037877976576733)
                ·
                  refine ⟨6928084557014204241216275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18474892152037877976576733 6928084557014204241216275)
                  ·
                    refine ⟨10392126835521306361824413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6928084557014204241216275 10392126835521306361824413)
                    ·
                      refine ⟨3897047563320489885684155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10392126835521306361824413 3897047563320489885684155)
                      ·
                        rfl

theorem cell23_7589473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_7589473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589473 prefixEnd_7589473 := by exact prefixLift 7589473
  have htrace : WordTrace (prefixWord ++ tailWord_7589473) baseStart_7589473 baseEnd_7589473 := by
    simpa [prefixWord, tailWord_7589473, baseEnd_7589473] using wordTrace_append hprefix tailTrace_7589473
  have hstable : (prefixWord ++ tailWord_7589473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589473).length < 2 ^ (prefixWord ++ tailWord_7589473).sum := by decide
  have hdescent : baseEnd_7589473 < baseStart_7589473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589516 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_7589516 : Nat := 118140960795 + 7589516 * 2 ^ 59
def prefixEnd_7589516 : Nat := 4983230072969 + 3 ^ 40 * 7589516 * 2
def baseEnd_7589516 : Nat := 3897069642988633217446457

theorem tailTrace_7589516 : CollatzResearch.WordTrace tailWord_7589516 prefixEnd_7589516 3897069642988633217446457 := by
  unfold tailWord_7589516
  simp only [CollatzResearch.WordTrace]
  refine ⟨138406194786243596491630201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184541593048324795322173601 138406194786243596491630201)
  ·
    refine ⟨103804646089682697368722651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138406194786243596491630201 103804646089682697368722651)
    ·
      refine ⟨155706969134524046053083977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103804646089682697368722651 155706969134524046053083977)
      ·
        refine ⟨116780226850893034539812983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155706969134524046053083977 116780226850893034539812983)
        ·
          refine ⟨175170340276339551809719475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116780226850893034539812983 175170340276339551809719475)
          ·
            refine ⟨262755510414509327714579213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175170340276339551809719475 262755510414509327714579213)
            ·
              refine ⟨98533316405440997892967205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262755510414509327714579213 98533316405440997892967205)
              ·
                refine ⟨18474996826020187104931351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98533316405440997892967205 18474996826020187104931351)
                ·
                  refine ⟨27712495239030280657397027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18474996826020187104931351 27712495239030280657397027)
                  ·
                    refine ⟨41568742858545420986095541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27712495239030280657397027 41568742858545420986095541)
                    ·
                      refine ⟨3897069642988633217446457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41568742858545420986095541 3897069642988633217446457)
                      ·
                        rfl

theorem cell23_7589516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_7589516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589516 prefixEnd_7589516 := by exact prefixLift 7589516
  have htrace : WordTrace (prefixWord ++ tailWord_7589516) baseStart_7589516 baseEnd_7589516 := by
    simpa [prefixWord, tailWord_7589516, baseEnd_7589516] using wordTrace_append hprefix tailTrace_7589516
  have hstable : (prefixWord ++ tailWord_7589516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589516).length < 2 ^ (prefixWord ++ tailWord_7589516).sum := by decide
  have hdescent : baseEnd_7589516 < baseStart_7589516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589536 : List Nat := [2, 1, 1, 4, 3, 1, 2, 9]
def baseStart_7589536 : Nat := 118140960795 + 7589536 * 2 ^ 59
def prefixEnd_7589536 : Nat := 4983230072969 + 3 ^ 40 * 7589536 * 2
def baseEnd_7589536 : Nat := 144336293059323079229495

theorem tailTrace_7589536 : CollatzResearch.WordTrace tailWord_7589536 prefixEnd_7589536 144336293059323079229495 := by
  unfold tailWord_7589536
  simp only [CollatzResearch.WordTrace]
  refine ⟨138406559516207368199494231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184542079354943157599325641 138406559516207368199494231)
  ·
    refine ⟨207609839274311052299241347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138406559516207368199494231 207609839274311052299241347)
    ·
      refine ⟨311414758911466578448862021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207609839274311052299241347 311414758911466578448862021)
      ·
        refine ⟨58390267295899983459161629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311414758911466578448862021 58390267295899983459161629)
        ·
          refine ⟨21896350235962493797185611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58390267295899983459161629 21896350235962493797185611)
          ·
            refine ⟨32844525353943740695778417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21896350235962493797185611 32844525353943740695778417)
            ·
              refine ⟨24633394015457805521833813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32844525353943740695778417 24633394015457805521833813)
              ·
                refine ⟨144336293059323079229495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24633394015457805521833813 144336293059323079229495)
                ·
                  rfl

theorem cell23_7589536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 9].length) (baseStart_7589536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589536 prefixEnd_7589536 := by exact prefixLift 7589536
  have htrace : WordTrace (prefixWord ++ tailWord_7589536) baseStart_7589536 baseEnd_7589536 := by
    simpa [prefixWord, tailWord_7589536, baseEnd_7589536] using wordTrace_append hprefix tailTrace_7589536
  have hstable : (prefixWord ++ tailWord_7589536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589536).length < 2 ^ (prefixWord ++ tailWord_7589536).sum := by decide
  have hdescent : baseEnd_7589536 < baseStart_7589536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589557 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 2, 4]
def baseStart_7589557 : Nat := 118140960795 + 7589557 * 2 ^ 59
def prefixEnd_7589557 : Nat := 4983230072969 + 3 ^ 40 * 7589557 * 2
def baseEnd_7589557 : Nat := 1299030231898489185677923

theorem tailTrace_7589557 : CollatzResearch.WordTrace tailWord_7589557 prefixEnd_7589557 1299030231898489185677923 := by
  unfold tailWord_7589557
  simp only [CollatzResearch.WordTrace]
  refine ⟨276813884965338656985502925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184542589976892437990335283 276813884965338656985502925)
  ·
    refine ⟨103805206862001996369563597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276813884965338656985502925 103805206862001996369563597)
    ·
      refine ⟨38926952573250748638586349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103805206862001996369563597 38926952573250748638586349)
      ·
        refine ⟨14597607214969030739469881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38926952573250748638586349 14597607214969030739469881)
        ·
          refine ⟨10948205411226773054602411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14597607214969030739469881 10948205411226773054602411)
          ·
            refine ⟨16422308116840159581903617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10948205411226773054602411 16422308116840159581903617)
            ·
              refine ⟨12316731087630119686427713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16422308116840159581903617 12316731087630119686427713)
              ·
                refine ⟨9237548315722589764820785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12316731087630119686427713 9237548315722589764820785)
                ·
                  refine ⟨6928161236791942323615589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9237548315722589764820785 6928161236791942323615589)
                  ·
                    refine ⟨1299030231898489185677923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6928161236791942323615589 1299030231898489185677923)
                    ·
                      rfl

theorem cell23_7589557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_7589557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589557 prefixEnd_7589557 := by exact prefixLift 7589557
  have htrace : WordTrace (prefixWord ++ tailWord_7589557) baseStart_7589557 baseEnd_7589557 := by
    simpa [prefixWord, tailWord_7589557, baseEnd_7589557] using wordTrace_append hprefix tailTrace_7589557
  have hstable : (prefixWord ++ tailWord_7589557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589557).length < 2 ^ (prefixWord ++ tailWord_7589557).sum := by decide
  have hdescent : baseEnd_7589557 < baseStart_7589557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589558 : List Nat := [5, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_7589558 : Nat := 118140960795 + 7589558 * 2 ^ 59
def prefixEnd_7589558 : Nat := 4983230072969 + 3 ^ 40 * 7589558 * 2
def baseEnd_7589558 : Nat := 3897091209176122053121265

theorem tailTrace_7589558 : CollatzResearch.WordTrace tailWord_7589558 prefixEnd_7589558 3897091209176122053121265 := by
  unfold tailWord_7589558
  simp only [CollatzResearch.WordTrace]
  refine ⟨17300870089895939634768083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184542614292223356104192885 17300870089895939634768083)
  ·
    refine ⟨25951305134843909452152125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17300870089895939634768083 25951305134843909452152125)
    ·
      refine ⟨9731739425566466044557047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25951305134843909452152125 9731739425566466044557047)
      ·
        refine ⟨14597609138349699066835571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9731739425566466044557047 14597609138349699066835571)
        ·
          refine ⟨21896413707524548600253357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14597609138349699066835571 21896413707524548600253357)
          ·
            refine ⟨8211155140321705725095009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21896413707524548600253357 8211155140321705725095009)
            ·
              refine ⟨6158366355241279293821257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8211155140321705725095009 6158366355241279293821257)
              ·
                refine ⟨4618774766430959470365943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6158366355241279293821257 4618774766430959470365943)
                ·
                  refine ⟨6928162149646439205548915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618774766430959470365943 6928162149646439205548915)
                  ·
                    refine ⟨10392243224469658808323373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6928162149646439205548915 10392243224469658808323373)
                    ·
                      refine ⟨3897091209176122053121265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10392243224469658808323373 3897091209176122053121265)
                      ·
                        rfl

theorem cell23_7589558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_7589558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589558 prefixEnd_7589558 := by exact prefixLift 7589558
  have htrace : WordTrace (prefixWord ++ tailWord_7589558) baseStart_7589558 baseEnd_7589558 := by
    simpa [prefixWord, tailWord_7589558, baseEnd_7589558] using wordTrace_append hprefix tailTrace_7589558
  have hstable : (prefixWord ++ tailWord_7589558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589558).length < 2 ^ (prefixWord ++ tailWord_7589558).sum := by decide
  have hdescent : baseEnd_7589558 < baseStart_7589558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589563 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 4, 1, 3]
def baseStart_7589563 : Nat := 118140960795 + 7589563 * 2 ^ 59
def prefixEnd_7589563 : Nat := 4983230072969 + 3 ^ 40 * 7589563 * 2
def baseEnd_7589563 : Nat := 3897093776579394533558741

theorem tailTrace_7589563 : CollatzResearch.WordTrace tailWord_7589563 prefixEnd_7589563 3897093776579394533558741 := by
  unfold tailWord_7589563
  simp only [CollatzResearch.WordTrace]
  refine ⟨276814103803316920010221343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184542735868877946673480895 276814103803316920010221343)
  ·
    refine ⟨415221155704975380015332015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276814103803316920010221343 415221155704975380015332015)
    ·
      refine ⟨622831733557463070022998023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415221155704975380015332015 622831733557463070022998023)
      ·
        refine ⟨934247600336194605034497035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622831733557463070022998023 934247600336194605034497035)
        ·
          refine ⟨1401371400504291907551745553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934247600336194605034497035 1401371400504291907551745553)
          ·
            refine ⟨1051028550378218930663809165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401371400504291907551745553 1051028550378218930663809165)
            ·
              refine ⟨394135706391832098998928437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1051028550378218930663809165 394135706391832098998928437)
              ·
                refine ⟨36950222474234259281149541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 394135706391832098998928437 36950222474234259281149541)
                ·
                  refine ⟨6928166713918923615215539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36950222474234259281149541 6928166713918923615215539)
                  ·
                    refine ⟨10392250070878385422823309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6928166713918923615215539 10392250070878385422823309)
                    ·
                      refine ⟨3897093776579394533558741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10392250070878385422823309 3897093776579394533558741)
                      ·
                        rfl

theorem cell23_7589563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 1, 3].length) (baseStart_7589563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589563 prefixEnd_7589563 := by exact prefixLift 7589563
  have htrace : WordTrace (prefixWord ++ tailWord_7589563) baseStart_7589563 baseEnd_7589563 := by
    simpa [prefixWord, tailWord_7589563, baseEnd_7589563] using wordTrace_append hprefix tailTrace_7589563
  have hstable : (prefixWord ++ tailWord_7589563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589563).length < 2 ^ (prefixWord ++ tailWord_7589563).sum := by decide
  have hdescent : baseEnd_7589563 < baseStart_7589563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589564 : List Nat := [2, 2, 2, 3, 1, 3, 1, 4, 1, 2, 2]
def baseStart_7589564 : Nat := 118140960795 + 7589564 * 2 ^ 59
def prefixEnd_7589564 : Nat := 4983230072969 + 3 ^ 40 * 7589564 * 2
def baseEnd_7589564 : Nat := 3897094290060049029646237

theorem tailTrace_7589564 : CollatzResearch.WordTrace tailWord_7589564 prefixEnd_7589564 3897094290060049029646237 := by
  unfold tailWord_7589564
  simp only [CollatzResearch.WordTrace]
  refine ⟨138407070138156648590503873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184542760184208864787338497 138407070138156648590503873)
  ·
    refine ⟨103805302603617486442877905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138407070138156648590503873 103805302603617486442877905)
    ·
      refine ⟨77853976952713114832158429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103805302603617486442877905 77853976952713114832158429)
      ·
        refine ⟨29195241357267418062059411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77853976952713114832158429 29195241357267418062059411)
        ·
          refine ⟨43792862035901127093089117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29195241357267418062059411 43792862035901127093089117)
          ·
            refine ⟨16422323263462922659908419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43792862035901127093089117 16422323263462922659908419)
            ·
              refine ⟨24633484895194383989862629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16422323263462922659908419 24633484895194383989862629)
              ·
                refine ⟨4618778417848946998099243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24633484895194383989862629 4618778417848946998099243)
                ·
                  refine ⟨6928167626773420497148865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618778417848946998099243 6928167626773420497148865)
                  ·
                    refine ⟨5196125720080065372861649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6928167626773420497148865 5196125720080065372861649)
                    ·
                      refine ⟨3897094290060049029646237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196125720080065372861649 3897094290060049029646237)
                      ·
                        rfl

theorem cell23_7589564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_7589564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589564 prefixEnd_7589564 := by exact prefixLift 7589564
  have htrace : WordTrace (prefixWord ++ tailWord_7589564) baseStart_7589564 baseEnd_7589564 := by
    simpa [prefixWord, tailWord_7589564, baseEnd_7589564] using wordTrace_append hprefix tailTrace_7589564
  have hstable : (prefixWord ++ tailWord_7589564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589564).length < 2 ^ (prefixWord ++ tailWord_7589564).sum := by decide
  have hdescent : baseEnd_7589564 < baseStart_7589564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589574 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_7589574 : Nat := 118140960795 + 7589574 * 2 ^ 59
def prefixEnd_7589574 : Nat := 4983230072969 + 3 ^ 40 * 7589574 * 2
def baseEnd_7589574 : Nat := 1299033141622197996840397

theorem tailTrace_7589574 : CollatzResearch.WordTrace tailWord_7589574 prefixEnd_7589574 1299033141622197996840397 := by
  unfold tailWord_7589574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650453281446158402777243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184543003337518045925914517 8650453281446158402777243)
  ·
    refine ⟨12975679922169237604165865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8650453281446158402777243 12975679922169237604165865)
    ·
      refine ⟨9731759941626928203124399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12975679922169237604165865 9731759941626928203124399)
      ·
        refine ⟨14597639912440392304686599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9731759941626928203124399 14597639912440392304686599)
        ·
          refine ⟨21896459868660588457029899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14597639912440392304686599 21896459868660588457029899)
          ·
            refine ⟨32844689802990882685544849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21896459868660588457029899 32844689802990882685544849)
            ·
              refine ⟨24633517352243162014158637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32844689802990882685544849 24633517352243162014158637)
              ·
                refine ⟨9237569007091185755309489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24633517352243162014158637 9237569007091185755309489)
                ·
                  refine ⟨6928176755318389316482117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9237569007091185755309489 6928176755318389316482117)
                  ·
                    refine ⟨1299033141622197996840397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6928176755318389316482117 1299033141622197996840397)
                    ·
                      rfl

theorem cell23_7589574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_7589574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589574 prefixEnd_7589574 := by exact prefixLift 7589574
  have htrace : WordTrace (prefixWord ++ tailWord_7589574) baseStart_7589574 baseEnd_7589574 := by
    simpa [prefixWord, tailWord_7589574, baseEnd_7589574] using wordTrace_append hprefix tailTrace_7589574
  have hstable : (prefixWord ++ tailWord_7589574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589574).length < 2 ^ (prefixWord ++ tailWord_7589574).sum := by decide
  have hdescent : baseEnd_7589574 < baseStart_7589574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589613 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_7589613 : Nat := 118140960795 + 7589613 * 2 ^ 59
def prefixEnd_7589613 : Nat := 4983230072969 + 3 ^ 40 * 7589613 * 2
def baseEnd_7589613 : Nat := 1299039816870706445977837

theorem tailTrace_7589613 : CollatzResearch.WordTrace tailWord_7589613 prefixEnd_7589613 1299039816870706445977837 := by
  unfold tailWord_7589613
  simp only [CollatzResearch.WordTrace]
  refine ⟨276815927453135778549541493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184543951635423852366360995 276815927453135778549541493)
  ·
    refine ⟨25951493198731479239019515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276815927453135778549541493 25951493198731479239019515)
    ·
      refine ⟨38927239798097218858529273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25951493198731479239019515 38927239798097218858529273)
      ·
        refine ⟨29195429848572914143896955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38927239798097218858529273 29195429848572914143896955)
        ·
          refine ⟨43793144772859371215845433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29195429848572914143896955 43793144772859371215845433)
          ·
            refine ⟨32844858579644528411884075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43793144772859371215845433 32844858579644528411884075)
            ·
              refine ⟨49267287869466792617826113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32844858579644528411884075 49267287869466792617826113)
              ·
                refine ⟨36950465902100094463369585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49267287869466792617826113 36950465902100094463369585)
                ·
                  refine ⟨27712849426575070847527189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36950465902100094463369585 27712849426575070847527189)
                  ·
                    refine ⟨1299039816870706445977837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27712849426575070847527189 1299039816870706445977837)
                    ·
                      rfl

theorem cell23_7589613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_7589613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589613 prefixEnd_7589613 := by exact prefixLift 7589613
  have htrace : WordTrace (prefixWord ++ tailWord_7589613) baseStart_7589613 baseEnd_7589613 := by
    simpa [prefixWord, tailWord_7589613, baseEnd_7589613] using wordTrace_append hprefix tailTrace_7589613
  have hstable : (prefixWord ++ tailWord_7589613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589613).length < 2 ^ (prefixWord ++ tailWord_7589613).sum := by decide
  have hdescent : baseEnd_7589613 < baseStart_7589613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589633 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_7589633 : Nat := 118140960795 + 7589633 * 2 ^ 59
def prefixEnd_7589633 : Nat := 4983230072969 + 3 ^ 40 * 7589633 * 2
def baseEnd_7589633 : Nat := 3897129720225209259683419

theorem tailTrace_7589633 : CollatzResearch.WordTrace tailWord_7589633 prefixEnd_7589633 3897129720225209259683419 := by
  unfold tailWord_7589633
  simp only [CollatzResearch.WordTrace]
  refine ⟨276816656913063321965269553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184544437942042214643513035 276816656913063321965269553)
  ·
    refine ⟨207612492684797491473952165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276816656913063321965269553 207612492684797491473952165)
    ·
      refine ⟨38927342378399529651366031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207612492684797491473952165 38927342378399529651366031)
      ·
        refine ⟨58391013567599294477049047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38927342378399529651366031 58391013567599294477049047)
        ·
          refine ⟨87586520351398941715573571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58391013567599294477049047 87586520351398941715573571)
          ·
            refine ⟨131379780527098412573360357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87586520351398941715573571 131379780527098412573360357)
            ·
              refine ⟨24633708848830952357505067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131379780527098412573360357 24633708848830952357505067)
              ·
                refine ⟨36950563273246428536257601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24633708848830952357505067 36950563273246428536257601)
                ·
                  refine ⟨27712922454934821402193201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36950563273246428536257601 27712922454934821402193201)
                  ·
                    refine ⟨20784691841201116051644901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27712922454934821402193201 20784691841201116051644901)
                    ·
                      refine ⟨3897129720225209259683419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20784691841201116051644901 3897129720225209259683419)
                      ·
                        rfl

theorem cell23_7589633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_7589633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589633 prefixEnd_7589633 := by exact prefixLift 7589633
  have htrace : WordTrace (prefixWord ++ tailWord_7589633) baseStart_7589633 baseEnd_7589633 := by
    simpa [prefixWord, tailWord_7589633, baseEnd_7589633] using wordTrace_append hprefix tailTrace_7589633
  have hstable : (prefixWord ++ tailWord_7589633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589633).length < 2 ^ (prefixWord ++ tailWord_7589633).sum := by decide
  have hdescent : baseEnd_7589633 < baseStart_7589633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589638 : List Nat := [6, 2, 2, 1, 1, 2, 2, 7]
def baseStart_7589638 : Nat := 118140960795 + 7589638 * 2 ^ 59
def prefixEnd_7589638 : Nat := 4983230072969 + 3 ^ 40 * 7589638 * 2
def baseEnd_7589638 : Nat := 144338232875128953337811

theorem tailTrace_7589638 : CollatzResearch.WordTrace tailWord_7589638 prefixEnd_7589638 144338232875128953337811 := by
  unfold tailWord_7589638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650526227438912744350049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184544559518696805212801045 8650526227438912744350049)
  ·
    refine ⟨6487894670579184558262537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8650526227438912744350049 6487894670579184558262537)
    ·
      refine ⟨4865921002934388418696903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6487894670579184558262537 4865921002934388418696903)
      ·
        refine ⟨7298881504401582628045355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865921002934388418696903 7298881504401582628045355)
        ·
          refine ⟨10948322256602373942068033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7298881504401582628045355 10948322256602373942068033)
          ·
            refine ⟨8211241692451780456551025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10948322256602373942068033 8211241692451780456551025)
            ·
              refine ⟨6158431269338835342413269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8211241692451780456551025 6158431269338835342413269)
              ·
                refine ⟨144338232875128953337811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6158431269338835342413269 144338232875128953337811)
                ·
                  rfl

theorem cell23_7589638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_7589638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589638 prefixEnd_7589638 := by exact prefixLift 7589638
  have htrace : WordTrace (prefixWord ++ tailWord_7589638) baseStart_7589638 baseEnd_7589638 := by
    simpa [prefixWord, tailWord_7589638, baseEnd_7589638] using wordTrace_append hprefix tailTrace_7589638
  have hstable : (prefixWord ++ tailWord_7589638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589638).length < 2 ^ (prefixWord ++ tailWord_7589638).sum := by decide
  have hdescent : baseEnd_7589638 < baseStart_7589638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589710 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2]
def baseStart_7589710 : Nat := 118140960795 + 7589710 * 2 ^ 59
def prefixEnd_7589710 : Nat := 4983230072969 + 3 ^ 40 * 7589710 * 2
def baseEnd_7589710 : Nat := 3897169258235605458420565

theorem tailTrace_7589710 : CollatzResearch.WordTrace tailWord_7589710 prefixEnd_7589710 3897169258235605458420565 := by
  unfold tailWord_7589710
  simp only [CollatzResearch.WordTrace]
  refine ⟨34602433166723045514477823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184546310222522909410548389 34602433166723045514477823)
  ·
    refine ⟨51903649750084568271716735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34602433166723045514477823 51903649750084568271716735)
    ·
      refine ⟨77855474625126852407575103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51903649750084568271716735 77855474625126852407575103)
      ·
        refine ⟨116783211937690278611362655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77855474625126852407575103 116783211937690278611362655)
        ·
          refine ⟨175174817906535417917043983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116783211937690278611362655 175174817906535417917043983)
          ·
            refine ⟨262762226859803126875565975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175174817906535417917043983 262762226859803126875565975)
            ·
              refine ⟨394143340289704690313348963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262762226859803126875565975 394143340289704690313348963)
              ·
                refine ⟨591215010434557035470023445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394143340289704690313348963 591215010434557035470023445)
                ·
                  refine ⟨27713203614119861037657349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 591215010434557035470023445 27713203614119861037657349)
                  ·
                    refine ⟨5196225677647473944560753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27713203614119861037657349 5196225677647473944560753)
                    ·
                      refine ⟨3897169258235605458420565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196225677647473944560753 3897169258235605458420565)
                      ·
                        rfl

theorem cell23_7589710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_7589710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589710 prefixEnd_7589710 := by exact prefixLift 7589710
  have htrace : WordTrace (prefixWord ++ tailWord_7589710) baseStart_7589710 baseEnd_7589710 := by
    simpa [prefixWord, tailWord_7589710, baseEnd_7589710] using wordTrace_append hprefix tailTrace_7589710
  have hstable : (prefixWord ++ tailWord_7589710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589710).length < 2 ^ (prefixWord ++ tailWord_7589710).sum := by decide
  have hdescent : baseEnd_7589710 < baseStart_7589710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589743 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 3]
def baseStart_7589743 : Nat := 118140960795 + 7589743 * 2 ^ 59
def prefixEnd_7589743 : Nat := 4983230072969 + 3 ^ 40 * 7589743 * 2
def baseEnd_7589743 : Nat := 3897186203097203829307913

theorem tailTrace_7589743 : CollatzResearch.WordTrace tailWord_7589743 prefixEnd_7589743 3897186203097203829307913 := by
  unfold tailWord_7589743
  simp only [CollatzResearch.WordTrace]
  refine ⟨276820668942664810751773883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184547112628443207167849255 276820668942664810751773883)
  ·
    refine ⟨415231003413997216127660825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276820668942664810751773883 415231003413997216127660825)
    ·
      refine ⟨311423252560497912095745619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415231003413997216127660825 311423252560497912095745619)
      ·
        refine ⟨467134878840746868143618429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311423252560497912095745619 467134878840746868143618429)
        ·
          refine ⟨175175579565280075553856911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467134878840746868143618429 175175579565280075553856911)
          ·
            refine ⟨262763369347920113330785367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175175579565280075553856911 262763369347920113330785367)
            ·
              refine ⟨394145054021880169996178051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262763369347920113330785367 394145054021880169996178051)
              ·
                refine ⟨591217581032820254994267077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394145054021880169996178051 591217581032820254994267077)
                ·
                  refine ⟨110853296443653797811425077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 591217581032820254994267077 110853296443653797811425077)
                  ·
                    refine ⟨10392496541592543544821101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110853296443653797811425077 10392496541592543544821101)
                    ·
                      refine ⟨3897186203097203829307913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10392496541592543544821101 3897186203097203829307913)
                      ·
                        rfl

theorem cell23_7589743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 3].length) (baseStart_7589743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589743 prefixEnd_7589743 := by exact prefixLift 7589743
  have htrace : WordTrace (prefixWord ++ tailWord_7589743) baseStart_7589743 baseEnd_7589743 := by
    simpa [prefixWord, tailWord_7589743, baseEnd_7589743] using wordTrace_append hprefix tailTrace_7589743
  have hstable : (prefixWord ++ tailWord_7589743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589743).length < 2 ^ (prefixWord ++ tailWord_7589743).sum := by decide
  have hdescent : baseEnd_7589743 < baseStart_7589743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589761 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_7589761 : Nat := 118140960795 + 7589761 * 2 ^ 59
def prefixEnd_7589761 : Nat := 4983230072969 + 3 ^ 40 * 7589761 * 2
def baseEnd_7589761 : Nat := 3897195445748984758882831

theorem tailTrace_7589761 : CollatzResearch.WordTrace tailWord_7589761 prefixEnd_7589761 3897195445748984758882831 := by
  unfold tailWord_7589761
  simp only [CollatzResearch.WordTrace]
  refine ⟨276821325456599599825929137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184547550304399733217286091 276821325456599599825929137)
  ·
    refine ⟨207615994092449699869446853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276821325456599599825929137 207615994092449699869446853)
    ·
      refine ⟨38927998892334318725521285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207615994092449699869446853 38927998892334318725521285)
      ·
        refine ⟨7298999792312684761035241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38927998892334318725521285 7298999792312684761035241)
        ·
          refine ⟨5474249844234513570776431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7298999792312684761035241 5474249844234513570776431)
          ·
            refine ⟨8211374766351770356164647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474249844234513570776431 8211374766351770356164647)
            ·
              refine ⟨12317062149527655534246971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211374766351770356164647 12317062149527655534246971)
              ·
                refine ⟨18475593224291483301370457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12317062149527655534246971 18475593224291483301370457)
                ·
                  refine ⟨13856694918218612476027843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18475593224291483301370457 13856694918218612476027843)
                  ·
                    refine ⟨20785042377327918714041765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13856694918218612476027843 20785042377327918714041765)
                    ·
                      refine ⟨3897195445748984758882831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20785042377327918714041765 3897195445748984758882831)
                      ·
                        rfl

theorem cell23_7589761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_7589761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589761 prefixEnd_7589761 := by exact prefixLift 7589761
  have htrace : WordTrace (prefixWord ++ tailWord_7589761) baseStart_7589761 baseEnd_7589761 := by
    simpa [prefixWord, tailWord_7589761, baseEnd_7589761] using wordTrace_append hprefix tailTrace_7589761
  have hstable : (prefixWord ++ tailWord_7589761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589761).length < 2 ^ (prefixWord ++ tailWord_7589761).sum := by decide
  have hdescent : baseEnd_7589761 < baseStart_7589761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589784 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 6]
def baseStart_7589784 : Nat := 118140960795 + 7589784 * 2 ^ 59
def prefixEnd_7589784 : Nat := 4983230072969 + 3 ^ 40 * 7589784 * 2
def baseEnd_7589784 : Nat := 433023028422670907655025

theorem tailTrace_7589784 : CollatzResearch.WordTrace tailWord_7589784 prefixEnd_7589784 433023028422670907655025 := by
  unfold tailWord_7589784
  simp only [CollatzResearch.WordTrace]
  refine ⟨138411082167758137377008203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184548109557010849836010937 138411082167758137377008203)
  ·
    refine ⟨207616623251637206065512305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138411082167758137377008203 207616623251637206065512305)
    ·
      refine ⟨155712467438727904549134229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207616623251637206065512305 155712467438727904549134229)
      ·
        refine ⟨7299021911190370525740667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155712467438727904549134229 7299021911190370525740667)
        ·
          refine ⟨10948532866785555788611001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7299021911190370525740667 10948532866785555788611001)
          ·
            refine ⟨8211399650089166841458251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10948532866785555788611001 8211399650089166841458251)
            ·
              refine ⟨12317099475133750262187377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211399650089166841458251 12317099475133750262187377)
              ·
                refine ⟨9237824606350312696640533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12317099475133750262187377 9237824606350312696640533)
                ·
                  refine ⟨433023028422670907655025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9237824606350312696640533 433023028422670907655025)
                  ·
                    rfl

theorem cell23_7589784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 6].length) (baseStart_7589784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589784 prefixEnd_7589784 := by exact prefixLift 7589784
  have htrace : WordTrace (prefixWord ++ tailWord_7589784) baseStart_7589784 baseEnd_7589784 := by
    simpa [prefixWord, tailWord_7589784, baseEnd_7589784] using wordTrace_append hprefix tailTrace_7589784
  have hstable : (prefixWord ++ tailWord_7589784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589784).length < 2 ^ (prefixWord ++ tailWord_7589784).sum := by decide
  have hdescent : baseEnd_7589784 < baseStart_7589784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589817 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 4]
def baseStart_7589817 : Nat := 118140960795 + 7589817 * 2 ^ 59
def prefixEnd_7589817 : Nat := 4983230072969 + 3 ^ 40 * 7589817 * 2
def baseEnd_7589817 : Nat := 3897224200665636539782573

theorem tailTrace_7589817 : CollatzResearch.WordTrace tailWord_7589817 prefixEnd_7589817 3897224200665636539782573 := by
  unfold tailWord_7589817
  simp only [CollatzResearch.WordTrace]
  refine ⟨276823367944396721389967705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184548911962931147593311803 276823367944396721389967705)
  ·
    refine ⟨207617525958297541042475779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276823367944396721389967705 207617525958297541042475779)
    ·
      refine ⟨311426288937446311563713669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207617525958297541042475779 311426288937446311563713669)
      ·
        refine ⟨58392429175771183418196313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311426288937446311563713669 58392429175771183418196313)
        ·
          refine ⟨43794321881828387563647235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58392429175771183418196313 43794321881828387563647235)
          ·
            refine ⟨65691482822742581345470853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43794321881828387563647235 65691482822742581345470853)
            ·
              refine ⟨12317153029264234002275785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65691482822742581345470853 12317153029264234002275785)
              ·
                refine ⟨9237864771948175501706839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12317153029264234002275785 9237864771948175501706839)
                ·
                  refine ⟨13856797157922263252560259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9237864771948175501706839 13856797157922263252560259)
                  ·
                    refine ⟨20785195736883394878840389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13856797157922263252560259 20785195736883394878840389)
                    ·
                      refine ⟨3897224200665636539782573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20785195736883394878840389 3897224200665636539782573)
                      ·
                        rfl

theorem cell23_7589817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_7589817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589817 prefixEnd_7589817 := by exact prefixLift 7589817
  have htrace : WordTrace (prefixWord ++ tailWord_7589817) baseStart_7589817 baseEnd_7589817 := by
    simpa [prefixWord, tailWord_7589817, baseEnd_7589817] using wordTrace_append hprefix tailTrace_7589817
  have hstable : (prefixWord ++ tailWord_7589817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589817).length < 2 ^ (prefixWord ++ tailWord_7589817).sum := by decide
  have hdescent : baseEnd_7589817 < baseStart_7589817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589823 : List Nat := [1, 1, 2, 2, 2, 1, 5, 9]
def baseStart_7589823 : Nat := 118140960795 + 7589823 * 2 ^ 59
def prefixEnd_7589823 : Nat := 4983230072969 + 3 ^ 40 * 7589823 * 2
def baseEnd_7589823 : Nat := 144341751168502352455835

theorem tailTrace_7589823 : CollatzResearch.WordTrace tailWord_7589823 prefixEnd_7589823 144341751168502352455835 := by
  unfold tailWord_7589823
  simp only [CollatzResearch.WordTrace]
  refine ⟨276823586782374984414686123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184549057854916656276457415 276823586782374984414686123)
  ·
    refine ⟨415235380173562476622029185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276823586782374984414686123 415235380173562476622029185)
    ·
      refine ⟨311426535130171857466521889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415235380173562476622029185 311426535130171857466521889)
      ·
        refine ⟨233569901347628893099891417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311426535130171857466521889 233569901347628893099891417)
        ·
          refine ⟨175177426010721669824918563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233569901347628893099891417 175177426010721669824918563)
          ·
            refine ⟨262766139016082504737377845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175177426010721669824918563 262766139016082504737377845)
            ·
              refine ⟨24634325532757734819129173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262766139016082504737377845 24634325532757734819129173)
              ·
                refine ⟨144341751168502352455835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24634325532757734819129173 144341751168502352455835)
                ·
                  rfl

theorem cell23_7589823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 9].length) (baseStart_7589823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589823 prefixEnd_7589823 := by exact prefixLift 7589823
  have htrace : WordTrace (prefixWord ++ tailWord_7589823) baseStart_7589823 baseEnd_7589823 := by
    simpa [prefixWord, tailWord_7589823, baseEnd_7589823] using wordTrace_append hprefix tailTrace_7589823
  have hstable : (prefixWord ++ tailWord_7589823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589823).length < 2 ^ (prefixWord ++ tailWord_7589823).sum := by decide
  have hdescent : baseEnd_7589823 < baseStart_7589823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589900 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_7589900 : Nat := 118140960795 + 7589900 * 2 ^ 59
def prefixEnd_7589900 : Nat := 4983230072969 + 3 ^ 40 * 7589900 * 2
def baseEnd_7589900 : Nat := 1299088939853319905014897

theorem tailTrace_7589900 : CollatzResearch.WordTrace tailWord_7589900 prefixEnd_7589900 1299088939853319905014897 := by
  unfold tailWord_7589900
  simp only [CollatzResearch.WordTrace]
  refine ⟨138413197601548013282619577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184550930135397351043492769 138413197601548013282619577)
  ·
    refine ⟨103809898201161009961964683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138413197601548013282619577 103809898201161009961964683)
    ·
      refine ⟨155714847301741514942947025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103809898201161009961964683 155714847301741514942947025)
      ·
        refine ⟨116786135476306136207210269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155714847301741514942947025 116786135476306136207210269)
        ·
          refine ⟨43794800803614801077703851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116786135476306136207210269 43794800803614801077703851)
          ·
            refine ⟨65692201205422201616555777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43794800803614801077703851 65692201205422201616555777)
            ·
              refine ⟨49269150904066651212416833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65692201205422201616555777 49269150904066651212416833)
              ·
                refine ⟨36951863178049988409312625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49269150904066651212416833 36951863178049988409312625)
                ·
                  refine ⟨27713897383537491306984469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36951863178049988409312625 27713897383537491306984469)
                  ·
                    refine ⟨1299088939853319905014897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27713897383537491306984469 1299088939853319905014897)
                    ·
                      rfl

theorem cell23_7589900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_7589900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589900 prefixEnd_7589900 := by exact prefixLift 7589900
  have htrace : WordTrace (prefixWord ++ tailWord_7589900) baseStart_7589900 baseEnd_7589900 := by
    simpa [prefixWord, tailWord_7589900, baseEnd_7589900] using wordTrace_append hprefix tailTrace_7589900
  have hstable : (prefixWord ++ tailWord_7589900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589900).length < 2 ^ (prefixWord ++ tailWord_7589900).sum := by decide
  have hdescent : baseEnd_7589900 < baseStart_7589900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589917 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_7589917 : Nat := 118140960795 + 7589917 * 2 ^ 59
def prefixEnd_7589917 : Nat := 4983230072969 + 3 ^ 40 * 7589917 * 2
def baseEnd_7589917 : Nat := 1299091849577028716177371

theorem tailTrace_7589917 : CollatzResearch.WordTrace tailWord_7589917 prefixEnd_7589917 1299091849577028716177371 := by
  unfold tailWord_7589917
  simp only [CollatzResearch.WordTrace]
  refine ⟨276827015244034438468608005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184551343496022958979072003 276827015244034438468608005)
  ·
    refine ⟨51905065358256457212864001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276827015244034438468608005 51905065358256457212864001)
    ·
      refine ⟨38928799018692342909648001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51905065358256457212864001 38928799018692342909648001)
      ·
        refine ⟨29196599264019257182236001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38928799018692342909648001 29196599264019257182236001)
        ·
          refine ⟨21897449448014442886677001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29196599264019257182236001 21897449448014442886677001)
          ·
            refine ⟨16423087086010832165007751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21897449448014442886677001 16423087086010832165007751)
            ·
              refine ⟨24634630629016248247511627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16423087086010832165007751 24634630629016248247511627)
              ·
                refine ⟨36951945943524372371267441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24634630629016248247511627 36951945943524372371267441)
                ·
                  refine ⟨27713959457643279278450581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36951945943524372371267441 27713959457643279278450581)
                  ·
                    refine ⟨1299091849577028716177371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27713959457643279278450581 1299091849577028716177371)
                    ·
                      rfl

theorem cell23_7589917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_7589917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589917 prefixEnd_7589917 := by exact prefixLift 7589917
  have htrace : WordTrace (prefixWord ++ tailWord_7589917) baseStart_7589917 baseEnd_7589917 := by
    simpa [prefixWord, tailWord_7589917, baseEnd_7589917] using wordTrace_append hprefix tailTrace_7589917
  have hstable : (prefixWord ++ tailWord_7589917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589917).length < 2 ^ (prefixWord ++ tailWord_7589917).sum := by decide
  have hdescent : baseEnd_7589917 < baseStart_7589917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589945 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 1, 3, 2]
def baseStart_7589945 : Nat := 118140960795 + 7589945 * 2 ^ 59
def prefixEnd_7589945 : Nat := 4983230072969 + 3 ^ 40 * 7589945 * 2
def baseEnd_7589945 : Nat := 3897289926189412038981985

theorem tailTrace_7589945 : CollatzResearch.WordTrace tailWord_7589945 prefixEnd_7589945 3897289926189412038981985 := by
  unfold tailWord_7589945
  simp only [CollatzResearch.WordTrace]
  refine ⟨276828036487932999250627289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184552024325288666167084859 276828036487932999250627289)
  ·
    refine ⟨207621027365949749437970467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276828036487932999250627289 207621027365949749437970467)
    ·
      refine ⟨311431541048924624156955701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207621027365949749437970467 311431541048924624156955701)
      ·
        refine ⟨29196706973336683514714597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311431541048924624156955701 29196706973336683514714597)
        ·
          refine ⟨5474382557500628159008987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29196706973336683514714597 5474382557500628159008987)
          ·
            refine ⟨8211573836250942238513481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474382557500628159008987 8211573836250942238513481)
            ·
              refine ⟨6158680377188206678885111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8211573836250942238513481 6158680377188206678885111)
              ·
                refine ⟨9238020565782310018327667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6158680377188206678885111 9238020565782310018327667)
                ·
                  refine ⟨13857030848673465027491501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9238020565782310018327667 13857030848673465027491501)
                  ·
                    refine ⟨5196386568252549385309313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13857030848673465027491501 5196386568252549385309313)
                    ·
                      refine ⟨3897289926189412038981985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196386568252549385309313 3897289926189412038981985)
                      ·
                        rfl

theorem cell23_7589945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_7589945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589945 prefixEnd_7589945 := by exact prefixLift 7589945
  have htrace : WordTrace (prefixWord ++ tailWord_7589945) baseStart_7589945 baseEnd_7589945 := by
    simpa [prefixWord, tailWord_7589945, baseEnd_7589945] using wordTrace_append hprefix tailTrace_7589945
  have hstable : (prefixWord ++ tailWord_7589945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589945).length < 2 ^ (prefixWord ++ tailWord_7589945).sum := by decide
  have hdescent : baseEnd_7589945 < baseStart_7589945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589958 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_7589958 : Nat := 118140960795 + 7589958 * 2 ^ 59
def prefixEnd_7589958 : Nat := 4983230072969 + 3 ^ 40 * 7589958 * 2
def baseEnd_7589958 : Nat := 3897296601437920488119425

theorem tailTrace_7589958 : CollatzResearch.WordTrace tailWord_7589958 prefixEnd_7589958 3897296601437920488119425 := by
  unfold tailWord_7589958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650890957402684452214079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184552340424590601647233685 8650890957402684452214079)
  ·
    refine ⟨12976336436104026678321119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8650890957402684452214079 12976336436104026678321119)
    ·
      refine ⟨19464504654156040017481679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12976336436104026678321119 19464504654156040017481679)
      ·
        refine ⟨29196756981234060026222519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19464504654156040017481679 29196756981234060026222519)
        ·
          refine ⟨43795135471851090039333779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29196756981234060026222519 43795135471851090039333779)
          ·
            refine ⟨65692703207776635059000669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43795135471851090039333779 65692703207776635059000669)
            ·
              refine ⟨24634763702916238147125251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65692703207776635059000669 24634763702916238147125251)
              ·
                refine ⟨36952145554374357220687877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24634763702916238147125251 36952145554374357220687877)
                ·
                  refine ⟨6928527291445191978878977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36952145554374357220687877 6928527291445191978878977)
                  ·
                    refine ⟨5196395468583893984159233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6928527291445191978878977 5196395468583893984159233)
                    ·
                      refine ⟨3897296601437920488119425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196395468583893984159233 3897296601437920488119425)
                      ·
                        rfl

theorem cell23_7589958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_7589958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589958 prefixEnd_7589958 := by exact prefixLift 7589958
  have htrace : WordTrace (prefixWord ++ tailWord_7589958) baseStart_7589958 baseEnd_7589958 := by
    simpa [prefixWord, tailWord_7589958, baseEnd_7589958] using wordTrace_append hprefix tailTrace_7589958
  have hstable : (prefixWord ++ tailWord_7589958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589958).length < 2 ^ (prefixWord ++ tailWord_7589958).sum := by decide
  have hdescent : baseEnd_7589958 < baseStart_7589958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7589997 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_7589997 : Nat := 118140960795 + 7589997 * 2 ^ 59
def prefixEnd_7589997 : Nat := 4983230072969 + 3 ^ 40 * 7589997 * 2
def baseEnd_7589997 : Nat := 3897316627183445835531745

theorem tailTrace_7589997 : CollatzResearch.WordTrace tailWord_7589997 prefixEnd_7589997 3897316627183445835531745 := by
  unfold tailWord_7589997
  simp only [CollatzResearch.WordTrace]
  refine ⟨276829933083744612131520245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184553288722496408087680163 276829933083744612131520245)
  ·
    refine ⟨25952806226601057387330023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276829933083744612131520245 25952806226601057387330023)
    ·
      refine ⟨38929209339901586080995035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25952806226601057387330023 38929209339901586080995035)
      ·
        refine ⟨58393814009852379121492553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38929209339901586080995035 58393814009852379121492553)
        ·
          refine ⟨43795360507389284341119415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58393814009852379121492553 43795360507389284341119415)
          ·
            refine ⟨65693040761083926511679123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43795360507389284341119415 65693040761083926511679123)
            ·
              refine ⟨98539561141625889767518685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65693040761083926511679123 98539561141625889767518685)
              ·
                refine ⟨36952335428109708662819507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98539561141625889767518685 36952335428109708662819507)
                ·
                  refine ⟨55428503142164562994229261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36952335428109708662819507 55428503142164562994229261)
                  ·
                    refine ⟨20785688678311711122835973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55428503142164562994229261 20785688678311711122835973)
                    ·
                      refine ⟨3897316627183445835531745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20785688678311711122835973 3897316627183445835531745)
                      ·
                        rfl

theorem cell23_7589997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_7589997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7589997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7589997 prefixEnd_7589997 := by exact prefixLift 7589997
  have htrace : WordTrace (prefixWord ++ tailWord_7589997) baseStart_7589997 baseEnd_7589997 := by
    simpa [prefixWord, tailWord_7589997, baseEnd_7589997] using wordTrace_append hprefix tailTrace_7589997
  have hstable : (prefixWord ++ tailWord_7589997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7589997).length < 2 ^ (prefixWord ++ tailWord_7589997).sum := by decide
  have hdescent : baseEnd_7589997 < baseStart_7589997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7589997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590034 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_7590034 : Nat := 118140960795 + 7590034 * 2 ^ 59
def prefixEnd_7590034 : Nat := 4983230072969 + 3 ^ 40 * 7590034 * 2
def baseEnd_7590034 : Nat := 3897335625967662190769075

theorem tailTrace_7590034 : CollatzResearch.WordTrace tailWord_7590034 prefixEnd_7590034 3897335625967662190769075 := by
  unfold tailWord_7590034
  simp only [CollatzResearch.WordTrace]
  refine ⟨69207820646152641862654289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184554188389740378300411437 69207820646152641862654289)
  ·
    refine ⟨51905865484614481396990717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69207820646152641862654289 51905865484614481396990717)
    ·
      refine ⟨19464699556730430523871519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51905865484614481396990717 19464699556730430523871519)
      ·
        refine ⟨29197049335095645785807279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19464699556730430523871519 29197049335095645785807279)
        ·
          refine ⟨43795574002643468678710919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29197049335095645785807279 43795574002643468678710919)
          ·
            refine ⟨65693361003965203018066379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43795574002643468678710919 65693361003965203018066379)
            ·
              refine ⟨98540041505947804527099569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65693361003965203018066379 98540041505947804527099569)
              ·
                refine ⟨73905031129460853395324677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98540041505947804527099569 73905031129460853395324677)
                ·
                  refine ⟨13857193336773910011623377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73905031129460853395324677 13857193336773910011623377)
                  ·
                    refine ⟨10392895002580432508717533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13857193336773910011623377 10392895002580432508717533)
                    ·
                      refine ⟨3897335625967662190769075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10392895002580432508717533 3897335625967662190769075)
                      ·
                        rfl

theorem cell23_7590034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_7590034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590034 prefixEnd_7590034 := by exact prefixLift 7590034
  have htrace : WordTrace (prefixWord ++ tailWord_7590034) baseStart_7590034 baseEnd_7590034 := by
    simpa [prefixWord, tailWord_7590034, baseEnd_7590034] using wordTrace_append hprefix tailTrace_7590034
  have hstable : (prefixWord ++ tailWord_7590034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590034).length < 2 ^ (prefixWord ++ tailWord_7590034).sum := by decide
  have hdescent : baseEnd_7590034 < baseStart_7590034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590037 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 6]
def baseStart_7590037 : Nat := 118140960795 + 7590037 * 2 ^ 59
def prefixEnd_7590037 : Nat := 4983230072969 + 3 ^ 40 * 7590037 * 2
def baseEnd_7590037 : Nat := 433037462934402853225729

theorem tailTrace_7590037 : CollatzResearch.WordTrace tailWord_7590037 prefixEnd_7590037 433037462934402853225729 := by
  unfold tailWord_7590037
  simp only [CollatzResearch.WordTrace]
  refine ⟨276831392003599698962976365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184554261335733132641984243 276831392003599698962976365)
  ·
    refine ⟨103811772001349887111116137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276831392003599698962976365 103811772001349887111116137)
    ·
      refine ⟨77858829001012415333337103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103811772001349887111116137 77858829001012415333337103)
      ·
        refine ⟨116788243501518623000005655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77858829001012415333337103 116788243501518623000005655)
        ·
          refine ⟨175182365252277934500008483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116788243501518623000005655 175182365252277934500008483)
          ·
            refine ⟨262773547878416901750012725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175182365252277934500008483 262773547878416901750012725)
            ·
              refine ⟨24635020113601584539063693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262773547878416901750012725 24635020113601584539063693)
              ·
                refine ⟨9238132542600594202148885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24635020113601584539063693 9238132542600594202148885)
                ·
                  refine ⟨433037462934402853225729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9238132542600594202148885 433037462934402853225729)
                  ·
                    rfl

theorem cell23_7590037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_7590037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590037 prefixEnd_7590037 := by exact prefixLift 7590037
  have htrace : WordTrace (prefixWord ++ tailWord_7590037) baseStart_7590037 baseEnd_7590037 := by
    simpa [prefixWord, tailWord_7590037, baseEnd_7590037] using wordTrace_append hprefix tailTrace_7590037
  have hstable : (prefixWord ++ tailWord_7590037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590037).length < 2 ^ (prefixWord ++ tailWord_7590037).sum := by decide
  have hdescent : baseEnd_7590037 < baseStart_7590037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590084 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_7590084 : Nat := 118140960795 + 7590084 * 2 ^ 59
def prefixEnd_7590084 : Nat := 4983230072969 + 3 ^ 40 * 7590084 * 2
def baseEnd_7590084 : Nat := 1299120433333462331714615

theorem tailTrace_7590084 : CollatzResearch.WordTrace tailWord_7590084 prefixEnd_7590084 1299120433333462331714615 := by
  unfold tailWord_7590084
  simp only [CollatzResearch.WordTrace]
  refine ⟨138416553117214712994968653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184555404156286283993291537 138416553117214712994968653)
  ·
    refine ⟨51906207418955517373113245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138416553117214712994968653 51906207418955517373113245)
    ·
      refine ⟨19464827782108319014917467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51906207418955517373113245 19464827782108319014917467)
      ·
        refine ⟨29197241673162478522376201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19464827782108319014917467 29197241673162478522376201)
        ·
          refine ⟨21897931254871858891782151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29197241673162478522376201 21897931254871858891782151)
          ·
            refine ⟨32846896882307788337673227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21897931254871858891782151 32846896882307788337673227)
            ·
              refine ⟨49270345323461682506509841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32846896882307788337673227 49270345323461682506509841)
              ·
                refine ⟨36952758992596261879882381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49270345323461682506509841 36952758992596261879882381)
                ·
                  refine ⟨13857284622223598204955893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36952758992596261879882381 13857284622223598204955893)
                  ·
                    refine ⟨1299120433333462331714615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13857284622223598204955893 1299120433333462331714615)
                    ·
                      rfl

theorem cell23_7590084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_7590084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590084 prefixEnd_7590084 := by exact prefixLift 7590084
  have htrace : WordTrace (prefixWord ++ tailWord_7590084) baseStart_7590084 baseEnd_7590084 := by
    simpa [prefixWord, tailWord_7590084, baseEnd_7590084] using wordTrace_append hprefix tailTrace_7590084
  have hstable : (prefixWord ++ tailWord_7590084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590084).length < 2 ^ (prefixWord ++ tailWord_7590084).sum := by decide
  have hdescent : baseEnd_7590084 < baseStart_7590084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590097 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 1, 6]
def baseStart_7590097 : Nat := 118140960795 + 7590097 * 2 ^ 59
def prefixEnd_7590097 : Nat := 4983230072969 + 3 ^ 40 * 7590097 * 2
def baseEnd_7590097 : Nat := 1299122658416298481427095

theorem tailTrace_7590097 : CollatzResearch.WordTrace tailWord_7590097 prefixEnd_7590097 1299122658416298481427095 := by
  unfold tailWord_7590097
  simp only [CollatzResearch.WordTrace]
  refine ⟨276833580383382329210160545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184555720255588219473440363 276833580383382329210160545)
  ·
    refine ⟨207625185287536746907620409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276833580383382329210160545 207625185287536746907620409)
    ·
      refine ⟨155718888965652560180715307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207625185287536746907620409 155718888965652560180715307)
      ·
        refine ⟨233578333448478840271072961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155718888965652560180715307 233578333448478840271072961)
        ·
          refine ⟨175183750086359130203304721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233578333448478840271072961 175183750086359130203304721)
          ·
            refine ⟨131387812564769347652478541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175183750086359130203304721 131387812564769347652478541)
            ·
              refine ⟨49270429711788505369679453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131387812564769347652478541 49270429711788505369679453)
              ·
                refine ⟨18476411141920689513629795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49270429711788505369679453 18476411141920689513629795)
                ·
                  refine ⟨27714616712881034270444693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18476411141920689513629795 27714616712881034270444693)
                  ·
                    refine ⟨1299122658416298481427095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27714616712881034270444693 1299122658416298481427095)
                    ·
                      rfl

theorem cell23_7590097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_7590097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590097 prefixEnd_7590097 := by exact prefixLift 7590097
  have htrace : WordTrace (prefixWord ++ tailWord_7590097) baseStart_7590097 baseEnd_7590097 := by
    simpa [prefixWord, tailWord_7590097, baseEnd_7590097] using wordTrace_append hprefix tailTrace_7590097
  have hstable : (prefixWord ++ tailWord_7590097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590097).length < 2 ^ (prefixWord ++ tailWord_7590097).sum := by decide
  have hdescent : baseEnd_7590097 < baseStart_7590097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590104 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_7590104 : Nat := 118140960795 + 7590104 * 2 ^ 59
def prefixEnd_7590104 : Nat := 4983230072969 + 3 ^ 40 * 7590104 * 2
def baseEnd_7590104 : Nat := 3897371569613476916893753

theorem tailTrace_7590104 : CollatzResearch.WordTrace tailWord_7590104 prefixEnd_7590104 3897371569613476916893753 := by
  unfold tailWord_7590104
  simp only [CollatzResearch.WordTrace]
  refine ⟨138416917847178484702832683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184555890462904646270443577 138416917847178484702832683)
  ·
    refine ⟨207625376770767727054249025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138416917847178484702832683 207625376770767727054249025)
    ·
      refine ⟨155719032578075795290686769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207625376770767727054249025 155719032578075795290686769)
      ·
        refine ⟨116789274433556846468015077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155719032578075795290686769 116789274433556846468015077)
        ·
          refine ⟨21897988956291908712752827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116789274433556846468015077 21897988956291908712752827)
          ·
            refine ⟨32846983434437863069129241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21897988956291908712752827 32846983434437863069129241)
            ·
              refine ⟨24635237575828397301846931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32846983434437863069129241 24635237575828397301846931)
              ·
                refine ⟨36952856363742595952770397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24635237575828397301846931 36952856363742595952770397)
                ·
                  refine ⟨13857321136403473482288899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36952856363742595952770397 13857321136403473482288899)
                  ·
                    refine ⟨20785981704605210223433349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13857321136403473482288899 20785981704605210223433349)
                    ·
                      refine ⟨3897371569613476916893753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20785981704605210223433349 3897371569613476916893753)
                      ·
                        rfl

theorem cell23_7590104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_7590104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590104 prefixEnd_7590104 := by exact prefixLift 7590104
  have htrace : WordTrace (prefixWord ++ tailWord_7590104) baseStart_7590104 baseEnd_7590104 := by
    simpa [prefixWord, tailWord_7590104, baseEnd_7590104] using wordTrace_append hprefix tailTrace_7590104
  have hstable : (prefixWord ++ tailWord_7590104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590104).length < 2 ^ (prefixWord ++ tailWord_7590104).sum := by decide
  have hdescent : baseEnd_7590104 < baseStart_7590104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590127 : List Nat := [1, 1, 2, 1, 6, 2, 10]
def baseStart_7590127 : Nat := 118140960795 + 7590127 * 2 ^ 59
def prefixEnd_7590127 : Nat := 4983230072969 + 3 ^ 40 * 7590127 * 2
def baseEnd_7590127 : Nat := 48115844193438646011187

theorem tailTrace_7590127 : CollatzResearch.WordTrace tailWord_7590127 prefixEnd_7590127 48115844193438646011187 := by
  unfold tailWord_7590127
  simp only [CollatzResearch.WordTrace]
  refine ⟨276834674573273644333752635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184556449715515762889168423 276834674573273644333752635)
  ·
    refine ⟨415252011859910466500628953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276834674573273644333752635 415252011859910466500628953)
    ·
      refine ⟨311439008894932849875471715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415252011859910466500628953 311439008894932849875471715)
      ·
        refine ⟨467158513342399274813207573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311439008894932849875471715 467158513342399274813207573)
        ·
          refine ⟨21898055312924966006869105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 467158513342399274813207573 21898055312924966006869105)
          ·
            refine ⟨16423541484693724505151829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21898055312924966006869105 16423541484693724505151829)
            ·
              refine ⟨48115844193438646011187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16423541484693724505151829 48115844193438646011187)
              ·
                rfl

theorem cell23_7590127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 10].length) (baseStart_7590127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590127 prefixEnd_7590127 := by exact prefixLift 7590127
  have htrace : WordTrace (prefixWord ++ tailWord_7590127) baseStart_7590127 baseEnd_7590127 := by
    simpa [prefixWord, tailWord_7590127, baseEnd_7590127] using wordTrace_append hprefix tailTrace_7590127
  have hstable : (prefixWord ++ tailWord_7590127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590127).length < 2 ^ (prefixWord ++ tailWord_7590127).sum := by decide
  have hdescent : baseEnd_7590127 < baseStart_7590127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590134 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_7590134 : Nat := 118140960795 + 7590134 * 2 ^ 59
def prefixEnd_7590134 : Nat := 4983230072969 + 3 ^ 40 * 7590134 * 2
def baseEnd_7590134 : Nat := 3897386974033111799518615

theorem tailTrace_7590134 : CollatzResearch.WordTrace tailWord_7590134 prefixEnd_7590134 3897386974033111799518615 := by
  unfold tailWord_7590134
  simp only [CollatzResearch.WordTrace]
  refine ⟨17302183117765517783078591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184556619922832189686171637 17302183117765517783078591)
  ·
    refine ⟨25953274676648276674617887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17302183117765517783078591 25953274676648276674617887)
    ·
      refine ⟨38929912014972415011926831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25953274676648276674617887 38929912014972415011926831)
      ·
        refine ⟨58394868022458622517890247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38929912014972415011926831 58394868022458622517890247)
        ·
          refine ⟨87592302033687933776835371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58394868022458622517890247 87592302033687933776835371)
          ·
            refine ⟨131388453050531900665253057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87592302033687933776835371 131388453050531900665253057)
            ·
              refine ⟨98541339787898925498939793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131388453050531900665253057 98541339787898925498939793)
              ·
                refine ⟨73906004840924194124204845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98541339787898925498939793 73906004840924194124204845)
                ·
                  refine ⟨27714751815346572796576817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73906004840924194124204845 27714751815346572796576817)
                  ·
                    refine ⟨20786063861509929597432613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27714751815346572796576817 20786063861509929597432613)
                    ·
                      refine ⟨3897386974033111799518615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20786063861509929597432613 3897386974033111799518615)
                      ·
                        rfl

theorem cell23_7590134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_7590134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590134 prefixEnd_7590134 := by exact prefixLift 7590134
  have htrace : WordTrace (prefixWord ++ tailWord_7590134) baseStart_7590134 baseEnd_7590134 := by
    simpa [prefixWord, tailWord_7590134, baseEnd_7590134] using wordTrace_append hprefix tailTrace_7590134
  have hstable : (prefixWord ++ tailWord_7590134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590134).length < 2 ^ (prefixWord ++ tailWord_7590134).sum := by decide
  have hdescent : baseEnd_7590134 < baseStart_7590134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590138 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2]
def baseStart_7590138 : Nat := 118140960795 + 7590138 * 2 ^ 59
def prefixEnd_7590138 : Nat := 4983230072969 + 3 ^ 40 * 7590138 * 2
def baseEnd_7590138 : Nat := 3897389027955729783868597

theorem tailTrace_7590138 : CollatzResearch.WordTrace tailWord_7590138 prefixEnd_7590138 3897389027955729783868597 := by
  unfold tailWord_7590138
  simp only [CollatzResearch.WordTrace]
  refine ⟨69208768944058448303100767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184556717184155862141602045 69208768944058448303100767)
  ·
    refine ⟨103813153416087672454651151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69208768944058448303100767 103813153416087672454651151)
    ·
      refine ⟨155719730124131508681976727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103813153416087672454651151 155719730124131508681976727)
      ·
        refine ⟨233579595186197263022965091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155719730124131508681976727 233579595186197263022965091)
        ·
          refine ⟨350369392779295894534447637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233579595186197263022965091 350369392779295894534447637)
          ·
            refine ⟨16423565286529495056302233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 350369392779295894534447637 16423565286529495056302233)
            ·
              refine ⟨12317673964897121292226675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16423565286529495056302233 12317673964897121292226675)
              ·
                refine ⟨18476510947345681938340013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12317673964897121292226675 18476510947345681938340013)
                ·
                  refine ⟨6928691605254630726877505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18476510947345681938340013 6928691605254630726877505)
                  ·
                    refine ⟨5196518703940973045158129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6928691605254630726877505 5196518703940973045158129)
                    ·
                      refine ⟨3897389027955729783868597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196518703940973045158129 3897389027955729783868597)
                      ·
                        rfl

theorem cell23_7590138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2].length) (baseStart_7590138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590138 prefixEnd_7590138 := by exact prefixLift 7590138
  have htrace : WordTrace (prefixWord ++ tailWord_7590138) baseStart_7590138 baseEnd_7590138 := by
    simpa [prefixWord, tailWord_7590138, baseEnd_7590138] using wordTrace_append hprefix tailTrace_7590138
  have hstable : (prefixWord ++ tailWord_7590138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590138).length < 2 ^ (prefixWord ++ tailWord_7590138).sum := by decide
  have hdescent : baseEnd_7590138 < baseStart_7590138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590148 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_7590148 : Nat := 118140960795 + 7590148 * 2 ^ 59
def prefixEnd_7590148 : Nat := 4983230072969 + 3 ^ 40 * 7590148 * 2
def baseEnd_7590148 : Nat := 1299131387587424914914517

theorem tailTrace_7590148 : CollatzResearch.WordTrace tailWord_7590148 prefixEnd_7590148 1299131387587424914914517 := by
  unfold tailWord_7590148
  simp only [CollatzResearch.WordTrace]
  refine ⟨138417720253098782460133549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184556960337465043280178065 138417720253098782460133549)
  ·
    refine ⟨51906645094912043422550081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138417720253098782460133549 51906645094912043422550081)
    ·
      refine ⟨38929983821184032566912561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51906645094912043422550081 38929983821184032566912561)
      ·
        refine ⟨29197487865888024425184421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38929983821184032566912561 29197487865888024425184421)
        ·
          refine ⟨5474528974854004579722079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29197487865888024425184421 5474528974854004579722079)
          ·
            refine ⟨8211793462281006869583119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474528974854004579722079 8211793462281006869583119)
            ·
              refine ⟨12317690193421510304374679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211793462281006869583119 12317690193421510304374679)
              ·
                refine ⟨18476535290132265456562019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12317690193421510304374679 18476535290132265456562019)
                ·
                  refine ⟨27714802935198398184843029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18476535290132265456562019 27714802935198398184843029)
                  ·
                    refine ⟨1299131387587424914914517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27714802935198398184843029 1299131387587424914914517)
                    ·
                      rfl

theorem cell23_7590148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_7590148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590148 prefixEnd_7590148 := by exact prefixLift 7590148
  have htrace : WordTrace (prefixWord ++ tailWord_7590148) baseStart_7590148 baseEnd_7590148 := by
    simpa [prefixWord, tailWord_7590148, baseEnd_7590148] using wordTrace_append hprefix tailTrace_7590148
  have hstable : (prefixWord ++ tailWord_7590148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590148).length < 2 ^ (prefixWord ++ tailWord_7590148).sum := by decide
  have hdescent : baseEnd_7590148 < baseStart_7590148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590151 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7590151 : Nat := 118140960795 + 7590151 * 2 ^ 59
def prefixEnd_7590151 : Nat := 4983230072969 + 3 ^ 40 * 7590151 * 2
def baseEnd_7590151 : Nat := 3897395703204238233006037

theorem tailTrace_7590151 : CollatzResearch.WordTrace tailWord_7590151 prefixEnd_7590151 3897395703204238233006037 := by
  unfold tailWord_7590151
  simp only [CollatzResearch.WordTrace]
  refine ⟨276835549925186696432626307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184557033283457797621750871 276835549925186696432626307)
  ·
    refine ⟨415253324887780044648939461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276835549925186696432626307 415253324887780044648939461)
    ·
      refine ⟨77859998416458758371676149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415253324887780044648939461 77859998416458758371676149)
      ·
        refine ⟨7299374851543008597344639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77859998416458758371676149 7299374851543008597344639)
        ·
          refine ⟨10949062277314512896016959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7299374851543008597344639 10949062277314512896016959)
          ·
            refine ⟨16423593415971769344025439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10949062277314512896016959 16423593415971769344025439)
            ·
              refine ⟨24635390123957654016038159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16423593415971769344025439 24635390123957654016038159)
              ·
                refine ⟨36953085185936481024057239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24635390123957654016038159 36953085185936481024057239)
                ·
                  refine ⟨55429627778904721536085859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36953085185936481024057239 55429627778904721536085859)
                  ·
                    refine ⟨83144441668357082304128789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55429627778904721536085859 83144441668357082304128789)
                    ·
                      refine ⟨3897395703204238233006037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83144441668357082304128789 3897395703204238233006037)
                      ·
                        rfl

theorem cell23_7590151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7590151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590151 prefixEnd_7590151 := by exact prefixLift 7590151
  have htrace : WordTrace (prefixWord ++ tailWord_7590151) baseStart_7590151 baseEnd_7590151 := by
    simpa [prefixWord, tailWord_7590151, baseEnd_7590151] using wordTrace_append hprefix tailTrace_7590151
  have hstable : (prefixWord ++ tailWord_7590151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590151).length < 2 ^ (prefixWord ++ tailWord_7590151).sum := by decide
  have hdescent : baseEnd_7590151 < baseStart_7590151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590189 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_7590189 : Nat := 118140960795 + 7590189 * 2 ^ 59
def prefixEnd_7590189 : Nat := 4983230072969 + 3 ^ 40 * 7590189 * 2
def baseEnd_7590189 : Nat := 3897415215469109084330863

theorem tailTrace_7590189 : CollatzResearch.WordTrace tailWord_7590189 prefixEnd_7590189 3897415215469109084330863 := by
  unfold tailWord_7590189
  simp only [CollatzResearch.WordTrace]
  refine ⟨276836935899049028922509621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184557957266032685948339747 276836935899049028922509621)
  ·
    refine ⟨25953462740535846461485277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276836935899049028922509621 25953462740535846461485277)
    ·
      refine ⟨9732548527700942423056979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25953462740535846461485277 9732548527700942423056979)
      ·
        refine ⟨14598822791551413634585469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9732548527700942423056979 14598822791551413634585469)
        ·
          refine ⟨5474558546831780112969551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14598822791551413634585469 5474558546831780112969551)
          ·
            refine ⟨8211837820247670169454327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474558546831780112969551 8211837820247670169454327)
            ·
              refine ⟨12317756730371505254181491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211837820247670169454327 12317756730371505254181491)
              ·
                refine ⟨18476635095557257881272237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12317756730371505254181491 18476635095557257881272237)
                ·
                  refine ⟨6928738160833971705477089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18476635095557257881272237 6928738160833971705477089)
                  ·
                    refine ⟨5196553620625478779107817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6928738160833971705477089 5196553620625478779107817)
                    ·
                      refine ⟨3897415215469109084330863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196553620625478779107817 3897415215469109084330863)
                      ·
                        rfl

theorem cell23_7590189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_7590189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590189 prefixEnd_7590189 := by exact prefixLift 7590189
  have htrace : WordTrace (prefixWord ++ tailWord_7590189) baseStart_7590189 baseEnd_7590189 := by
    simpa [prefixWord, tailWord_7590189, baseEnd_7590189] using wordTrace_append hprefix tailTrace_7590189
  have hstable : (prefixWord ++ tailWord_7590189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590189).length < 2 ^ (prefixWord ++ tailWord_7590189).sum := by decide
  have hdescent : baseEnd_7590189 < baseStart_7590189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590217 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 9]
def baseStart_7590217 : Nat := 118140960795 + 7590217 * 2 ^ 59
def prefixEnd_7590217 : Nat := 4983230072969 + 3 ^ 40 * 7590217 * 2
def baseEnd_7590217 : Nat := 433047732547492774975637

theorem tailTrace_7590217 : CollatzResearch.WordTrace tailWord_7590217 prefixEnd_7590217 433047732547492774975637 := by
  unfold tailWord_7590217
  simp only [CollatzResearch.WordTrace]
  refine ⟨276837957142947589704528905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184558638095298393136352603 276837957142947589704528905)
  ·
    refine ⟨207628467857210692278396679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276837957142947589704528905 207628467857210692278396679)
    ·
      refine ⟨311442701785816038417595019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207628467857210692278396679 311442701785816038417595019)
      ·
        refine ⟨467164052678724057626392529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311442701785816038417595019 467164052678724057626392529)
        ·
          refine ⟨350373039509043043219794397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467164052678724057626392529 350373039509043043219794397)
          ·
            refine ⟨131389889815891141207422899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350373039509043043219794397 131389889815891141207422899)
            ·
              refine ⟨197084834723836711811134349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131389889815891141207422899 197084834723836711811134349)
              ·
                refine ⟨73906813021438766929175381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197084834723836711811134349 73906813021438766929175381)
                ·
                  refine ⟨433047732547492774975637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73906813021438766929175381 433047732547492774975637)
                  ·
                    rfl

theorem cell23_7590217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 9].length) (baseStart_7590217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590217 prefixEnd_7590217 := by exact prefixLift 7590217
  have htrace : WordTrace (prefixWord ++ tailWord_7590217) baseStart_7590217 baseEnd_7590217 := by
    simpa [prefixWord, tailWord_7590217, baseEnd_7590217] using wordTrace_append hprefix tailTrace_7590217
  have hstable : (prefixWord ++ tailWord_7590217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590217).length < 2 ^ (prefixWord ++ tailWord_7590217).sum := by decide
  have hdescent : baseEnd_7590217 < baseStart_7590217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590227 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 7]
def baseStart_7590227 : Nat := 118140960795 + 7590227 * 2 ^ 59
def prefixEnd_7590227 : Nat := 4983230072969 + 3 ^ 40 * 7590227 * 2
def baseEnd_7590227 : Nat := 3897434727733979935655687

theorem tailTrace_7590227 : CollatzResearch.WordTrace tailWord_7590227 prefixEnd_7590227 3897434727733979935655687 := by
  unfold tailWord_7590227
  simp only [CollatzResearch.WordTrace]
  refine ⟨276838321872911361412392935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184558881248607574274928623 276838321872911361412392935)
  ·
    refine ⟨415257482809367042118589403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276838321872911361412392935 415257482809367042118589403)
    ·
      refine ⟨622886224214050563177884105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415257482809367042118589403 622886224214050563177884105)
      ·
        refine ⟨467164668160537922383413079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622886224214050563177884105 467164668160537922383413079)
        ·
          refine ⟨700747002240806883575119619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467164668160537922383413079 700747002240806883575119619)
          ·
            refine ⟨1051120503361210325362679429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700747002240806883575119619 1051120503361210325362679429)
            ·
              refine ⟨197085094380226936005502393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1051120503361210325362679429 197085094380226936005502393)
              ·
                refine ⟨147813820785170202004126795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197085094380226936005502393 147813820785170202004126795)
                ·
                  refine ⟨221720731177755303006190193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147813820785170202004126795 221720731177755303006190193)
                  ·
                    refine ⟨166290548383316477254642645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221720731177755303006190193 166290548383316477254642645)
                    ·
                      refine ⟨3897434727733979935655687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166290548383316477254642645 3897434727733979935655687)
                      ·
                        rfl

theorem cell23_7590227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_7590227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590227 prefixEnd_7590227 := by exact prefixLift 7590227
  have htrace : WordTrace (prefixWord ++ tailWord_7590227) baseStart_7590227 baseEnd_7590227 := by
    simpa [prefixWord, tailWord_7590227, baseEnd_7590227] using wordTrace_append hprefix tailTrace_7590227
  have hstable : (prefixWord ++ tailWord_7590227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590227).length < 2 ^ (prefixWord ++ tailWord_7590227).sum := by decide
  have hdescent : baseEnd_7590227 < baseStart_7590227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590228 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_7590228 : Nat := 118140960795 + 7590228 * 2 ^ 59
def prefixEnd_7590228 : Nat := 4983230072969 + 3 ^ 40 * 7590228 * 2
def baseEnd_7590228 : Nat := 3897435241214634431743183

theorem tailTrace_7590228 : CollatzResearch.WordTrace tailWord_7590228 prefixEnd_7590228 3897435241214634431743183 := by
  unfold tailWord_7590228
  simp only [CollatzResearch.WordTrace]
  refine ⟨138419179172953869291589669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184558905563938492388786225 138419179172953869291589669)
  ·
    refine ⟨25953596094928850492173063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138419179172953869291589669 25953596094928850492173063)
    ·
      refine ⟨38930394142393275738259595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25953596094928850492173063 38930394142393275738259595)
      ·
        refine ⟨58395591213589913607389393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38930394142393275738259595 58395591213589913607389393)
        ·
          refine ⟨43796693410192435205542045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58395591213589913607389393 43796693410192435205542045)
          ·
            refine ⟨16423760028822163202078267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43796693410192435205542045 16423760028822163202078267)
            ·
              refine ⟨24635640043233244803117401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16423760028822163202078267 24635640043233244803117401)
              ·
                refine ⟨18476730032424933602338051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24635640043233244803117401 18476730032424933602338051)
                ·
                  refine ⟨27715095048637400403507077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18476730032424933602338051 27715095048637400403507077)
                  ·
                    refine ⟨5196580321619512575657577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27715095048637400403507077 5196580321619512575657577)
                    ·
                      refine ⟨3897435241214634431743183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196580321619512575657577 3897435241214634431743183)
                      ·
                        rfl

theorem cell23_7590228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_7590228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590228 prefixEnd_7590228 := by exact prefixLift 7590228
  have htrace : WordTrace (prefixWord ++ tailWord_7590228) baseStart_7590228 baseEnd_7590228 := by
    simpa [prefixWord, tailWord_7590228, baseEnd_7590228] using wordTrace_append hprefix tailTrace_7590228
  have hstable : (prefixWord ++ tailWord_7590228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590228).length < 2 ^ (prefixWord ++ tailWord_7590228).sum := by decide
  have hdescent : baseEnd_7590228 < baseStart_7590228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590245 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 2, 2, 2]
def baseStart_7590245 : Nat := 118140960795 + 7590245 * 2 ^ 59
def prefixEnd_7590245 : Nat := 4983230072969 + 3 ^ 40 * 7590245 * 2
def baseEnd_7590245 : Nat := 3897443970385760865230605

theorem tailTrace_7590245 : CollatzResearch.WordTrace tailWord_7590245 prefixEnd_7590245 3897443970385760865230605 := by
  unfold tailWord_7590245
  simp only [CollatzResearch.WordTrace]
  refine ⟨276838978386846150486548189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184559318924564100324365459 276838978386846150486548189)
  ·
    refine ⟨103814616895067306432455571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276838978386846150486548189 103814616895067306432455571)
    ·
      refine ⟨155721925342600959648683357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103814616895067306432455571 155721925342600959648683357)
      ·
        refine ⟨58395722003475359868256259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155721925342600959648683357 58395722003475359868256259)
        ·
          refine ⟨87593583005213039802384389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58395722003475359868256259 87593583005213039802384389)
          ·
            refine ⟨16423796813477444962947073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87593583005213039802384389 16423796813477444962947073)
            ·
              refine ⟨12317847610108083722210305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16423796813477444962947073 12317847610108083722210305)
              ·
                refine ⟨9238385707581062791657729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12317847610108083722210305 9238385707581062791657729)
                ·
                  refine ⟨6928789280685797093743297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9238385707581062791657729 6928789280685797093743297)
                  ·
                    refine ⟨5196591960514347820307473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6928789280685797093743297 5196591960514347820307473)
                    ·
                      refine ⟨3897443970385760865230605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196591960514347820307473 3897443970385760865230605)
                      ·
                        rfl

theorem cell23_7590245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_7590245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590245 prefixEnd_7590245 := by exact prefixLift 7590245
  have htrace : WordTrace (prefixWord ++ tailWord_7590245) baseStart_7590245 baseEnd_7590245 := by
    simpa [prefixWord, tailWord_7590245, baseEnd_7590245] using wordTrace_append hprefix tailTrace_7590245
  have hstable : (prefixWord ++ tailWord_7590245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590245).length < 2 ^ (prefixWord ++ tailWord_7590245).sum := by decide
  have hdescent : baseEnd_7590245 < baseStart_7590245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590261 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_7590261 : Nat := 118140960795 + 7590261 * 2 ^ 59
def prefixEnd_7590261 : Nat := 4983230072969 + 3 ^ 40 * 7590261 * 2
def baseEnd_7590261 : Nat := 3897452186076232802630531

theorem tailTrace_7590261 : CollatzResearch.WordTrace tailWord_7590261 prefixEnd_7590261 3897452186076232802630531 := by
  unfold tailWord_7590261
  simp only [CollatzResearch.WordTrace]
  refine ⟨276839561954788185219130637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184559707969858790146087091 276839561954788185219130637)
  ·
    refine ⟨103814835733045569457173989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276839561954788185219130637 103814835733045569457173989)
    ·
      refine ⟨19465281699946044273220123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103814835733045569457173989 19465281699946044273220123)
      ·
        refine ⟨29197922549919066409830185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19465281699946044273220123 29197922549919066409830185)
        ·
          refine ⟨21898441912439299807372639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29197922549919066409830185 21898441912439299807372639)
          ·
            refine ⟨32847662868658949711058959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21898441912439299807372639 32847662868658949711058959)
            ·
              refine ⟨49271494302988424566588439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32847662868658949711058959 49271494302988424566588439)
              ·
                refine ⟨73907241454482636849882659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49271494302988424566588439 73907241454482636849882659)
                ·
                  refine ⟨110860862181723955274823989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73907241454482636849882659 110860862181723955274823989)
                  ·
                    refine ⟨10393205829536620807014749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110860862181723955274823989 10393205829536620807014749)
                    ·
                      refine ⟨3897452186076232802630531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10393205829536620807014749 3897452186076232802630531)
                      ·
                        rfl

theorem cell23_7590261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_7590261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590261 prefixEnd_7590261 := by exact prefixLift 7590261
  have htrace : WordTrace (prefixWord ++ tailWord_7590261) baseStart_7590261 baseEnd_7590261 := by
    simpa [prefixWord, tailWord_7590261, baseEnd_7590261] using wordTrace_append hprefix tailTrace_7590261
  have hstable : (prefixWord ++ tailWord_7590261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590261).length < 2 ^ (prefixWord ++ tailWord_7590261).sum := by decide
  have hdescent : baseEnd_7590261 < baseStart_7590261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590262 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7590262 : Nat := 118140960795 + 7590262 * 2 ^ 59
def prefixEnd_7590262 : Nat := 4983230072969 + 3 ^ 40 * 7590262 * 2
def baseEnd_7590262 : Nat := 3897452699556887298718027

theorem tailTrace_7590262 : CollatzResearch.WordTrace tailWord_7590262 prefixEnd_7590262 3897452699556887298718027 := by
  unfold tailWord_7590262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17302474901736535149369815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184559732285189708259944693 17302474901736535149369815)
  ·
    refine ⟨25953712352604802724054723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17302474901736535149369815 25953712352604802724054723)
    ·
      refine ⟨38930568528907204086082085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25953712352604802724054723 38930568528907204086082085)
      ·
        refine ⟨7299481599170100766140391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38930568528907204086082085 7299481599170100766140391)
        ·
          refine ⟨10949222398755151149210587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7299481599170100766140391 10949222398755151149210587)
          ·
            refine ⟨16423833598132726723815881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10949222398755151149210587 16423833598132726723815881)
            ·
              refine ⟨12317875198599545042861911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16423833598132726723815881 12317875198599545042861911)
              ·
                refine ⟨18476812797899317564292867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12317875198599545042861911 18476812797899317564292867)
                ·
                  refine ⟨27715219196848976346439301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18476812797899317564292867 27715219196848976346439301)
                  ·
                    refine ⟨5196603599409183064957369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27715219196848976346439301 5196603599409183064957369)
                    ·
                      refine ⟨3897452699556887298718027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196603599409183064957369 3897452699556887298718027)
                      ·
                        rfl

theorem cell23_7590262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7590262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590262 prefixEnd_7590262 := by exact prefixLift 7590262
  have htrace : WordTrace (prefixWord ++ tailWord_7590262) baseStart_7590262 baseEnd_7590262 := by
    simpa [prefixWord, tailWord_7590262, baseEnd_7590262] using wordTrace_append hprefix tailTrace_7590262
  have hstable : (prefixWord ++ tailWord_7590262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590262).length < 2 ^ (prefixWord ++ tailWord_7590262).sum := by decide
  have hdescent : baseEnd_7590262 < baseStart_7590262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590281 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 2, 5]
def baseStart_7590281 : Nat := 118140960795 + 7590281 * 2 ^ 59
def prefixEnd_7590281 : Nat := 4983230072969 + 3 ^ 40 * 7590281 * 2
def baseEnd_7590281 : Nat := 1299154151896440908126813

theorem tailTrace_7590281 : CollatzResearch.WordTrace tailWord_7590281 prefixEnd_7590281 1299154151896440908126813 := by
  unfold tailWord_7590281
  simp only [CollatzResearch.WordTrace]
  refine ⟨276840291414715728634858697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184560194276477152423239131 276840291414715728634858697)
  ·
    refine ⟨207630218561036796476144023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276840291414715728634858697 207630218561036796476144023)
    ·
      refine ⟨311445327841555194714216035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207630218561036796476144023 311445327841555194714216035)
      ·
        refine ⟨467167991762332792071324053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311445327841555194714216035 467167991762332792071324053)
        ·
          refine ⟨21898499613859349628343315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 467167991762332792071324053 21898499613859349628343315)
          ·
            refine ⟨32847749420789024442514973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21898499613859349628343315 32847749420789024442514973)
            ·
              refine ⟨12317906032795884165943115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32847749420789024442514973 12317906032795884165943115)
              ·
                refine ⟨18476859049193826248914673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12317906032795884165943115 18476859049193826248914673)
                ·
                  refine ⟨13857644286895369686686005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18476859049193826248914673 13857644286895369686686005)
                  ·
                    refine ⟨1299154151896440908126813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13857644286895369686686005 1299154151896440908126813)
                    ·
                      rfl

theorem cell23_7590281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 5].length) (baseStart_7590281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590281 prefixEnd_7590281 := by exact prefixLift 7590281
  have htrace : WordTrace (prefixWord ++ tailWord_7590281) baseStart_7590281 baseEnd_7590281 := by
    simpa [prefixWord, tailWord_7590281, baseEnd_7590281] using wordTrace_append hprefix tailTrace_7590281
  have hstable : (prefixWord ++ tailWord_7590281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590281).length < 2 ^ (prefixWord ++ tailWord_7590281).sum := by decide
  have hdescent : baseEnd_7590281 < baseStart_7590281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590321 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 1, 4, 3]
def baseStart_7590321 : Nat := 118140960795 + 7590321 * 2 ^ 59
def prefixEnd_7590321 : Nat := 4983230072969 + 3 ^ 40 * 7590321 * 2
def baseEnd_7590321 : Nat := 3897482994915502567880255

theorem tailTrace_7590321 : CollatzResearch.WordTrace tailWord_7590321 prefixEnd_7590321 3897482994915502567880255 := by
  unfold tailWord_7590321
  simp only [CollatzResearch.WordTrace]
  refine ⟨276841750334570815466314817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184561166889713876977543211 276841750334570815466314817)
  ·
    refine ⟨207631312750928111599736113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276841750334570815466314817 207631312750928111599736113)
    ·
      refine ⟨155723484563196083699802085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207631312750928111599736113 155723484563196083699802085)
      ·
        refine ⟨29198153355599265693712891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155723484563196083699802085 29198153355599265693712891)
        ·
          refine ⟨43797230033398898540569337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29198153355599265693712891 43797230033398898540569337)
          ·
            refine ⟨32847922525049173905427003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43797230033398898540569337 32847922525049173905427003)
            ·
              refine ⟨49271883787573760858140505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32847922525049173905427003 49271883787573760858140505)
              ·
                refine ⟨36953912840680320643605379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49271883787573760858140505 36953912840680320643605379)
                ·
                  refine ⟨55430869261020480965408069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36953912840680320643605379 55430869261020480965408069)
                  ·
                    refine ⟨10393287986441340181014013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55430869261020480965408069 10393287986441340181014013)
                    ·
                      refine ⟨3897482994915502567880255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10393287986441340181014013 3897482994915502567880255)
                      ·
                        rfl

theorem cell23_7590321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_7590321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590321 prefixEnd_7590321 := by exact prefixLift 7590321
  have htrace : WordTrace (prefixWord ++ tailWord_7590321) baseStart_7590321 baseEnd_7590321 := by
    simpa [prefixWord, tailWord_7590321, baseEnd_7590321] using wordTrace_append hprefix tailTrace_7590321
  have hstable : (prefixWord ++ tailWord_7590321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590321).length < 2 ^ (prefixWord ++ tailWord_7590321).sum := by decide
  have hdescent : baseEnd_7590321 < baseStart_7590321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590358 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_7590358 : Nat := 118140960795 + 7590358 * 2 ^ 59
def prefixEnd_7590358 : Nat := 4983230072969 + 3 ^ 40 * 7590358 * 2
def baseEnd_7590358 : Nat := 433055777077746547013065

theorem tailTrace_7590358 : CollatzResearch.WordTrace tailWord_7590358 prefixEnd_7590358 433055777077746547013065 := by
  unfold tailWord_7590358
  simp only [CollatzResearch.WordTrace]
  refine ⟨17302693739714798174088233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184562066556957847190274485 17302693739714798174088233)
  ·
    refine ⟨12977020304786098630566175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17302693739714798174088233 12977020304786098630566175)
    ·
      refine ⟨19465530457179147945849263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12977020304786098630566175 19465530457179147945849263)
      ·
        refine ⟨29198295685768721918773895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19465530457179147945849263 29198295685768721918773895)
        ·
          refine ⟨43797443528653082878160843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29198295685768721918773895 43797443528653082878160843)
          ·
            refine ⟨65696165292979624317241265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43797443528653082878160843 65696165292979624317241265)
            ·
              refine ⟨49272123969734718237930949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65696165292979624317241265 49272123969734718237930949)
              ·
                refine ⟨9238523244325259669612053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49272123969734718237930949 9238523244325259669612053)
                ·
                  refine ⟨433055777077746547013065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9238523244325259669612053 433055777077746547013065)
                  ·
                    rfl

theorem cell23_7590358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_7590358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590358 prefixEnd_7590358 := by exact prefixLift 7590358
  have htrace : WordTrace (prefixWord ++ tailWord_7590358) baseStart_7590358 baseEnd_7590358 := by
    simpa [prefixWord, tailWord_7590358, baseEnd_7590358] using wordTrace_append hprefix tailTrace_7590358
  have hstable : (prefixWord ++ tailWord_7590358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590358).length < 2 ^ (prefixWord ++ tailWord_7590358).sum := by decide
  have hdescent : baseEnd_7590358 < baseStart_7590358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590401 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 3, 6]
def baseStart_7590401 : Nat := 118140960795 + 7590401 * 2 ^ 59
def prefixEnd_7590401 : Nat := 4983230072969 + 3 ^ 40 * 7590401 * 2
def baseEnd_7590401 : Nat := 1299174691122620751626629

theorem tailTrace_7590401 : CollatzResearch.WordTrace tailWord_7590401 prefixEnd_7590401 1299174691122620751626629 := by
  unfold tailWord_7590401
  simp only [CollatzResearch.WordTrace]
  refine ⟨276844668174280989129227057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184563112116187326086151371 276844668174280989129227057)
  ·
    refine ⟨207633501130710741846920293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276844668174280989129227057 207633501130710741846920293)
    ·
      refine ⟨38931281462008264096297555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207633501130710741846920293 38931281462008264096297555)
      ·
        refine ⟨58396922193012396144446333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38931281462008264096297555 58396922193012396144446333)
        ·
          refine ⟨21898845822379648554167375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58396922193012396144446333 21898845822379648554167375)
          ·
            refine ⟨32848268733569472831251063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21898845822379648554167375 32848268733569472831251063)
            ·
              refine ⟨49272403100354209246876595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32848268733569472831251063 49272403100354209246876595)
              ·
                refine ⟨73908604650531313870314893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49272403100354209246876595 73908604650531313870314893)
                ·
                  refine ⟨27715726743949242701368085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73908604650531313870314893 27715726743949242701368085)
                  ·
                    refine ⟨1299174691122620751626629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27715726743949242701368085 1299174691122620751626629)
                    ·
                      rfl

theorem cell23_7590401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_7590401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590401 prefixEnd_7590401 := by exact prefixLift 7590401
  have htrace : WordTrace (prefixWord ++ tailWord_7590401) baseStart_7590401 baseEnd_7590401 := by
    simpa [prefixWord, tailWord_7590401, baseEnd_7590401] using wordTrace_append hprefix tailTrace_7590401
  have hstable : (prefixWord ++ tailWord_7590401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590401).length < 2 ^ (prefixWord ++ tailWord_7590401).sum := by decide
  have hdescent : baseEnd_7590401 < baseStart_7590401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590421 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_7590421 : Nat := 118140960795 + 7590421 * 2 ^ 59
def prefixEnd_7590421 : Nat := 4983230072969 + 3 ^ 40 * 7590421 * 2
def baseEnd_7590421 : Nat := 3897534342980952176629795

theorem tailTrace_7590421 : CollatzResearch.WordTrace tailWord_7590421 prefixEnd_7590421 3897534342980952176629795 := by
  unfold tailWord_7590421
  simp only [CollatzResearch.WordTrace]
  refine ⟨276845397634208532544955117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184563598422805688363303411 276845397634208532544955117)
  ·
    refine ⟨103817024112828199704358169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276845397634208532544955117 103817024112828199704358169)
    ·
      refine ⟨77862768084621149778268627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103817024112828199704358169 77862768084621149778268627)
      ·
        refine ⟨116794152126931724667402941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77862768084621149778268627 116794152126931724667402941)
        ·
          refine ⟨43797807047599396750276103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116794152126931724667402941 43797807047599396750276103)
          ·
            refine ⟨65696710571399095125414155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43797807047599396750276103 65696710571399095125414155)
            ·
              refine ⟨98545065857098642688121233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65696710571399095125414155 98545065857098642688121233)
              ·
                refine ⟨73908799392823982016090925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98545065857098642688121233 73908799392823982016090925)
                ·
                  refine ⟨27715799772308993256034097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73908799392823982016090925 27715799772308993256034097)
                  ·
                    refine ⟨20786849829231744942025573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27715799772308993256034097 20786849829231744942025573)
                    ·
                      refine ⟨3897534342980952176629795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20786849829231744942025573 3897534342980952176629795)
                      ·
                        rfl

theorem cell23_7590421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_7590421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590421 prefixEnd_7590421 := by exact prefixLift 7590421
  have htrace : WordTrace (prefixWord ++ tailWord_7590421) baseStart_7590421 baseEnd_7590421 := by
    simpa [prefixWord, tailWord_7590421, baseEnd_7590421] using wordTrace_append hprefix tailTrace_7590421
  have hstable : (prefixWord ++ tailWord_7590421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590421).length < 2 ^ (prefixWord ++ tailWord_7590421).sum := by decide
  have hdescent : baseEnd_7590421 < baseStart_7590421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590428 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_7590428 : Nat := 118140960795 + 7590428 * 2 ^ 59
def prefixEnd_7590428 : Nat := 4983230072969 + 3 ^ 40 * 7590428 * 2
def baseEnd_7590428 : Nat := 3897537937345533649242263

theorem tailTrace_7590428 : CollatzResearch.WordTrace tailWord_7590428 prefixEnd_7590428 3897537937345533649242263 := by
  unfold tailWord_7590428
  simp only [CollatzResearch.WordTrace]
  refine ⟨138422826472591586370229969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184563768630122115160306625 138422826472591586370229969)
  ·
    refine ⟨103817119854443689777672477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138422826472591586370229969 103817119854443689777672477)
    ·
      refine ⟨38931419945416383666627179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103817119854443689777672477 38931419945416383666627179)
      ·
        refine ⟨58397129918124575499940769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38931419945416383666627179 58397129918124575499940769)
        ·
          refine ⟨43797847438593431624955577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58397129918124575499940769 43797847438593431624955577)
          ·
            refine ⟨32848385578945073718716683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43797847438593431624955577 32848385578945073718716683)
            ·
              refine ⟨49272578368417610578075025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32848385578945073718716683 49272578368417610578075025)
              ·
                refine ⟨36954433776313207933556269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49272578368417610578075025 36954433776313207933556269)
                ·
                  refine ⟨13857912666117452975083601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36954433776313207933556269 13857912666117452975083601)
                  ·
                    refine ⟨10393434499588089731312701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13857912666117452975083601 10393434499588089731312701)
                    ·
                      refine ⟨3897537937345533649242263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10393434499588089731312701 3897537937345533649242263)
                      ·
                        rfl

theorem cell23_7590428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_7590428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590428 prefixEnd_7590428 := by exact prefixLift 7590428
  have htrace : WordTrace (prefixWord ++ tailWord_7590428) baseStart_7590428 baseEnd_7590428 := by
    simpa [prefixWord, tailWord_7590428, baseEnd_7590428] using wordTrace_append hprefix tailTrace_7590428
  have hstable : (prefixWord ++ tailWord_7590428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590428).length < 2 ^ (prefixWord ++ tailWord_7590428).sum := by decide
  have hdescent : baseEnd_7590428 < baseStart_7590428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590442 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_7590442 : Nat := 118140960795 + 7590442 * 2 ^ 59
def prefixEnd_7590442 : Nat := 4983230072969 + 3 ^ 40 * 7590442 * 2
def baseEnd_7590442 : Nat := 3897545126074696594467199

theorem tailTrace_7590442 : CollatzResearch.WordTrace tailWord_7590442 prefixEnd_7590442 3897545126074696594467199 := by
  unfold tailWord_7590442
  simp only [CollatzResearch.WordTrace]
  refine ⟨69211540891783113282867395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184564109044754968754313053 69211540891783113282867395)
  ·
    refine ⟨103817311337674669924301093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69211540891783113282867395 103817311337674669924301093)
    ·
      refine ⟨19465745875814000610806455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103817311337674669924301093 19465745875814000610806455)
      ·
        refine ⟨29198618813721000916209683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19465745875814000610806455 29198618813721000916209683)
        ·
          refine ⟨43797928220581501374314525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29198618813721000916209683 43797928220581501374314525)
          ·
            refine ⟨16424223082718063015367947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43797928220581501374314525 16424223082718063015367947)
            ·
              refine ⟨24636334624077094523051921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16424223082718063015367947 24636334624077094523051921)
              ·
                refine ⟨18477250968057820892288941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24636334624077094523051921 18477250968057820892288941)
                ·
                  refine ⟨6928969113021682834608353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18477250968057820892288941 6928969113021682834608353)
                  ·
                    refine ⟨5196726834766262125956265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6928969113021682834608353 5196726834766262125956265)
                    ·
                      refine ⟨3897545126074696594467199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196726834766262125956265 3897545126074696594467199)
                      ·
                        rfl

theorem cell23_7590442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_7590442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590442 prefixEnd_7590442 := by exact prefixLift 7590442
  have htrace : WordTrace (prefixWord ++ tailWord_7590442) baseStart_7590442 baseEnd_7590442 := by
    simpa [prefixWord, tailWord_7590442, baseEnd_7590442] using wordTrace_append hprefix tailTrace_7590442
  have hstable : (prefixWord ++ tailWord_7590442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590442).length < 2 ^ (prefixWord ++ tailWord_7590442).sum := by decide
  have hdescent : baseEnd_7590442 < baseStart_7590442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590458 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3]
def baseStart_7590458 : Nat := 118140960795 + 7590458 * 2 ^ 59
def prefixEnd_7590458 : Nat := 4983230072969 + 3 ^ 40 * 7590458 * 2
def baseEnd_7590458 : Nat := 3897553341765168531867125

theorem tailTrace_7590458 : CollatzResearch.WordTrace tailWord_7590458 prefixEnd_7590458 3897553341765168531867125 := by
  unfold tailWord_7590458
  simp only [CollatzResearch.WordTrace]
  refine ⟨69211686783768621966013007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184564498090049658576034685 69211686783768621966013007)
  ·
    refine ⟨103817530175652932949019511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69211686783768621966013007 103817530175652932949019511)
    ·
      refine ⟨155726295263479399423529267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103817530175652932949019511 155726295263479399423529267)
      ·
        refine ⟨233589442895219099135293901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155726295263479399423529267 233589442895219099135293901)
        ·
          refine ⟨87596041085707162175735213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233589442895219099135293901 87596041085707162175735213)
          ·
            refine ⟨32848515407140185815900705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87596041085707162175735213 32848515407140185815900705)
            ·
              refine ⟨24636386555355139361925529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32848515407140185815900705 24636386555355139361925529)
              ·
                refine ⟨18477289916516354521444147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24636386555355139361925529 18477289916516354521444147)
                ·
                  refine ⟨27715934874774531782166221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18477289916516354521444147 27715934874774531782166221)
                  ·
                    refine ⟨10393475578040449418312333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27715934874774531782166221 10393475578040449418312333)
                    ·
                      refine ⟨3897553341765168531867125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10393475578040449418312333 3897553341765168531867125)
                      ·
                        rfl

theorem cell23_7590458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_7590458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590458 prefixEnd_7590458 := by exact prefixLift 7590458
  have htrace : WordTrace (prefixWord ++ tailWord_7590458) baseStart_7590458 baseEnd_7590458 := by
    simpa [prefixWord, tailWord_7590458, baseEnd_7590458] using wordTrace_append hprefix tailTrace_7590458
  have hstable : (prefixWord ++ tailWord_7590458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590458).length < 2 ^ (prefixWord ++ tailWord_7590458).sum := by decide
  have hdescent : baseEnd_7590458 < baseStart_7590458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590475 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 2, 1, 3]
def baseStart_7590475 : Nat := 118140960795 + 7590475 * 2 ^ 59
def prefixEnd_7590475 : Nat := 4983230072969 + 3 ^ 40 * 7590475 * 2
def baseEnd_7590475 : Nat := 3897562070936294965354547

theorem tailTrace_7590475 : CollatzResearch.WordTrace tailWord_7590475 prefixEnd_7590475 3897562070936294965354547 := by
  unfold tailWord_7590475
  simp only [CollatzResearch.WordTrace]
  refine ⟨276847367176012899767420879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184564911450675266511613919 276847367176012899767420879)
  ·
    refine ⟨415271050764019349651131319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276847367176012899767420879 415271050764019349651131319)
    ·
      refine ⟨622906576146029024476696979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415271050764019349651131319 622906576146029024476696979)
      ·
        refine ⟨934359864219043536715045469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622906576146029024476696979 934359864219043536715045469)
        ·
          refine ⟨350384949082141326268142051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 934359864219043536715045469 350384949082141326268142051)
          ·
            refine ⟨525577423623211989402213077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350384949082141326268142051 525577423623211989402213077)
            ·
              refine ⟨12318220866169031001614369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 525577423623211989402213077 12318220866169031001614369)
              ·
                refine ⟨9238665649626773251210777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12318220866169031001614369 9238665649626773251210777)
                ·
                  refine ⟨6928999237220079938408083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9238665649626773251210777 6928999237220079938408083)
                  ·
                    refine ⟨10393498855830119907612125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6928999237220079938408083 10393498855830119907612125)
                    ·
                      refine ⟨3897562070936294965354547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10393498855830119907612125 3897562070936294965354547)
                      ·
                        rfl

theorem cell23_7590475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 1, 3].length) (baseStart_7590475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590475 prefixEnd_7590475 := by exact prefixLift 7590475
  have htrace : WordTrace (prefixWord ++ tailWord_7590475) baseStart_7590475 baseEnd_7590475 := by
    simpa [prefixWord, tailWord_7590475, baseEnd_7590475] using wordTrace_append hprefix tailTrace_7590475
  have hstable : (prefixWord ++ tailWord_7590475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590475).length < 2 ^ (prefixWord ++ tailWord_7590475).sum := by decide
  have hdescent : baseEnd_7590475 < baseStart_7590475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590492 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_7590492 : Nat := 118140960795 + 7590492 * 2 ^ 59
def prefixEnd_7590492 : Nat := 4983230072969 + 3 ^ 40 * 7590492 * 2
def baseEnd_7590492 : Nat := 3897570800107421398841969

theorem tailTrace_7590492 : CollatzResearch.WordTrace tailWord_7590492 prefixEnd_7590492 3897570800107421398841969 := by
  unfold tailWord_7590492
  simp only [CollatzResearch.WordTrace]
  refine ⟨138423993608475655835394865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184565324811300874447193153 138423993608475655835394865)
  ·
    refine ⟨103817995206356741876546149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138423993608475655835394865 103817995206356741876546149)
    ·
      refine ⟨19465874101191889101852403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103817995206356741876546149 19465874101191889101852403)
      ·
        refine ⟨29198811151787833652778605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19465874101191889101852403 29198811151787833652778605)
        ·
          refine ⟨10949554181920437619791977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29198811151787833652778605 10949554181920437619791977)
          ·
            refine ⟨8212165636440328214843983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10949554181920437619791977 8212165636440328214843983)
            ·
              refine ⟨12318248454660492322265975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8212165636440328214843983 12318248454660492322265975)
              ·
                refine ⟨18477372681990738483398963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12318248454660492322265975 18477372681990738483398963)
                ·
                  refine ⟨27716059022986107725098445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18477372681990738483398963 27716059022986107725098445)
                  ·
                    refine ⟨10393522133619790396911917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27716059022986107725098445 10393522133619790396911917)
                    ·
                      refine ⟨3897570800107421398841969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10393522133619790396911917 3897570800107421398841969)
                      ·
                        rfl

theorem cell23_7590492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_7590492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590492 prefixEnd_7590492 := by exact prefixLift 7590492
  have htrace : WordTrace (prefixWord ++ tailWord_7590492) baseStart_7590492 baseEnd_7590492 := by
    simpa [prefixWord, tailWord_7590492, baseEnd_7590492] using wordTrace_append hprefix tailTrace_7590492
  have hstable : (prefixWord ++ tailWord_7590492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590492).length < 2 ^ (prefixWord ++ tailWord_7590492).sum := by decide
  have hdescent : baseEnd_7590492 < baseStart_7590492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590511 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 4]
def baseStart_7590511 : Nat := 118140960795 + 7590511 * 2 ^ 59
def prefixEnd_7590511 : Nat := 4983230072969 + 3 ^ 40 * 7590511 * 2
def baseEnd_7590511 : Nat := 3897580556239856824504381

theorem tailTrace_7590511 : CollatzResearch.WordTrace tailWord_7590511 prefixEnd_7590511 3897580556239856824504381 := by
  unfold tailWord_7590511
  simp only [CollatzResearch.WordTrace]
  refine ⟨276848680203882477915731387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184565786802588318610487591 276848680203882477915731387)
  ·
    refine ⟨415273020305823716873597081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276848680203882477915731387 415273020305823716873597081)
    ·
      refine ⟨311454765229367787655197811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415273020305823716873597081 311454765229367787655197811)
      ·
        refine ⟨467182147844051681482796717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311454765229367787655197811 467182147844051681482796717)
        ·
          refine ⟨175193305441519380556048769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467182147844051681482796717 175193305441519380556048769)
          ·
            refine ⟨131394979081139535417036577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175193305441519380556048769 131394979081139535417036577)
            ·
              refine ⟨98546234310854651562777433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131394979081139535417036577 98546234310854651562777433)
              ·
                refine ⟨73909675733140988672083075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98546234310854651562777433 73909675733140988672083075)
                ·
                  refine ⟨110864513599711483008124613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73909675733140988672083075 110864513599711483008124613)
                  ·
                    refine ⟨20787096299945903064023365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110864513599711483008124613 20787096299945903064023365)
                    ·
                      refine ⟨3897580556239856824504381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20787096299945903064023365 3897580556239856824504381)
                      ·
                        rfl

theorem cell23_7590511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_7590511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590511 prefixEnd_7590511 := by exact prefixLift 7590511
  have htrace : WordTrace (prefixWord ++ tailWord_7590511) baseStart_7590511 baseEnd_7590511 := by
    simpa [prefixWord, tailWord_7590511, baseEnd_7590511] using wordTrace_append hprefix tailTrace_7590511
  have hstable : (prefixWord ++ tailWord_7590511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590511).length < 2 ^ (prefixWord ++ tailWord_7590511).sum := by decide
  have hdescent : baseEnd_7590511 < baseStart_7590511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590532 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_7590532 : Nat := 118140960795 + 7590532 * 2 ^ 59
def prefixEnd_7590532 : Nat := 4983230072969 + 3 ^ 40 * 7590532 * 2
def baseEnd_7590532 : Nat := 3897591339333601242341785

theorem tailTrace_7590532 : CollatzResearch.WordTrace tailWord_7590532 prefixEnd_7590532 3897591339333601242341785 := by
  unfold tailWord_7590532
  simp only [CollatzResearch.WordTrace]
  refine ⟨138424723068403199251122925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184566297424537599001497233 138424723068403199251122925)
  ·
    refine ⟨51909271150651199719171097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138424723068403199251122925 51909271150651199719171097)
    ·
      refine ⟨38931953362988399789378323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51909271150651199719171097 38931953362988399789378323)
      ·
        refine ⟨58397930044482599684067485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38931953362988399789378323 58397930044482599684067485)
        ·
          refine ⟨21899223766680974881525307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58397930044482599684067485 21899223766680974881525307)
          ·
            refine ⟨32848835650021462322287961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21899223766680974881525307 32848835650021462322287961)
            ·
              refine ⟨24636626737516096741715971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32848835650021462322287961 24636626737516096741715971)
              ·
                refine ⟨36954940106274145112573957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24636626737516096741715971 36954940106274145112573957)
                ·
                  refine ⟨6929051269926402208607617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36954940106274145112573957 6929051269926402208607617)
                  ·
                    refine ⟨5196788452444801656455713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6929051269926402208607617 5196788452444801656455713)
                    ·
                      refine ⟨3897591339333601242341785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196788452444801656455713 3897591339333601242341785)
                      ·
                        rfl

theorem cell23_7590532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_7590532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590532 prefixEnd_7590532 := by exact prefixLift 7590532
  have htrace : WordTrace (prefixWord ++ tailWord_7590532) baseStart_7590532 baseEnd_7590532 := by
    simpa [prefixWord, tailWord_7590532, baseEnd_7590532] using wordTrace_append hprefix tailTrace_7590532
  have hstable : (prefixWord ++ tailWord_7590532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590532).length < 2 ^ (prefixWord ++ tailWord_7590532).sum := by decide
  have hdescent : baseEnd_7590532 < baseStart_7590532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590615 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 3, 4]
def baseStart_7590615 : Nat := 118140960795 + 7590615 * 2 ^ 59
def prefixEnd_7590615 : Nat := 4983230072969 + 3 ^ 40 * 7590615 * 2
def baseEnd_7590615 : Nat := 1299211319409308139201301

theorem tailTrace_7590615 : CollatzResearch.WordTrace tailWord_7590615 prefixEnd_7590615 1299211319409308139201301 := by
  unfold tailWord_7590615
  simp only [CollatzResearch.WordTrace]
  refine ⟨276852473395505703677517299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184568315597003802451678199 276852473395505703677517299)
  ·
    refine ⟨415278710093258555516275949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276852473395505703677517299 415278710093258555516275949)
    ·
      refine ⟨155729516284971958318603481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415278710093258555516275949 155729516284971958318603481)
      ·
        refine ⟨116797137213728968738952611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155729516284971958318603481 116797137213728968738952611)
        ·
          refine ⟨175195705820593453108428917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116797137213728968738952611 175195705820593453108428917)
          ·
            refine ⟨16424597420680636228915211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175195705820593453108428917 16424597420680636228915211)
            ·
              refine ⟨24636896131020954343372817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16424597420680636228915211 24636896131020954343372817)
              ·
                refine ⟨18477672098265715757529613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24636896131020954343372817 18477672098265715757529613)
                ·
                  refine ⟨6929127036849643409073605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18477672098265715757529613 6929127036849643409073605)
                  ·
                    refine ⟨1299211319409308139201301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6929127036849643409073605 1299211319409308139201301)
                    ·
                      rfl

theorem cell23_7590615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_7590615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590615 prefixEnd_7590615 := by exact prefixLift 7590615
  have htrace : WordTrace (prefixWord ++ tailWord_7590615) baseStart_7590615 baseEnd_7590615 := by
    simpa [prefixWord, tailWord_7590615, baseEnd_7590615] using wordTrace_append hprefix tailTrace_7590615
  have hstable : (prefixWord ++ tailWord_7590615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590615).length < 2 ^ (prefixWord ++ tailWord_7590615).sum := by decide
  have hdescent : baseEnd_7590615 < baseStart_7590615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590625 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_7590625 : Nat := 118140960795 + 7590625 * 2 ^ 59
def prefixEnd_7590625 : Nat := 4983230072969 + 3 ^ 40 * 7590625 * 2
def baseEnd_7590625 : Nat := 3897639093034469378478857

theorem tailTrace_7590625 : CollatzResearch.WordTrace tailWord_7590625 prefixEnd_7590625 3897639093034469378478857 := by
  unfold tailWord_7590625
  simp only [CollatzResearch.WordTrace]
  refine ⟨276852838125469475385381329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184568558750312983590254219 276852838125469475385381329)
  ·
    refine ⟨207639628594102106539035997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276852838125469475385381329 207639628594102106539035997)
    ·
      refine ⟨77864860722788289952138499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207639628594102106539035997 77864860722788289952138499)
      ·
        refine ⟨116797291084182434928207749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77864860722788289952138499 116797291084182434928207749)
        ·
          refine ⟨21899492078284206549038953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116797291084182434928207749 21899492078284206549038953)
          ·
            refine ⟨16424619058713154911779215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21899492078284206549038953 16424619058713154911779215)
            ·
              refine ⟨24636928588069732367668823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16424619058713154911779215 24636928588069732367668823)
              ·
                refine ⟨36955392882104598551503235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24636928588069732367668823 36955392882104598551503235)
                ·
                  refine ⟨55433089323156897827254853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36955392882104598551503235 55433089323156897827254853)
                  ·
                    refine ⟨10393704248091918342610285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55433089323156897827254853 10393704248091918342610285)
                    ·
                      refine ⟨3897639093034469378478857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10393704248091918342610285 3897639093034469378478857)
                      ·
                        rfl

theorem cell23_7590625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_7590625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590625 prefixEnd_7590625 := by exact prefixLift 7590625
  have htrace : WordTrace (prefixWord ++ tailWord_7590625) baseStart_7590625 baseEnd_7590625 := by
    simpa [prefixWord, tailWord_7590625, baseEnd_7590625] using wordTrace_append hprefix tailTrace_7590625
  have hstable : (prefixWord ++ tailWord_7590625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590625).length < 2 ^ (prefixWord ++ tailWord_7590625).sum := by decide
  have hdescent : baseEnd_7590625 < baseStart_7590625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590665 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 1, 5, 2]
def baseStart_7590665 : Nat := 118140960795 + 7590665 * 2 ^ 59
def prefixEnd_7590665 : Nat := 4983230072969 + 3 ^ 40 * 7590665 * 2
def baseEnd_7590665 : Nat := 3897659632260649221978673

theorem tailTrace_7590665 : CollatzResearch.WordTrace tailWord_7590665 prefixEnd_7590665 3897659632260649221978673 := by
  unfold tailWord_7590665
  simp only [CollatzResearch.WordTrace]
  refine ⟨276854297045324562216837449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184569531363549708144558299 276854297045324562216837449)
  ·
    refine ⟨207640722783993421662628087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276854297045324562216837449 207640722783993421662628087)
    ·
      refine ⟨311461084175990132493942131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207640722783993421662628087 311461084175990132493942131)
      ·
        refine ⟨467191626263985198740913197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311461084175990132493942131 467191626263985198740913197)
        ·
          refine ⟨175196859848994449527842449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467191626263985198740913197 175196859848994449527842449)
          ·
            refine ⟨131397644886745837145881837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175196859848994449527842449 131397644886745837145881837)
            ·
              refine ⟨49274116832529688929705689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131397644886745837145881837 49274116832529688929705689)
              ·
                refine ⟨36955587624397266697279267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49274116832529688929705689 36955587624397266697279267)
                ·
                  refine ⟨55433381436595900045918901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36955587624397266697279267 55433381436595900045918901)
                  ·
                    refine ⟨5196879509680865629304897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55433381436595900045918901 5196879509680865629304897)
                    ·
                      refine ⟨3897659632260649221978673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196879509680865629304897 3897659632260649221978673)
                      ·
                        rfl

theorem cell23_7590665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 5, 2].length) (baseStart_7590665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590665 prefixEnd_7590665 := by exact prefixLift 7590665
  have htrace : WordTrace (prefixWord ++ tailWord_7590665) baseStart_7590665 baseEnd_7590665 := by
    simpa [prefixWord, tailWord_7590665, baseEnd_7590665] using wordTrace_append hprefix tailTrace_7590665
  have hstable : (prefixWord ++ tailWord_7590665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590665).length < 2 ^ (prefixWord ++ tailWord_7590665).sum := by decide
  have hdescent : baseEnd_7590665 < baseStart_7590665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590675 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 1, 5]
def baseStart_7590675 : Nat := 118140960795 + 7590675 * 2 ^ 59
def prefixEnd_7590675 : Nat := 4983230072969 + 3 ^ 40 * 7590675 * 2
def baseEnd_7590675 : Nat := 1299221589022398060951209

theorem tailTrace_7590675 : CollatzResearch.WordTrace tailWord_7590675 prefixEnd_7590675 1299221589022398060951209 := by
  unfold tailWord_7590675
  simp only [CollatzResearch.WordTrace]
  refine ⟨276854661775288333924701479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184569774516858889283134319 276854661775288333924701479)
  ·
    refine ⟨415281992662932500887052219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276854661775288333924701479 415281992662932500887052219)
    ·
      refine ⟨622922988994398751330578329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415281992662932500887052219 622922988994398751330578329)
      ·
        refine ⟨467192241745799063497933747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622922988994398751330578329 467192241745799063497933747)
        ·
          refine ⟨700788362618698595246900621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467192241745799063497933747 700788362618698595246900621)
          ·
            refine ⟨262795635982011973217587733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 700788362618698595246900621 262795635982011973217587733)
            ·
              refine ⟨12318545436656811244574425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 262795635982011973217587733 12318545436656811244574425)
              ·
                refine ⟨9238909077492608433430819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12318545436656811244574425 9238909077492608433430819)
                ·
                  refine ⟨13858363616238912650146229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9238909077492608433430819 13858363616238912650146229)
                  ·
                    refine ⟨1299221589022398060951209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13858363616238912650146229 1299221589022398060951209)
                    ·
                      rfl

theorem cell23_7590675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 5].length) (baseStart_7590675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590675 prefixEnd_7590675 := by exact prefixLift 7590675
  have htrace : WordTrace (prefixWord ++ tailWord_7590675) baseStart_7590675 baseEnd_7590675 := by
    simpa [prefixWord, tailWord_7590675, baseEnd_7590675] using wordTrace_append hprefix tailTrace_7590675
  have hstable : (prefixWord ++ tailWord_7590675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590675).length < 2 ^ (prefixWord ++ tailWord_7590675).sum := by decide
  have hdescent : baseEnd_7590675 < baseStart_7590675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590682 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2]
def baseStart_7590682 : Nat := 118140960795 + 7590682 * 2 ^ 59
def prefixEnd_7590682 : Nat := 4983230072969 + 3 ^ 40 * 7590682 * 2
def baseEnd_7590682 : Nat := 3897668361431775655466095

theorem tailTrace_7590682 : CollatzResearch.WordTrace tailWord_7590682 prefixEnd_7590682 3897668361431775655466095 := by
  unfold tailWord_7590682
  simp only [CollatzResearch.WordTrace]
  refine ⟨69213729271565743530051575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184569944724175316080137533 69213729271565743530051575)
  ·
    refine ⟨103820593907348615295077363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69213729271565743530051575 103820593907348615295077363)
    ·
      refine ⟨155730890861022922942616045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103820593907348615295077363 155730890861022922942616045)
      ·
        refine ⟨58399084072883596103481017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155730890861022922942616045 58399084072883596103481017)
        ·
          refine ⟨43799313054662697077610763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58399084072883596103481017 43799313054662697077610763)
          ·
            refine ⟨65698969581994045616416145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43799313054662697077610763 65698969581994045616416145)
            ·
              refine ⟨49274227186495534212312109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65698969581994045616416145 49274227186495534212312109)
              ·
                refine ⟨18477835194935825329617041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49274227186495534212312109 18477835194935825329617041)
                ·
                  refine ⟨13858376396201868997212781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18477835194935825329617041 13858376396201868997212781)
                  ·
                    refine ⟨5196891148575700873954793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13858376396201868997212781 5196891148575700873954793)
                    ·
                      refine ⟨3897668361431775655466095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5196891148575700873954793 3897668361431775655466095)
                      ·
                        rfl

theorem cell23_7590682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_7590682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590682 prefixEnd_7590682 := by exact prefixLift 7590682
  have htrace : WordTrace (prefixWord ++ tailWord_7590682) baseStart_7590682 baseEnd_7590682 := by
    simpa [prefixWord, tailWord_7590682, baseEnd_7590682] using wordTrace_append hprefix tailTrace_7590682
  have hstable : (prefixWord ++ tailWord_7590682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590682).length < 2 ^ (prefixWord ++ tailWord_7590682).sum := by decide
  have hdescent : baseEnd_7590682 < baseStart_7590682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590705 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 4, 4]
def baseStart_7590705 : Nat := 118140960795 + 7590705 * 2 ^ 59
def prefixEnd_7590705 : Nat := 4983230072969 + 3 ^ 40 * 7590705 * 2
def baseEnd_7590705 : Nat := 1299226723828943021826163

theorem tailTrace_7590705 : CollatzResearch.WordTrace tailWord_7590705 prefixEnd_7590705 1299226723828943021826163 := by
  unfold tailWord_7590705
  simp only [CollatzResearch.WordTrace]
  refine ⟨276855755965179649048293569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184570503976786432698862379 276855755965179649048293569)
  ·
    refine ⟨207641816973884736786220177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276855755965179649048293569 207641816973884736786220177)
    ·
      refine ⟨155731362730413552589665133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207641816973884736786220177 155731362730413552589665133)
      ·
        refine ⟨58399261023905082221124425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155731362730413552589665133 58399261023905082221124425)
        ·
          refine ⟨43799445767928811665843319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58399261023905082221124425 43799445767928811665843319)
          ·
            refine ⟨65699168651893217498764979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43799445767928811665843319 65699168651893217498764979)
            ·
              refine ⟨98548752977839826248147469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65699168651893217498764979 98548752977839826248147469)
              ·
                refine ⟨36955782366689934843055301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98548752977839826248147469 36955782366689934843055301)
                ·
                  refine ⟨6929209193754362783072869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36955782366689934843055301 6929209193754362783072869)
                  ·
                    refine ⟨1299226723828943021826163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6929209193754362783072869 1299226723828943021826163)
                    ·
                      rfl

theorem cell23_7590705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_7590705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590705 prefixEnd_7590705 := by exact prefixLift 7590705
  have htrace : WordTrace (prefixWord ++ tailWord_7590705) baseStart_7590705 baseEnd_7590705 := by
    simpa [prefixWord, tailWord_7590705, baseEnd_7590705] using wordTrace_append hprefix tailTrace_7590705
  have hstable : (prefixWord ++ tailWord_7590705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590705).length < 2 ^ (prefixWord ++ tailWord_7590705).sum := by decide
  have hdescent : baseEnd_7590705 < baseStart_7590705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590706 : List Nat := [3, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3]
def baseStart_7590706 : Nat := 118140960795 + 7590706 * 2 ^ 59
def prefixEnd_7590706 : Nat := 4983230072969 + 3 ^ 40 * 7590706 * 2
def baseEnd_7590706 : Nat := 3897680684967483561565985

theorem tailTrace_7590706 : CollatzResearch.WordTrace tailWord_7590706 prefixEnd_7590706 3897680684967483561565985 := by
  unfold tailWord_7590706
  simp only [CollatzResearch.WordTrace]
  refine ⟨69213948109544006554769993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184570528292117350812719981 69213948109544006554769993)
  ·
    refine ⟨51910461082158004916077495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69213948109544006554769993 51910461082158004916077495)
    ·
      refine ⟨77865691623237007374116243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51910461082158004916077495 77865691623237007374116243)
      ·
        refine ⟨116798537434855511061174365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77865691623237007374116243 116798537434855511061174365)
        ·
          refine ⟨43799451538070816647940387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116798537434855511061174365 43799451538070816647940387)
          ·
            refine ⟨65699177307106224971910581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43799451538070816647940387 65699177307106224971910581)
            ·
              refine ⟨6159297872541208591116617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65699177307106224971910581 6159297872541208591116617)
              ·
                refine ⟨4619473404405906443337463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6159297872541208591116617 4619473404405906443337463)
                ·
                  refine ⟨6929210106608859665006195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4619473404405906443337463 6929210106608859665006195)
                  ·
                    refine ⟨10393815159913289497509293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6929210106608859665006195 10393815159913289497509293)
                    ·
                      refine ⟨3897680684967483561565985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10393815159913289497509293 3897680684967483561565985)
                      ·
                        rfl

theorem cell23_7590706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_7590706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590706 prefixEnd_7590706 := by exact prefixLift 7590706
  have htrace : WordTrace (prefixWord ++ tailWord_7590706) baseStart_7590706 baseEnd_7590706 := by
    simpa [prefixWord, tailWord_7590706, baseEnd_7590706] using wordTrace_append hprefix tailTrace_7590706
  have hstable : (prefixWord ++ tailWord_7590706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590706).length < 2 ^ (prefixWord ++ tailWord_7590706).sum := by decide
  have hdescent : baseEnd_7590706 < baseStart_7590706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590732 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 3, 2, 3]
def baseStart_7590732 : Nat := 118140960795 + 7590732 * 2 ^ 59
def prefixEnd_7590732 : Nat := 4983230072969 + 3 ^ 40 * 7590732 * 2
def baseEnd_7590732 : Nat := 3897694035464500459840865

theorem tailTrace_7590732 : CollatzResearch.WordTrace tailWord_7590732 prefixEnd_7590732 3897694035464500459840865 := by
  unfold tailWord_7590732
  simp only [CollatzResearch.WordTrace]
  refine ⟨138428370368040916329763225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184571160490721221773017633 138428370368040916329763225)
  ·
    refine ⟨103821277776030687247322419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138428370368040916329763225 103821277776030687247322419)
    ·
      refine ⟨155731916664046030870983629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103821277776030687247322419 155731916664046030870983629)
      ·
        refine ⟨58399468749017261576618861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155731916664046030870983629 58399468749017261576618861)
        ·
          refine ⟨21899800780881473091232073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58399468749017261576618861 21899800780881473091232073)
          ·
            refine ⟨16424850585661104818424055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21899800780881473091232073 16424850585661104818424055)
            ·
              refine ⟨24637275878491657227636083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16424850585661104818424055 24637275878491657227636083)
              ·
                refine ⟨36955913817737485841454125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24637275878491657227636083 36955913817737485841454125)
                ·
                  refine ⟨13858467681651557190545297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36955913817737485841454125 13858467681651557190545297)
                  ·
                    refine ⟨10393850761238667892908973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13858467681651557190545297 10393850761238667892908973)
                    ·
                      refine ⟨3897694035464500459840865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10393850761238667892908973 3897694035464500459840865)
                      ·
                        rfl

theorem cell23_7590732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_7590732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590732 prefixEnd_7590732 := by exact prefixLift 7590732
  have htrace : WordTrace (prefixWord ++ tailWord_7590732) baseStart_7590732 baseEnd_7590732 := by
    simpa [prefixWord, tailWord_7590732, baseEnd_7590732] using wordTrace_append hprefix tailTrace_7590732
  have hstable : (prefixWord ++ tailWord_7590732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590732).length < 2 ^ (prefixWord ++ tailWord_7590732).sum := by decide
  have hdescent : baseEnd_7590732 < baseStart_7590732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590745 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 3, 3, 3]
def baseStart_7590745 : Nat := 118140960795 + 7590745 * 2 ^ 59
def prefixEnd_7590745 : Nat := 4983230072969 + 3 ^ 40 * 7590745 * 2
def baseEnd_7590745 : Nat := 3897700710713008908978305

theorem tailTrace_7590745 : CollatzResearch.WordTrace tailWord_7590745 prefixEnd_7590745 3897700710713008908978305 := by
  unfold tailWord_7590745
  simp only [CollatzResearch.WordTrace]
  refine ⟨276857214885034735879749689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184571476590023157253166459 276857214885034735879749689)
  ·
    refine ⟨207642911163776051909812267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276857214885034735879749689 207642911163776051909812267)
    ·
      refine ⟨311464366745664077864718401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207642911163776051909812267 311464366745664077864718401)
      ·
        refine ⟨233598275059248058398538801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311464366745664077864718401 233598275059248058398538801)
        ·
          refine ⟨175198706294436043798904101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233598275059248058398538801 175198706294436043798904101)
          ·
            refine ⟨32849757430206758212294519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175198706294436043798904101 32849757430206758212294519)
            ·
              refine ⟨49274636145310137318441779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32849757430206758212294519 49274636145310137318441779)
              ·
                refine ⟨73911954217965205977662669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49274636145310137318441779 73911954217965205977662669)
                ·
                  refine ⟨27716982831736952241623501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73911954217965205977662669 27716982831736952241623501)
                  ·
                    refine ⟨10393868561901357090608813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27716982831736952241623501 10393868561901357090608813)
                    ·
                      refine ⟨3897700710713008908978305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10393868561901357090608813 3897700710713008908978305)
                      ·
                        rfl

theorem cell23_7590745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_7590745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590745 prefixEnd_7590745 := by exact prefixLift 7590745
  have htrace : WordTrace (prefixWord ++ tailWord_7590745) baseStart_7590745 baseEnd_7590745 := by
    simpa [prefixWord, tailWord_7590745, baseEnd_7590745] using wordTrace_append hprefix tailTrace_7590745
  have hstable : (prefixWord ++ tailWord_7590745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590745).length < 2 ^ (prefixWord ++ tailWord_7590745).sum := by decide
  have hdescent : baseEnd_7590745 < baseStart_7590745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590786 : List Nat := [3, 4, 2, 2, 1, 1, 3, 7]
def baseStart_7590786 : Nat := 118140960795 + 7590786 * 2 ^ 59
def prefixEnd_7590786 : Nat := 4983230072969 + 3 ^ 40 * 7590786 * 2
def baseEnd_7590786 : Nat := 144360065311846046243171

theorem tailTrace_7590786 : CollatzResearch.WordTrace tailWord_7590786 prefixEnd_7590786 144360065311846046243171 := by
  unfold tailWord_7590786
  simp only [CollatzResearch.WordTrace]
  refine ⟨69214677569471549970498053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184572473518590799921328141 69214677569471549970498053)
  ·
    refine ⟨12977752044275915619468385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69214677569471549970498053 12977752044275915619468385)
    ·
      refine ⟨9733314033206936714601289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12977752044275915619468385 9733314033206936714601289)
      ·
        refine ⟨7299985524905202535950967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9733314033206936714601289 7299985524905202535950967)
        ·
          refine ⟨10949978287357803803926451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7299985524905202535950967 10949978287357803803926451)
          ·
            refine ⟨16424967431036705705889677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10949978287357803803926451 16424967431036705705889677)
            ·
              refine ⟨6159362786638764639708629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16424967431036705705889677 6159362786638764639708629)
              ·
                refine ⟨144360065311846046243171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6159362786638764639708629 144360065311846046243171)
                ·
                  rfl

theorem cell23_7590786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 7].length) (baseStart_7590786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590786 prefixEnd_7590786 := by exact prefixLift 7590786
  have htrace : WordTrace (prefixWord ++ tailWord_7590786) baseStart_7590786 baseEnd_7590786 := by
    simpa [prefixWord, tailWord_7590786, baseEnd_7590786] using wordTrace_append hprefix tailTrace_7590786
  have hstable : (prefixWord ++ tailWord_7590786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590786).length < 2 ^ (prefixWord ++ tailWord_7590786).sum := by decide
  have hdescent : baseEnd_7590786 < baseStart_7590786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590825 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 7]
def baseStart_7590825 : Nat := 118140960795 + 7590825 * 2 ^ 59
def prefixEnd_7590825 : Nat := 4983230072969 + 3 ^ 40 * 7590825 * 2
def baseEnd_7590825 : Nat := 433082421018374288441993

theorem tailTrace_7590825 : CollatzResearch.WordTrace tailWord_7590825 prefixEnd_7590825 433082421018374288441993 := by
  unfold tailWord_7590825
  simp only [CollatzResearch.WordTrace]
  refine ⟨276860132724744909542661929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184573421816496606361774619 276860132724744909542661929)
  ·
    refine ⟨207645099543558682156996447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276860132724744909542661929 207645099543558682156996447)
    ·
      refine ⟨311467649315338023235494671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207645099543558682156996447 311467649315338023235494671)
      ·
        refine ⟨467201473973007034853242007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311467649315338023235494671 467201473973007034853242007)
        ·
          refine ⟨700802210959510552279863011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467201473973007034853242007 700802210959510552279863011)
          ·
            refine ⟨1051203316439265828419794517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700802210959510552279863011 1051203316439265828419794517)
            ·
              refine ⟨12318788864522646426794467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1051203316439265828419794517 12318788864522646426794467)
              ·
                refine ⟨18478183296783969640191701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12318788864522646426794467 18478183296783969640191701)
                ·
                  refine ⟨433082421018374288441993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18478183296783969640191701 433082421018374288441993)
                  ·
                    rfl

theorem cell23_7590825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 7].length) (baseStart_7590825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590825 prefixEnd_7590825 := by exact prefixLift 7590825
  have htrace : WordTrace (prefixWord ++ tailWord_7590825) baseStart_7590825 baseEnd_7590825 := by
    simpa [prefixWord, tailWord_7590825, baseEnd_7590825] using wordTrace_append hprefix tailTrace_7590825
  have hstable : (prefixWord ++ tailWord_7590825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590825).length < 2 ^ (prefixWord ++ tailWord_7590825).sum := by decide
  have hdescent : baseEnd_7590825 < baseStart_7590825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590835 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 3]
def baseStart_7590835 : Nat := 118140960795 + 7590835 * 2 ^ 59
def prefixEnd_7590835 : Nat := 4983230072969 + 3 ^ 40 * 7590835 * 2
def baseEnd_7590835 : Nat := 3897746923971913556852891

theorem tailTrace_7590835 : CollatzResearch.WordTrace tailWord_7590835 prefixEnd_7590835 3897746923971913556852891 := by
  unfold tailWord_7590835
  simp only [CollatzResearch.WordTrace]
  refine ⟨276860497454708681250525959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184573664969805787500350639 276860497454708681250525959)
  ·
    refine ⟨415290746182063021875788939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276860497454708681250525959 415290746182063021875788939)
    ·
      refine ⟨622936119273094532813683409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415290746182063021875788939 622936119273094532813683409)
      ·
        refine ⟨467202089454820899610262557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622936119273094532813683409 467202089454820899610262557)
        ·
          refine ⟨175200783545557837353848459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467202089454820899610262557 175200783545557837353848459)
          ·
            refine ⟨262801175318336756030772689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175200783545557837353848459 262801175318336756030772689)
            ·
              refine ⟨197100881488752567023079517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262801175318336756030772689 197100881488752567023079517)
              ·
                refine ⟨73912830558282212633654819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197100881488752567023079517 73912830558282212633654819)
                ·
                  refine ⟨110869245837423318950482229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73912830558282212633654819 110869245837423318950482229)
                  ·
                    refine ⟨10393991797258436151607709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110869245837423318950482229 10393991797258436151607709)
                    ·
                      refine ⟨3897746923971913556852891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10393991797258436151607709 3897746923971913556852891)
                      ·
                        rfl

theorem cell23_7590835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 3].length) (baseStart_7590835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590835 prefixEnd_7590835 := by exact prefixLift 7590835
  have htrace : WordTrace (prefixWord ++ tailWord_7590835) baseStart_7590835 baseEnd_7590835 := by
    simpa [prefixWord, tailWord_7590835, baseEnd_7590835] using wordTrace_append hprefix tailTrace_7590835
  have hstable : (prefixWord ++ tailWord_7590835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590835).length < 2 ^ (prefixWord ++ tailWord_7590835).sum := by decide
  have hdescent : baseEnd_7590835 < baseStart_7590835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590855 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 1, 7]
def baseStart_7590855 : Nat := 118140960795 + 7590855 * 2 ^ 59
def prefixEnd_7590855 : Nat := 4983230072969 + 3 ^ 40 * 7590855 * 2
def baseEnd_7590855 : Nat := 1299252397861667826200933

theorem tailTrace_7590855 : CollatzResearch.WordTrace tailWord_7590855 prefixEnd_7590855 1299252397861667826200933 := by
  unfold tailWord_7590855
  simp only [CollatzResearch.WordTrace]
  refine ⟨276861226914636224666254019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184574151276424149777502679 276861226914636224666254019)
  ·
    refine ⟨415291840371954336999381029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276861226914636224666254019 415291840371954336999381029)
    ·
      refine ⟨77867220069741438187383943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415291840371954336999381029 77867220069741438187383943)
      ·
        refine ⟨116800830104612157281075915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77867220069741438187383943 116800830104612157281075915)
        ·
          refine ⟨175201245156918235921613873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116800830104612157281075915 175201245156918235921613873)
          ·
            refine ⟨131400933867688676941210405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175201245156918235921613873 131400933867688676941210405)
            ·
              refine ⟨24637675100191626926476951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131400933867688676941210405 24637675100191626926476951)
              ·
                refine ⟨36956512650287440389715427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24637675100191626926476951 36956512650287440389715427)
                ·
                  refine ⟨55434768975431160584573141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36956512650287440389715427 55434768975431160584573141)
                  ·
                    refine ⟨1299252397861667826200933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55434768975431160584573141 1299252397861667826200933)
                    ·
                      rfl

theorem cell23_7590855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_7590855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590855 prefixEnd_7590855 := by exact prefixLift 7590855
  have htrace : WordTrace (prefixWord ++ tailWord_7590855) baseStart_7590855 baseEnd_7590855 := by
    simpa [prefixWord, tailWord_7590855, baseEnd_7590855] using wordTrace_append hprefix tailTrace_7590855
  have hstable : (prefixWord ++ tailWord_7590855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590855).length < 2 ^ (prefixWord ++ tailWord_7590855).sum := by decide
  have hdescent : baseEnd_7590855 < baseStart_7590855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590859 : List Nat := [1, 1, 1, 1, 3, 7, 1, 3, 5]
def baseStart_7590859 : Nat := 118140960795 + 7590859 * 2 ^ 59
def prefixEnd_7590859 : Nat := 4983230072969 + 3 ^ 40 * 7590859 * 2
def baseEnd_7590859 : Nat := 433084360834180162550309

theorem tailTrace_7590859 : CollatzResearch.WordTrace tailWord_7590859 prefixEnd_7590859 433084360834180162550309 := by
  unfold tailWord_7590859
  simp only [CollatzResearch.WordTrace]
  refine ⟨276861372806621733349399631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184574248537747822232933087 276861372806621733349399631)
  ·
    refine ⟨415292059209932600024099447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276861372806621733349399631 415292059209932600024099447)
    ·
      refine ⟨622938088814898900036149171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415292059209932600024099447 622938088814898900036149171)
      ·
        refine ⟨934407133222348350054223757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622938088814898900036149171 934407133222348350054223757)
        ·
          refine ⟨350402674958380631270333909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 934407133222348350054223757 350402674958380631270333909)
          ·
            refine ⟨8212562694337046045398451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 350402674958380631270333909 8212562694337046045398451)
            ·
              refine ⟨12318844041505569068097677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8212562694337046045398451 12318844041505569068097677)
              ·
                refine ⟨4619566515564588400536629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12318844041505569068097677 4619566515564588400536629)
                ·
                  refine ⟨433084360834180162550309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4619566515564588400536629 433084360834180162550309)
                  ·
                    rfl

theorem cell23_7590859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 5].length) (baseStart_7590859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590859 prefixEnd_7590859 := by exact prefixLift 7590859
  have htrace : WordTrace (prefixWord ++ tailWord_7590859) baseStart_7590859 baseEnd_7590859 := by
    simpa [prefixWord, tailWord_7590859, baseEnd_7590859] using wordTrace_append hprefix tailTrace_7590859
  have hstable : (prefixWord ++ tailWord_7590859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590859).length < 2 ^ (prefixWord ++ tailWord_7590859).sum := by decide
  have hdescent : baseEnd_7590859 < baseStart_7590859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590865 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_7590865 : Nat := 118140960795 + 7590865 * 2 ^ 59
def prefixEnd_7590865 : Nat := 4983230072969 + 3 ^ 40 * 7590865 * 2
def baseEnd_7590865 : Nat := 3897762328391548439477753

theorem tailTrace_7590865 : CollatzResearch.WordTrace tailWord_7590865 prefixEnd_7590865 3897762328391548439477753 := by
  unfold tailWord_7590865
  simp only [CollatzResearch.WordTrace]
  refine ⟨276861591644599996374118049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184574394429733330916078699 276861591644599996374118049)
  ·
    refine ⟨207646193733449997280588537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276861591644599996374118049 207646193733449997280588537)
    ·
      refine ⟨155734645300087497960441403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207646193733449997280588537 155734645300087497960441403)
      ·
        refine ⟨233601967950131246940662105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155734645300087497960441403 233601967950131246940662105)
        ·
          refine ⟨175201475962598435205496579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233601967950131246940662105 175201475962598435205496579)
          ·
            refine ⟨262802213943897652808244869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175201475962598435205496579 262802213943897652808244869)
            ·
              refine ⟨49275415114480809901545913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262802213943897652808244869 49275415114480809901545913)
              ·
                refine ⟨36956561335860607426159435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49275415114480809901545913 36956561335860607426159435)
                ·
                  refine ⟨55434842003790911139239153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36956561335860607426159435 55434842003790911139239153)
                  ·
                    refine ⟨41576131502843183354429365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55434842003790911139239153 41576131502843183354429365)
                    ·
                      refine ⟨3897762328391548439477753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41576131502843183354429365 3897762328391548439477753)
                      ·
                        rfl

theorem cell23_7590865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_7590865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590865 prefixEnd_7590865 := by exact prefixLift 7590865
  have htrace : WordTrace (prefixWord ++ tailWord_7590865) baseStart_7590865 baseEnd_7590865 := by
    simpa [prefixWord, tailWord_7590865, baseEnd_7590865] using wordTrace_append hprefix tailTrace_7590865
  have hstable : (prefixWord ++ tailWord_7590865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590865).length < 2 ^ (prefixWord ++ tailWord_7590865).sum := by decide
  have hdescent : baseEnd_7590865 < baseStart_7590865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590872 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 2, 5]
def baseStart_7590872 : Nat := 118140960795 + 7590872 * 2 ^ 59
def prefixEnd_7590872 : Nat := 4983230072969 + 3 ^ 40 * 7590872 * 2
def baseEnd_7590872 : Nat := 1299255307585376637363407

theorem tailTrace_7590872 : CollatzResearch.WordTrace tailWord_7590872 prefixEnd_7590872 1299255307585376637363407 := by
  unfold tailWord_7590872
  simp only [CollatzResearch.WordTrace]
  refine ⟨138430923477787318284811435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184574564637049757713081913 138430923477787318284811435)
  ·
    refine ⟨207646385216680977427217153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138430923477787318284811435 207646385216680977427217153)
    ·
      refine ⟨155734788912510733070412865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207646385216680977427217153 155734788912510733070412865)
      ·
        refine ⟨116801091684383049802809649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155734788912510733070412865 116801091684383049802809649)
        ·
          refine ⟨87600818763287287352107237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116801091684383049802809649 87600818763287287352107237)
          ·
            refine ⟨16425153518116366378520107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87600818763287287352107237 16425153518116366378520107)
            ·
              refine ⟨24637730277174549567780161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16425153518116366378520107 24637730277174549567780161)
              ·
                refine ⟨18478297707880912175835121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24637730277174549567780161 18478297707880912175835121)
                ·
                  refine ⟨13858723280910684131876341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18478297707880912175835121 13858723280910684131876341)
                  ·
                    refine ⟨1299255307585376637363407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13858723280910684131876341 1299255307585376637363407)
                    ·
                      rfl

theorem cell23_7590872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_7590872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590872 prefixEnd_7590872 := by exact prefixLift 7590872
  have htrace : WordTrace (prefixWord ++ tailWord_7590872) baseStart_7590872 baseEnd_7590872 := by
    simpa [prefixWord, tailWord_7590872, baseEnd_7590872] using wordTrace_append hprefix tailTrace_7590872
  have hstable : (prefixWord ++ tailWord_7590872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590872).length < 2 ^ (prefixWord ++ tailWord_7590872).sum := by decide
  have hdescent : baseEnd_7590872 < baseStart_7590872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590936 : List Nat := [2, 1, 2, 3, 2, 3, 1, 4, 1, 4]
def baseStart_7590936 : Nat := 118140960795 + 7590936 * 2 ^ 59
def prefixEnd_7590936 : Nat := 4983230072969 + 3 ^ 40 * 7590936 * 2
def baseEnd_7590936 : Nat := 1299266261839339220563309

theorem tailTrace_7590936 : CollatzResearch.WordTrace tailWord_7590936 prefixEnd_7590936 1299266261839339220563309 := by
  unfold tailWord_7590936
  simp only [CollatzResearch.WordTrace]
  refine ⟨138432090613671387749976331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184576120818228516999968441 138432090613671387749976331)
  ·
    refine ⟨207648135920507081624964497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138432090613671387749976331 207648135920507081624964497)
    ·
      refine ⟨155736101940380311218723373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207648135920507081624964497 155736101940380311218723373)
      ·
        refine ⟨58401038227642616707021265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155736101940380311218723373 58401038227642616707021265)
        ·
          refine ⟨43800778670731962530265949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58401038227642616707021265 43800778670731962530265949)
          ·
            refine ⟨16425292001524485948849731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43800778670731962530265949 16425292001524485948849731)
            ·
              refine ⟨24637938002286728923274597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16425292001524485948849731 24637938002286728923274597)
              ·
                refine ⟨4619613375428761673113987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24637938002286728923274597 4619613375428761673113987)
                ·
                  refine ⟨6929420063143142509670981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4619613375428761673113987 6929420063143142509670981)
                  ·
                    refine ⟨1299266261839339220563309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6929420063143142509670981 1299266261839339220563309)
                    ·
                      rfl

theorem cell23_7590936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_7590936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590936 prefixEnd_7590936 := by exact prefixLift 7590936
  have htrace : WordTrace (prefixWord ++ tailWord_7590936) baseStart_7590936 baseEnd_7590936 := by
    simpa [prefixWord, tailWord_7590936, baseEnd_7590936] using wordTrace_append hprefix tailTrace_7590936
  have hstable : (prefixWord ++ tailWord_7590936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590936).length < 2 ^ (prefixWord ++ tailWord_7590936).sum := by decide
  have hdescent : baseEnd_7590936 < baseStart_7590936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590955 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 7]
def baseStart_7590955 : Nat := 118140960795 + 7590955 * 2 ^ 59
def prefixEnd_7590955 : Nat := 4983230072969 + 3 ^ 40 * 7590955 * 2
def baseEnd_7590955 : Nat := 3897808541650453087352339

theorem tailTrace_7590955 : CollatzResearch.WordTrace tailWord_7590955 prefixEnd_7590955 3897808541650453087352339 := by
  unfold tailWord_7590955
  simp only [CollatzResearch.WordTrace]
  refine ⟨276864874214273941744894319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184576582809515961163262879 276864874214273941744894319)
  ·
    refine ⟨415297311321410912617341479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276864874214273941744894319 415297311321410912617341479)
    ·
      refine ⟨622945966982116368926012219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415297311321410912617341479 622945966982116368926012219)
      ·
        refine ⟨934418950473174553389018329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622945966982116368926012219 934418950473174553389018329)
        ·
          refine ⟨700814212854880915041763747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934418950473174553389018329 700814212854880915041763747)
          ·
            refine ⟨1051221319282321372562645621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700814212854880915041763747 1051221319282321372562645621)
            ·
              refine ⟨98551998682717628677748027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1051221319282321372562645621 98551998682717628677748027)
              ·
                refine ⟨147827998024076443016622041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98551998682717628677748027 147827998024076443016622041)
                ·
                  refine ⟨110870998518057332262466531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147827998024076443016622041 110870998518057332262466531)
                  ·
                    refine ⟨166306497777085998393699797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110870998518057332262466531 166306497777085998393699797)
                    ·
                      refine ⟨3897808541650453087352339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166306497777085998393699797 3897808541650453087352339)
                      ·
                        rfl

theorem cell23_7590955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_7590955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590955 prefixEnd_7590955 := by exact prefixLift 7590955
  have htrace : WordTrace (prefixWord ++ tailWord_7590955) baseStart_7590955 baseEnd_7590955 := by
    simpa [prefixWord, tailWord_7590955, baseEnd_7590955] using wordTrace_append hprefix tailTrace_7590955
  have hstable : (prefixWord ++ tailWord_7590955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590955).length < 2 ^ (prefixWord ++ tailWord_7590955).sum := by decide
  have hdescent : baseEnd_7590955 < baseStart_7590955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7590962 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_7590962 : Nat := 118140960795 + 7590962 * 2 ^ 59
def prefixEnd_7590962 : Nat := 4983230072969 + 3 ^ 40 * 7590962 * 2
def baseEnd_7590962 : Nat := 1299270712005011519988269

theorem tailTrace_7590962 : CollatzResearch.WordTrace tailWord_7590962 prefixEnd_7590962 1299270712005011519988269 := by
  unfold tailWord_7590962
  simp only [CollatzResearch.WordTrace]
  refine ⟨69216282381312145485099785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184576753016832387960266093 69216282381312145485099785)
  ·
    refine ⟨51912211785984109113824839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69216282381312145485099785 51912211785984109113824839)
    ·
      refine ⟨77868317678976163670737259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51912211785984109113824839 77868317678976163670737259)
      ·
        refine ⟨116802476518464245506105889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77868317678976163670737259 116802476518464245506105889)
        ·
          refine ⟨87601857388848184129579417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116802476518464245506105889 87601857388848184129579417)
          ·
            refine ⟨65701393041636138097184563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87601857388848184129579417 65701393041636138097184563)
            ·
              refine ⟨98552089562454207145776845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65701393041636138097184563 98552089562454207145776845)
              ·
                refine ⟨36957033585920327679666317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98552089562454207145776845 36957033585920327679666317)
                ·
                  refine ⟨13858887594720122879874869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36957033585920327679666317 13858887594720122879874869)
                  ·
                    refine ⟨1299270712005011519988269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13858887594720122879874869 1299270712005011519988269)
                    ·
                      rfl

theorem cell23_7590962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_7590962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7590962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7590962 prefixEnd_7590962 := by exact prefixLift 7590962
  have htrace : WordTrace (prefixWord ++ tailWord_7590962) baseStart_7590962 baseEnd_7590962 := by
    simpa [prefixWord, tailWord_7590962, baseEnd_7590962] using wordTrace_append hprefix tailTrace_7590962
  have hstable : (prefixWord ++ tailWord_7590962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7590962).length < 2 ^ (prefixWord ++ tailWord_7590962).sum := by decide
  have hdescent : baseEnd_7590962 < baseStart_7590962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7590962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591002 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3]
def baseStart_7591002 : Nat := 118140960795 + 7591002 * 2 ^ 59
def prefixEnd_7591002 : Nat := 4983230072969 + 3 ^ 40 * 7591002 * 2
def baseEnd_7591002 : Nat := 3897832675241214403464623

theorem tailTrace_7591002 : CollatzResearch.WordTrace tailWord_7591002 prefixEnd_7591002 3897832675241214403464623 := by
  unfold tailWord_7591002
  simp only [CollatzResearch.WordTrace]
  refine ⟨69216647111275917192963815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184577725630069112514570173 69216647111275917192963815)
  ·
    refine ⟨103824970666913875789445723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69216647111275917192963815 103824970666913875789445723)
    ·
      refine ⟨155737456000370813684168585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103824970666913875789445723 155737456000370813684168585)
      ·
        refine ⟨116803092000278110263126439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155737456000370813684168585 116803092000278110263126439)
        ·
          refine ⟨175204638000417165394689659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116803092000278110263126439 175204638000417165394689659)
          ·
            refine ⟨262806957000625748092034489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175204638000417165394689659 262806957000625748092034489)
            ·
              refine ⟨197105217750469311069025867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262806957000625748092034489 197105217750469311069025867)
              ·
                refine ⟨295657826625703966603538801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197105217750469311069025867 295657826625703966603538801)
                ·
                  refine ⟨221743369969277974952654101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295657826625703966603538801 221743369969277974952654101)
                  ·
                    refine ⟨10394220467309905075905661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 221743369969277974952654101 10394220467309905075905661)
                    ·
                      refine ⟨3897832675241214403464623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10394220467309905075905661 3897832675241214403464623)
                      ·
                        rfl

theorem cell23_7591002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_7591002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591002 prefixEnd_7591002 := by exact prefixLift 7591002
  have htrace : WordTrace (prefixWord ++ tailWord_7591002) baseStart_7591002 baseEnd_7591002 := by
    simpa [prefixWord, tailWord_7591002, baseEnd_7591002] using wordTrace_append hprefix tailTrace_7591002
  have hstable : (prefixWord ++ tailWord_7591002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591002).length < 2 ^ (prefixWord ++ tailWord_7591002).sum := by decide
  have hdescent : baseEnd_7591002 < baseStart_7591002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591009 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 2, 4]
def baseStart_7591009 : Nat := 118140960795 + 7591009 * 2 ^ 59
def prefixEnd_7591009 : Nat := 4983230072969 + 3 ^ 40 * 7591009 * 2
def baseEnd_7591009 : Nat := 1299278756535265292025697

theorem tailTrace_7591009 : CollatzResearch.WordTrace tailWord_7591009 prefixEnd_7591009 1299278756535265292025697 := by
  unfold tailWord_7591009
  simp only [CollatzResearch.WordTrace]
  refine ⟨276866843756078308967360081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184577895837385539311573387 276866843756078308967360081)
  ·
    refine ⟨207650132817058731725520061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276866843756078308967360081 207650132817058731725520061)
    ·
      refine ⟨77868799806397024397070023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207650132817058731725520061 77868799806397024397070023)
      ·
        refine ⟨116803199709595536595605035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77868799806397024397070023 116803199709595536595605035)
        ·
          refine ⟨175204799564393304893407553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116803199709595536595605035 175204799564393304893407553)
          ·
            refine ⟨131403599673294978670055665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175204799564393304893407553 131403599673294978670055665)
            ·
              refine ⟨98552699754971234002541749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131403599673294978670055665 98552699754971234002541749)
              ·
                refine ⟨9239315602028553187738289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98552699754971234002541749 9239315602028553187738289)
                ·
                  refine ⟨6929486701521414890803717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9239315602028553187738289 6929486701521414890803717)
                  ·
                    refine ⟨1299278756535265292025697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6929486701521414890803717 1299278756535265292025697)
                    ·
                      rfl

theorem cell23_7591009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_7591009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591009 prefixEnd_7591009 := by exact prefixLift 7591009
  have htrace : WordTrace (prefixWord ++ tailWord_7591009) baseStart_7591009 baseEnd_7591009 := by
    simpa [prefixWord, tailWord_7591009, baseEnd_7591009] using wordTrace_append hprefix tailTrace_7591009
  have hstable : (prefixWord ++ tailWord_7591009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591009).length < 2 ^ (prefixWord ++ tailWord_7591009).sum := by decide
  have hdescent : baseEnd_7591009 < baseStart_7591009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591070 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_7591070 : Nat := 118140960795 + 7591070 * 2 ^ 59
def prefixEnd_7591070 : Nat := 4983230072969 + 3 ^ 40 * 7591070 * 2
def baseEnd_7591070 : Nat := 3897867591925720137414311

theorem tailTrace_7591070 : CollatzResearch.WordTrace tailWord_7591070 prefixEnd_7591070 3897867591925720137414311 := by
  unfold tailWord_7591070
  simp only [CollatzResearch.WordTrace]
  refine ⟨34608633576107164548166333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184579379072571544256887109 34608633576107164548166333)
  ·
    refine ⟨12978237591040186705562375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34608633576107164548166333 12978237591040186705562375)
    ·
      refine ⟨19467356386560280058343563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12978237591040186705562375 19467356386560280058343563)
      ·
        refine ⟨29201034579840420087515345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19467356386560280058343563 29201034579840420087515345)
        ·
          refine ⟨21900775934880315065636509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29201034579840420087515345 21900775934880315065636509)
          ·
            refine ⟨8212790975580118149613691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21900775934880315065636509 8212790975580118149613691)
            ·
              refine ⟨12319186463370177224420537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8212790975580118149613691 12319186463370177224420537)
              ·
                refine ⟨9239389847527632918315403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12319186463370177224420537 9239389847527632918315403)
                ·
                  refine ⟨13859084771291449377473105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9239389847527632918315403 13859084771291449377473105)
                  ·
                    refine ⟨10394313578468587033104829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13859084771291449377473105 10394313578468587033104829)
                    ·
                      refine ⟨3897867591925720137414311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10394313578468587033104829 3897867591925720137414311)
                      ·
                        rfl

theorem cell23_7591070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_7591070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591070 prefixEnd_7591070 := by exact prefixLift 7591070
  have htrace : WordTrace (prefixWord ++ tailWord_7591070) baseStart_7591070 baseEnd_7591070 := by
    simpa [prefixWord, tailWord_7591070, baseEnd_7591070] using wordTrace_append hprefix tailTrace_7591070
  have hstable : (prefixWord ++ tailWord_7591070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591070).length < 2 ^ (prefixWord ++ tailWord_7591070).sum := by decide
  have hdescent : baseEnd_7591070 < baseStart_7591070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591146 : List Nat := [3, 1, 3, 1, 1, 3, 1, 5, 5]
def baseStart_7591146 : Nat := 118140960795 + 7591146 * 2 ^ 59
def prefixEnd_7591146 : Nat := 4983230072969 + 3 ^ 40 * 7591146 * 2
def baseEnd_7591146 : Nat := 433100735161717982229329

theorem tailTrace_7591146 : CollatzResearch.WordTrace tailWord_7591146 prefixEnd_7591146 433100735161717982229329 := by
  unfold tailWord_7591146
  simp only [CollatzResearch.WordTrace]
  refine ⟨69217960139145495341274323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184581227037721320910064861 69217960139145495341274323)
  ·
    refine ⟨103826940208718243011911485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69217960139145495341274323 103826940208718243011911485)
    ·
      refine ⟨38935102578269341129466807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103826940208718243011911485 38935102578269341129466807)
      ·
        refine ⟨58402653867404011694200211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38935102578269341129466807 58402653867404011694200211)
        ·
          refine ⟨87603980801106017541300317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58402653867404011694200211 87603980801106017541300317)
          ·
            refine ⟨32851492800414756577987619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87603980801106017541300317 32851492800414756577987619)
            ·
              refine ⟨49277239200622134866981429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32851492800414756577987619 49277239200622134866981429)
              ·
                refine ⟨4619741175058325143779509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49277239200622134866981429 4619741175058325143779509)
                ·
                  refine ⟨433100735161717982229329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4619741175058325143779509 433100735161717982229329)
                  ·
                    rfl

theorem cell23_7591146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_7591146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591146 prefixEnd_7591146 := by exact prefixLift 7591146
  have htrace : WordTrace (prefixWord ++ tailWord_7591146) baseStart_7591146 baseEnd_7591146 := by
    simpa [prefixWord, tailWord_7591146, baseEnd_7591146] using wordTrace_append hprefix tailTrace_7591146
  have hstable : (prefixWord ++ tailWord_7591146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591146).length < 2 ^ (prefixWord ++ tailWord_7591146).sum := by decide
  have hdescent : baseEnd_7591146 < baseStart_7591146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591179 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 4]
def baseStart_7591179 : Nat := 118140960795 + 7591179 * 2 ^ 59
def prefixEnd_7591179 : Nat := 4983230072969 + 3 ^ 40 * 7591179 * 2
def baseEnd_7591179 : Nat := 3897923561317060210951309

theorem tailTrace_7591179 : CollatzResearch.WordTrace tailWord_7591179 prefixEnd_7591179 3897923561317060210951309 := by
  unfold tailWord_7591179
  simp only [CollatzResearch.WordTrace]
  refine ⟨276873044165462428001048591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184582029443641618667365727 276873044165462428001048591)
  ·
    refine ⟨415309566248193642001572887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276873044165462428001048591 415309566248193642001572887)
    ·
      refine ⟨622964349372290463002359331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415309566248193642001572887 622964349372290463002359331)
      ·
        refine ⟨934446524058435694503538997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622964349372290463002359331 934446524058435694503538997)
        ·
          refine ⟨87604361630478346359706781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 934446524058435694503538997 87604361630478346359706781)
          ·
            refine ⟨32851635611429379884890043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87604361630478346359706781 32851635611429379884890043)
            ·
              refine ⟨49277453417144069827335065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32851635611429379884890043 49277453417144069827335065)
              ·
                refine ⟨36958090062858052370501299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49277453417144069827335065 36958090062858052370501299)
                ·
                  refine ⟨55437135094287078555751949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36958090062858052370501299 55437135094287078555751949)
                  ·
                    refine ⟨20788925660357654458406981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55437135094287078555751949 20788925660357654458406981)
                    ·
                      refine ⟨3897923561317060210951309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20788925660357654458406981 3897923561317060210951309)
                      ·
                        rfl

theorem cell23_7591179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 4].length) (baseStart_7591179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591179 prefixEnd_7591179 := by exact prefixLift 7591179
  have htrace : WordTrace (prefixWord ++ tailWord_7591179) baseStart_7591179 baseEnd_7591179 := by
    simpa [prefixWord, tailWord_7591179, baseEnd_7591179] using wordTrace_append hprefix tailTrace_7591179
  have hstable : (prefixWord ++ tailWord_7591179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591179).length < 2 ^ (prefixWord ++ tailWord_7591179).sum := by decide
  have hdescent : baseEnd_7591179 < baseStart_7591179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591196 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_7591196 : Nat := 118140960795 + 7591196 * 2 ^ 59
def prefixEnd_7591196 : Nat := 4983230072969 + 3 ^ 40 * 7591196 * 2
def baseEnd_7591196 : Nat := 3897932290488186644438731

theorem tailTrace_7591196 : CollatzResearch.WordTrace tailWord_7591196 prefixEnd_7591196 3897932290488186644438731 := by
  unfold tailWord_7591196
  simp only [CollatzResearch.WordTrace]
  refine ⟨138436832103200419952208721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184582442804267226602944961 138436832103200419952208721)
  ·
    refine ⟨103827624077400314964156541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138436832103200419952208721 103827624077400314964156541)
    ·
      refine ⟨38935359029025118111558703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103827624077400314964156541 38935359029025118111558703)
      ·
        refine ⟨58403038543537677167338055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38935359029025118111558703 58403038543537677167338055)
        ·
          refine ⟨87604557815306515751007083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58403038543537677167338055 87604557815306515751007083)
          ·
            refine ⟨131406836722959773626510625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87604557815306515751007083 131406836722959773626510625)
            ·
              refine ⟨98555127542219830219882969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131406836722959773626510625 98555127542219830219882969)
              ·
                refine ⟨73916345656664872664912227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98555127542219830219882969 73916345656664872664912227)
                ·
                  refine ⟨110874518484997308997368341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73916345656664872664912227 110874518484997308997368341)
                  ·
                    refine ⟨5197243053984248859251641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110874518484997308997368341 5197243053984248859251641)
                    ·
                      refine ⟨3897932290488186644438731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5197243053984248859251641 3897932290488186644438731)
                      ·
                        rfl

theorem cell23_7591196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_7591196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591196 prefixEnd_7591196 := by exact prefixLift 7591196
  have htrace : WordTrace (prefixWord ++ tailWord_7591196) baseStart_7591196 baseEnd_7591196 := by
    simpa [prefixWord, tailWord_7591196, baseEnd_7591196] using wordTrace_append hprefix tailTrace_7591196
  have hstable : (prefixWord ++ tailWord_7591196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591196).length < 2 ^ (prefixWord ++ tailWord_7591196).sum := by decide
  have hdescent : baseEnd_7591196 < baseStart_7591196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591213 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7591213 : Nat := 118140960795 + 7591213 * 2 ^ 59
def prefixEnd_7591213 : Nat := 4983230072969 + 3 ^ 40 * 7591213 * 2
def baseEnd_7591213 : Nat := 3897941019659313077926153

theorem tailTrace_7591213 : CollatzResearch.WordTrace tailWord_7591213 prefixEnd_7591213 3897941019659313077926153 := by
  unfold tailWord_7591213
  simp only [CollatzResearch.WordTrace]
  refine ⟨276874284247339251807786293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184582856164892834538524195 276874284247339251807786293)
  ·
    refine ⟨25956964148188054856979965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276874284247339251807786293 25956964148188054856979965)
    ·
      refine ⟨9733861555570520571367487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25956964148188054856979965 9733861555570520571367487)
      ·
        refine ⟨14600792333355780857051231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9733861555570520571367487 14600792333355780857051231)
        ·
          refine ⟨21901188500033671285576847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14600792333355780857051231 21901188500033671285576847)
          ·
            refine ⟨32851782750050506928365271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21901188500033671285576847 32851782750050506928365271)
            ·
              refine ⟨49277674125075760392547907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32851782750050506928365271 49277674125075760392547907)
              ·
                refine ⟨73916511187613640588821861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49277674125075760392547907 73916511187613640588821861)
                ·
                  refine ⟨13859345847677557610404099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73916511187613640588821861 13859345847677557610404099)
                  ·
                    refine ⟨20789018771516336415606149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13859345847677557610404099 20789018771516336415606149)
                    ·
                      refine ⟨3897941019659313077926153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20789018771516336415606149 3897941019659313077926153)
                      ·
                        rfl

theorem cell23_7591213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7591213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591213 prefixEnd_7591213 := by exact prefixLift 7591213
  have htrace : WordTrace (prefixWord ++ tailWord_7591213) baseStart_7591213 baseEnd_7591213 := by
    simpa [prefixWord, tailWord_7591213, baseEnd_7591213] using wordTrace_append hprefix tailTrace_7591213
  have hstable : (prefixWord ++ tailWord_7591213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591213).length < 2 ^ (prefixWord ++ tailWord_7591213).sum := by decide
  have hdescent : baseEnd_7591213 < baseStart_7591213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591216 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 3]
def baseStart_7591216 : Nat := 118140960795 + 7591216 * 2 ^ 59
def prefixEnd_7591216 : Nat := 4983230072969 + 3 ^ 40 * 7591216 * 2
def baseEnd_7591216 : Nat := 3897942560101276566188639

theorem tailTrace_7591216 : CollatzResearch.WordTrace tailWord_7591216 prefixEnd_7591216 3897942560101276566188639 := by
  unfold tailWord_7591216
  simp only [CollatzResearch.WordTrace]
  refine ⟨138437196833164191660072751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184582929110885588880097001 138437196833164191660072751)
  ·
    refine ⟨207655795249746287490109127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138437196833164191660072751 207655795249746287490109127)
    ·
      refine ⟨311483692874619431235163691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207655795249746287490109127 311483692874619431235163691)
      ·
        refine ⟨467225539311929146852745537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311483692874619431235163691 467225539311929146852745537)
        ·
          refine ⟨350419154483946860139559153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467225539311929146852745537 350419154483946860139559153)
          ·
            refine ⟨262814365862960145104669365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350419154483946860139559153 262814365862960145104669365)
            ·
              refine ⟨24638846799652513603562753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262814365862960145104669365 24638846799652513603562753)
              ·
                refine ⟨18479135099739385202672065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24638846799652513603562753 18479135099739385202672065)
                ·
                  refine ⟨13859351324804538902004049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18479135099739385202672065 13859351324804538902004049)
                  ·
                    refine ⟨10394513493603404176503037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13859351324804538902004049 10394513493603404176503037)
                    ·
                      refine ⟨3897942560101276566188639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10394513493603404176503037 3897942560101276566188639)
                      ·
                        rfl

theorem cell23_7591216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 3].length) (baseStart_7591216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591216 prefixEnd_7591216 := by exact prefixLift 7591216
  have htrace : WordTrace (prefixWord ++ tailWord_7591216) baseStart_7591216 baseEnd_7591216 := by
    simpa [prefixWord, tailWord_7591216, baseEnd_7591216] using wordTrace_append hprefix tailTrace_7591216
  have hstable : (prefixWord ++ tailWord_7591216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591216).length < 2 ^ (prefixWord ++ tailWord_7591216).sum := by decide
  have hdescent : baseEnd_7591216 < baseStart_7591216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591219 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 8]
def baseStart_7591219 : Nat := 118140960795 + 7591219 * 2 ^ 59
def prefixEnd_7591219 : Nat := 4983230072969 + 3 ^ 40 * 7591219 * 2
def baseEnd_7591219 : Nat := 433104900060360006050125

theorem tailTrace_7591219 : CollatzResearch.WordTrace tailWord_7591219 prefixEnd_7591219 433104900060360006050125 := by
  unfold tailWord_7591219
  simp only [CollatzResearch.WordTrace]
  refine ⟨276874503085317514832504711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184583002056878343221669807 276874503085317514832504711)
  ·
    refine ⟨415311754627976272248757067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276874503085317514832504711 415311754627976272248757067)
    ·
      refine ⟨622967631941964408373135601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415311754627976272248757067 622967631941964408373135601)
      ·
        refine ⟨467225723956473306279851701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622967631941964408373135601 467225723956473306279851701)
        ·
          refine ⟨43802411620919372463736097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 467225723956473306279851701 43802411620919372463736097)
          ·
            refine ⟨32851808715689529347802073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43802411620919372463736097 32851808715689529347802073)
            ·
              refine ⟨24638856536767147010851555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32851808715689529347802073 24638856536767147010851555)
              ·
                refine ⟨36958284805150720516277333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24638856536767147010851555 36958284805150720516277333)
                ·
                  refine ⟨433104900060360006050125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36958284805150720516277333 433104900060360006050125)
                  ·
                    rfl

theorem cell23_7591219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 8].length) (baseStart_7591219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591219 prefixEnd_7591219 := by exact prefixLift 7591219
  have htrace : WordTrace (prefixWord ++ tailWord_7591219) baseStart_7591219 baseEnd_7591219 := by
    simpa [prefixWord, tailWord_7591219, baseEnd_7591219] using wordTrace_append hprefix tailTrace_7591219
  have hstable : (prefixWord ++ tailWord_7591219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591219).length < 2 ^ (prefixWord ++ tailWord_7591219).sum := by decide
  have hdescent : baseEnd_7591219 < baseStart_7591219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591274 : List Nat := [3, 1, 3, 3, 2, 2, 2, 2, 1, 4]
def baseStart_7591274 : Nat := 118140960795 + 7591274 * 2 ^ 59
def prefixEnd_7591274 : Nat := 4983230072969 + 3 ^ 40 * 7591274 * 2
def baseEnd_7591274 : Nat := 1299324113993079113087791

theorem tailTrace_7591274 : CollatzResearch.WordTrace tailWord_7591274 prefixEnd_7591274 1299324113993079113087791 := by
  unfold tailWord_7591274
  simp only [CollatzResearch.WordTrace]
  refine ⟨69219127275029564806439219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184584339400078839483837917 69219127275029564806439219)
  ·
    refine ⟨103828690912544347209658829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69219127275029564806439219 103828690912544347209658829)
    ·
      refine ⟨38935759092204130203622061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103828690912544347209658829 38935759092204130203622061)
      ·
        refine ⟨14600909659576548826358273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38935759092204130203622061 14600909659576548826358273)
        ·
          refine ⟨10950682244682411619768705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14600909659576548826358273 10950682244682411619768705)
          ·
            refine ⟨8213011683511808714826529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10950682244682411619768705 8213011683511808714826529)
            ·
              refine ⟨6159758762633856536119897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8213011683511808714826529 6159758762633856536119897)
              ·
                refine ⟨4619819071975392402089923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6159758762633856536119897 4619819071975392402089923)
                ·
                  refine ⟨6929728607963088603134885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4619819071975392402089923 6929728607963088603134885)
                  ·
                    refine ⟨1299324113993079113087791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6929728607963088603134885 1299324113993079113087791)
                    ·
                      rfl

theorem cell23_7591274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_7591274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591274 prefixEnd_7591274 := by exact prefixLift 7591274
  have htrace : WordTrace (prefixWord ++ tailWord_7591274) baseStart_7591274 baseEnd_7591274 := by
    simpa [prefixWord, tailWord_7591274, baseEnd_7591274] using wordTrace_append hprefix tailTrace_7591274
  have hstable : (prefixWord ++ tailWord_7591274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591274).length < 2 ^ (prefixWord ++ tailWord_7591274).sum := by decide
  have hdescent : baseEnd_7591274 < baseStart_7591274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591279 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 3, 6]
def baseStart_7591279 : Nat := 118140960795 + 7591279 * 2 ^ 59
def prefixEnd_7591279 : Nat := 4983230072969 + 3 ^ 40 * 7591279 * 2
def baseEnd_7591279 : Nat := 1299324969794169939900283

theorem tailTrace_7591279 : CollatzResearch.WordTrace tailWord_7591279 prefixEnd_7591279 1299324969794169939900283 := by
  unfold tailWord_7591279
  simp only [CollatzResearch.WordTrace]
  refine ⟨276876691465100145079688891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184584460976733430053125927 276876691465100145079688891)
  ·
    refine ⟨415315037197650217619533337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276876691465100145079688891 415315037197650217619533337)
    ·
      refine ⟨311486277898237663214650003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415315037197650217619533337 311486277898237663214650003)
      ·
        refine ⟨467229416847356494821975005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311486277898237663214650003 467229416847356494821975005)
        ·
          refine ⟨175211031317758685558240627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467229416847356494821975005 175211031317758685558240627)
          ·
            refine ⟨262816546976638028337360941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175211031317758685558240627 262816546976638028337360941)
            ·
              refine ⟨98556205116239260626510353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262816546976638028337360941 98556205116239260626510353)
              ·
                refine ⟨73917153837179445469882765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98556205116239260626510353 73917153837179445469882765)
                ·
                  refine ⟨27718932688942292051206037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73917153837179445469882765 27718932688942292051206037)
                  ·
                    refine ⟨1299324969794169939900283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27718932688942292051206037 1299324969794169939900283)
                    ·
                      rfl

theorem cell23_7591279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_7591279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591279 prefixEnd_7591279 := by exact prefixLift 7591279
  have htrace : WordTrace (prefixWord ++ tailWord_7591279) baseStart_7591279 baseEnd_7591279 := by
    simpa [prefixWord, tailWord_7591279, baseEnd_7591279] using wordTrace_append hprefix tailTrace_7591279
  have hstable : (prefixWord ++ tailWord_7591279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591279).length < 2 ^ (prefixWord ++ tailWord_7591279).sum := by decide
  have hdescent : baseEnd_7591279 < baseStart_7591279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591280 : List Nat := [2, 1, 1, 1, 4, 2, 3, 4, 1, 1, 3]
def baseStart_7591280 : Nat := 118140960795 + 7591280 * 2 ^ 59
def prefixEnd_7591280 : Nat := 4983230072969 + 3 ^ 40 * 7591280 * 2
def baseEnd_7591280 : Nat := 3897975422863164315788345

theorem tailTrace_7591280 : CollatzResearch.WordTrace tailWord_7591280 prefixEnd_7591280 3897975422863164315788345 := by
  unfold tailWord_7591280
  simp only [CollatzResearch.WordTrace]
  refine ⟨138438363969048261125237647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184584485292064348166983529 138438363969048261125237647)
  ·
    refine ⟨207657545953572391687856471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138438363969048261125237647 207657545953572391687856471)
    ·
      refine ⟨311486318930358587531784707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207657545953572391687856471 311486318930358587531784707)
      ·
        refine ⟨467229478395537881297677061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311486318930358587531784707 467229478395537881297677061)
        ·
          refine ⟨87605527199163352743314449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 467229478395537881297677061 87605527199163352743314449)
          ·
            refine ⟨65704145399372514557485837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87605527199163352743314449 65704145399372514557485837)
            ·
              refine ⟨24639054524764692959057189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65704145399372514557485837 24639054524764692959057189)
              ·
                refine ⟨4619822723393379929823223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24639054524764692959057189 4619822723393379929823223)
                ·
                  refine ⟨6929734085090069894734835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4619822723393379929823223 6929734085090069894734835)
                  ·
                    refine ⟨10394601127635104842102253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6929734085090069894734835 10394601127635104842102253)
                    ·
                      refine ⟨3897975422863164315788345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10394601127635104842102253 3897975422863164315788345)
                      ·
                        rfl

theorem cell23_7591280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 1, 1, 3].length) (baseStart_7591280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591280 prefixEnd_7591280 := by exact prefixLift 7591280
  have htrace : WordTrace (prefixWord ++ tailWord_7591280) baseStart_7591280 baseEnd_7591280 := by
    simpa [prefixWord, tailWord_7591280, baseEnd_7591280] using wordTrace_append hprefix tailTrace_7591280
  have hstable : (prefixWord ++ tailWord_7591280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591280).length < 2 ^ (prefixWord ++ tailWord_7591280).sum := by decide
  have hdescent : baseEnd_7591280 < baseStart_7591280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591320 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 1, 1, 4]
def baseStart_7591320 : Nat := 118140960795 + 7591320 * 2 ^ 59
def prefixEnd_7591320 : Nat := 4983230072969 + 3 ^ 40 * 7591320 * 2
def baseEnd_7591320 : Nat := 3897995962089344159288161

theorem tailTrace_7591320 : CollatzResearch.WordTrace tailWord_7591320 prefixEnd_7591320 3897995962089344159288161 := by
  unfold tailWord_7591320
  simp only [CollatzResearch.WordTrace]
  refine ⟨138439093428975804540965707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184585457905301072721287609 138439093428975804540965707)
  ·
    refine ⟨207658640143463706811448561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138439093428975804540965707 207658640143463706811448561)
    ·
      refine ⟨155743980107597780108586421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207658640143463706811448561 155743980107597780108586421)
      ·
        refine ⟨14600998135087291885179977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155743980107597780108586421 14600998135087291885179977)
        ·
          refine ⟨10950748601315468913884983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14600998135087291885179977 10950748601315468913884983)
          ·
            refine ⟨16426122901973203370827475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10950748601315468913884983 16426122901973203370827475)
            ·
              refine ⟨24639184352959805056241213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16426122901973203370827475 24639184352959805056241213)
              ·
                refine ⟨9239694132359926896090455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24639184352959805056241213 9239694132359926896090455)
                ·
                  refine ⟨13859541198539890344135683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9239694132359926896090455 13859541198539890344135683)
                  ·
                    refine ⟨20789311797809835516203525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13859541198539890344135683 20789311797809835516203525)
                    ·
                      refine ⟨3897995962089344159288161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20789311797809835516203525 3897995962089344159288161)
                      ·
                        rfl

theorem cell23_7591320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_7591320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591320 prefixEnd_7591320 := by exact prefixLift 7591320
  have htrace : WordTrace (prefixWord ++ tailWord_7591320) baseStart_7591320 baseEnd_7591320 := by
    simpa [prefixWord, tailWord_7591320, baseEnd_7591320] using wordTrace_append hprefix tailTrace_7591320
  have hstable : (prefixWord ++ tailWord_7591320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591320).length < 2 ^ (prefixWord ++ tailWord_7591320).sum := by decide
  have hdescent : baseEnd_7591320 < baseStart_7591320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591330 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_7591330 : Nat := 118140960795 + 7591330 * 2 ^ 59
def prefixEnd_7591330 : Nat := 4983230072969 + 3 ^ 40 * 7591330 * 2
def baseEnd_7591330 : Nat := 1299333698965296373387705

theorem tailTrace_7591330 : CollatzResearch.WordTrace tailWord_7591330 prefixEnd_7591330 1299333698965296373387705 := by
  unfold tailWord_7591330
  simp only [CollatzResearch.WordTrace]
  refine ⟨69219637896978845197448861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184585701058610253859863629 69219637896978845197448861)
  ·
    refine ⟨25957364211367066949043323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69219637896978845197448861 25957364211367066949043323)
    ·
      refine ⟨38936046317050600423564985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25957364211367066949043323 38936046317050600423564985)
      ·
        refine ⟨29202034737787950317673739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38936046317050600423564985 29202034737787950317673739)
        ·
          refine ⟨43803052106681925476510609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29202034737787950317673739 43803052106681925476510609)
          ·
            refine ⟨32852289080011444107382957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43803052106681925476510609 32852289080011444107382957)
            ·
              refine ⟨12319608405004291540268609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32852289080011444107382957 12319608405004291540268609)
              ·
                refine ⟨9239706303753218655201457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12319608405004291540268609 9239706303753218655201457)
                ·
                  refine ⟨6929779727814913991401093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9239706303753218655201457 6929779727814913991401093)
                  ·
                    refine ⟨1299333698965296373387705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6929779727814913991401093 1299333698965296373387705)
                    ·
                      rfl

theorem cell23_7591330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_7591330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591330 prefixEnd_7591330 := by exact prefixLift 7591330
  have htrace : WordTrace (prefixWord ++ tailWord_7591330) baseStart_7591330 baseEnd_7591330 := by
    simpa [prefixWord, tailWord_7591330, baseEnd_7591330] using wordTrace_append hprefix tailTrace_7591330
  have hstable : (prefixWord ++ tailWord_7591330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591330).length < 2 ^ (prefixWord ++ tailWord_7591330).sum := by decide
  have hdescent : baseEnd_7591330 < baseStart_7591330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591339 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 6, 7]
def baseStart_7591339 : Nat := 118140960795 + 7591339 * 2 ^ 59
def prefixEnd_7591339 : Nat := 4983230072969 + 3 ^ 40 * 7591339 * 2
def baseEnd_7591339 : Nat := 1299335239407259861650191

theorem tailTrace_7591339 : CollatzResearch.WordTrace tailWord_7591339 prefixEnd_7591339 1299335239407259861650191 := by
  unfold tailWord_7591339
  simp only [CollatzResearch.WordTrace]
  refine ⟨276878879844882775326873071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184585919896588516884582047 276878879844882775326873071)
  ·
    refine ⟨415318319767324162990309607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276878879844882775326873071 415318319767324162990309607)
    ·
      refine ⟨622977479650986244485464411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415318319767324162990309607 622977479650986244485464411)
      ·
        refine ⟨934466219476479366728196617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622977479650986244485464411 934466219476479366728196617)
        ·
          refine ⟨700849664607359525046147463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934466219476479366728196617 700849664607359525046147463)
          ·
            refine ⟨1051274496911039287569221195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700849664607359525046147463 1051274496911039287569221195)
            ·
              refine ⟨1576911745366558931353831793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051274496911039287569221195 1576911745366558931353831793)
              ·
                refine ⟨1182683809024919198515373845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576911745366558931353831793 1182683809024919198515373845)
                ·
                  refine ⟨55438303548043087430408149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1182683809024919198515373845 55438303548043087430408149)
                  ·
                    refine ⟨1299335239407259861650191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55438303548043087430408149 1299335239407259861650191)
                    ·
                      rfl

theorem cell23_7591339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 7].length) (baseStart_7591339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591339 prefixEnd_7591339 := by exact prefixLift 7591339
  have htrace : WordTrace (prefixWord ++ tailWord_7591339) baseStart_7591339 baseEnd_7591339 := by
    simpa [prefixWord, tailWord_7591339, baseEnd_7591339] using wordTrace_append hprefix tailTrace_7591339
  have hstable : (prefixWord ++ tailWord_7591339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591339).length < 2 ^ (prefixWord ++ tailWord_7591339).sum := by decide
  have hdescent : baseEnd_7591339 < baseStart_7591339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591363 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 3, 3, 2]
def baseStart_7591363 : Nat := 118140960795 + 7591363 * 2 ^ 59
def prefixEnd_7591363 : Nat := 4983230072969 + 3 ^ 40 * 7591363 * 2
def baseEnd_7591363 : Nat := 3898018041757487491050463

theorem tailTrace_7591363 : CollatzResearch.WordTrace tailWord_7591363 prefixEnd_7591363 3898018041757487491050463 := by
  unfold tailWord_7591363
  simp only [CollatzResearch.WordTrace]
  refine ⟨276879755196795827425746743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184586503464530551617164495 276879755196795827425746743)
  ·
    refine ⟨415319632795193741138620115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276879755196795827425746743 415319632795193741138620115)
    ·
      refine ⟨622979449192790611707930173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415319632795193741138620115 622979449192790611707930173)
      ·
        refine ⟨233617293447296479390473815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 622979449192790611707930173 233617293447296479390473815)
        ·
          refine ⟨350425940170944719085710723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233617293447296479390473815 350425940170944719085710723)
          ·
            refine ⟨525638910256417078628566085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350425940170944719085710723 525638910256417078628566085)
            ·
              refine ⟨98557295673078202242856141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 525638910256417078628566085 98557295673078202242856141)
              ·
                refine ⟨36958985877404325841071053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98557295673078202242856141 36958985877404325841071053)
                ·
                  refine ⟨13859619704026622190401645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36958985877404325841071053 13859619704026622190401645)
                  ·
                    refine ⟨5197357389009983321400617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13859619704026622190401645 5197357389009983321400617)
                    ·
                      refine ⟨3898018041757487491050463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5197357389009983321400617 3898018041757487491050463)
                      ·
                        rfl

theorem cell23_7591363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 3, 2].length) (baseStart_7591363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591363 prefixEnd_7591363 := by exact prefixLift 7591363
  have htrace : WordTrace (prefixWord ++ tailWord_7591363) baseStart_7591363 baseEnd_7591363 := by
    simpa [prefixWord, tailWord_7591363, baseEnd_7591363] using wordTrace_append hprefix tailTrace_7591363
  have hstable : (prefixWord ++ tailWord_7591363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591363).length < 2 ^ (prefixWord ++ tailWord_7591363).sum := by decide
  have hdescent : baseEnd_7591363 < baseStart_7591363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591414 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_7591414 : Nat := 118140960795 + 7591414 * 2 ^ 59
def prefixEnd_7591414 : Nat := 4983230072969 + 3 ^ 40 * 7591414 * 2
def baseEnd_7591414 : Nat := 3898044229270866791512729

theorem tailTrace_7591414 : CollatzResearch.WordTrace tailWord_7591414 prefixEnd_7591414 3898044229270866791512729 := by
  unfold tailWord_7591414
  simp only [CollatzResearch.WordTrace]
  refine ⟨17305100957475691445990831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184587743546407375423902197 17305100957475691445990831)
  ·
    refine ⟨25957651436213537168986247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17305100957475691445990831 25957651436213537168986247)
    ·
      refine ⟨38936477154320305753479371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25957651436213537168986247 38936477154320305753479371)
      ·
        refine ⟨58404715731480458630219057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38936477154320305753479371 58404715731480458630219057)
        ·
          refine ⟨43803536798610343972664293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58404715731480458630219057 43803536798610343972664293)
          ·
            refine ⟨8213163149739439494874555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43803536798610343972664293 8213163149739439494874555)
            ·
              refine ⟨12319744724609159242311833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8213163149739439494874555 12319744724609159242311833)
              ·
                refine ⟨9239808543456869431733875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12319744724609159242311833 9239808543456869431733875)
                ·
                  refine ⟨13859712815185304147600813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9239808543456869431733875 13859712815185304147600813)
                  ·
                    refine ⟨5197392305694489055350305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13859712815185304147600813 5197392305694489055350305)
                    ·
                      refine ⟨3898044229270866791512729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5197392305694489055350305 3898044229270866791512729)
                      ·
                        rfl

theorem cell23_7591414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_7591414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591414 prefixEnd_7591414 := by exact prefixLift 7591414
  have htrace : WordTrace (prefixWord ++ tailWord_7591414) baseStart_7591414 baseEnd_7591414 := by
    simpa [prefixWord, tailWord_7591414, baseEnd_7591414] using wordTrace_append hprefix tailTrace_7591414
  have hstable : (prefixWord ++ tailWord_7591414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591414).length < 2 ^ (prefixWord ++ tailWord_7591414).sum := by decide
  have hdescent : baseEnd_7591414 < baseStart_7591414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591433 : List Nat := [1, 2, 1, 1, 3, 1, 4, 5, 5]
def baseStart_7591433 : Nat := 118140960795 + 7591433 * 2 ^ 59
def prefixEnd_7591433 : Nat := 4983230072969 + 3 ^ 40 * 7591433 * 2
def baseEnd_7591433 : Nat := 433117109489255801908349

theorem tailTrace_7591433 : CollatzResearch.WordTrace tailWord_7591433 prefixEnd_7591433 433117109489255801908349 := by
  unfold tailWord_7591433
  simp only [CollatzResearch.WordTrace]
  refine ⟨276882308306542229380794953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184588205537694819587196635 276882308306542229380794953)
  ·
    refine ⟨207661731229906672035596215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276882308306542229380794953 207661731229906672035596215)
    ·
      refine ⟨311492596844860008053394323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207661731229906672035596215 311492596844860008053394323)
      ·
        refine ⟨467238895267290012080091485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311492596844860008053394323 467238895267290012080091485)
        ·
          refine ⟨175214585725233754530034307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467238895267290012080091485 175214585725233754530034307)
          ·
            refine ⟨262821878587850631795051461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175214585725233754530034307 262821878587850631795051461)
            ·
              refine ⟨49279102235221993461572149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262821878587850631795051461 49279102235221993461572149)
              ·
                refine ⟨4619915834552061887022389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49279102235221993461572149 4619915834552061887022389)
                ·
                  refine ⟨433117109489255801908349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4619915834552061887022389 433117109489255801908349)
                  ·
                    rfl

theorem cell23_7591433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 5].length) (baseStart_7591433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591433 prefixEnd_7591433 := by exact prefixLift 7591433
  have htrace : WordTrace (prefixWord ++ tailWord_7591433) baseStart_7591433 baseEnd_7591433 := by
    simpa [prefixWord, tailWord_7591433, baseEnd_7591433] using wordTrace_append hprefix tailTrace_7591433
  have hstable : (prefixWord ++ tailWord_7591433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591433).length < 2 ^ (prefixWord ++ tailWord_7591433).sum := by decide
  have hdescent : baseEnd_7591433 < baseStart_7591433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591454 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_7591454 : Nat := 118140960795 + 7591454 * 2 ^ 59
def prefixEnd_7591454 : Nat := 4983230072969 + 3 ^ 40 * 7591454 * 2
def baseEnd_7591454 : Nat := 1299354922832348878337515

theorem tailTrace_7591454 : CollatzResearch.WordTrace tailWord_7591454 prefixEnd_7591454 1299354922832348878337515 := by
  unfold tailWord_7591454
  simp only [CollatzResearch.WordTrace]
  refine ⟨34610384279933268745913677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184588716159644099978206277 34610384279933268745913677)
  ·
    refine ⟨12978894104974975779717629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34610384279933268745913677 12978894104974975779717629)
    ·
      refine ⟨4867085289365615917394111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12978894104974975779717629 4867085289365615917394111)
      ·
        refine ⟨7300627934048423876091167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867085289365615917394111 7300627934048423876091167)
        ·
          refine ⟨10950941901072635814136751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7300627934048423876091167 10950941901072635814136751)
          ·
            refine ⟨16426412851608953721205127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10950941901072635814136751 16426412851608953721205127)
            ·
              refine ⟨24639619277413430581807691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16426412851608953721205127 24639619277413430581807691)
              ·
                refine ⟨36959428916120145872711537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24639619277413430581807691 36959428916120145872711537)
                ·
                  refine ⟨27719571687090109404533653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36959428916120145872711537 27719571687090109404533653)
                  ·
                    refine ⟨1299354922832348878337515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27719571687090109404533653 1299354922832348878337515)
                    ·
                      rfl

theorem cell23_7591454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_7591454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591454 prefixEnd_7591454 := by exact prefixLift 7591454
  have htrace : WordTrace (prefixWord ++ tailWord_7591454) baseStart_7591454 baseEnd_7591454 := by
    simpa [prefixWord, tailWord_7591454, baseEnd_7591454] using wordTrace_append hprefix tailTrace_7591454
  have hstable : (prefixWord ++ tailWord_7591454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591454).length < 2 ^ (prefixWord ++ tailWord_7591454).sum := by decide
  have hdescent : baseEnd_7591454 < baseStart_7591454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591480 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 2, 5]
def baseStart_7591480 : Nat := 118140960795 + 7591480 * 2 ^ 59
def prefixEnd_7591480 : Nat := 4983230072969 + 3 ^ 40 * 7591480 * 2
def baseEnd_7591480 : Nat := 1299359372998021177762475

theorem tailTrace_7591480 : CollatzResearch.WordTrace tailWord_7591480 prefixEnd_7591480 1299359372998021177762475 := by
  unfold tailWord_7591480
  simp only [CollatzResearch.WordTrace]
  refine ⟨138442011268685978203877947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184589348358247970938503929 138442011268685978203877947)
  ·
    refine ⟨207663016903028967305816921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138442011268685978203877947 207663016903028967305816921)
    ·
      refine ⟨155747262677271725479362691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207663016903028967305816921 155747262677271725479362691)
      ·
        refine ⟨233620894015907588219044037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155747262677271725479362691 233620894015907588219044037)
        ·
          refine ⟨43803917627982672791070757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233620894015907588219044037 43803917627982672791070757)
          ·
            refine ⟨8213234555246751148325767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43803917627982672791070757 8213234555246751148325767)
            ·
              refine ⟨12319851832870126722488651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8213234555246751148325767 12319851832870126722488651)
              ·
                refine ⟨18479777749305190083732977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12319851832870126722488651 18479777749305190083732977)
                ·
                  refine ⟨13859833311978892562799733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18479777749305190083732977 13859833311978892562799733)
                  ·
                    refine ⟨1299359372998021177762475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13859833311978892562799733 1299359372998021177762475)
                    ·
                      rfl

theorem cell23_7591480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_7591480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591480 prefixEnd_7591480 := by exact prefixLift 7591480
  have htrace : WordTrace (prefixWord ++ tailWord_7591480) baseStart_7591480 baseEnd_7591480 := by
    simpa [prefixWord, tailWord_7591480, baseEnd_7591480] using wordTrace_append hprefix tailTrace_7591480
  have hstable : (prefixWord ++ tailWord_7591480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591480).length < 2 ^ (prefixWord ++ tailWord_7591480).sum := by decide
  have hdescent : baseEnd_7591480 < baseStart_7591480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591493 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 5, 4]
def baseStart_7591493 : Nat := 118140960795 + 7591493 * 2 ^ 59
def prefixEnd_7591493 : Nat := 4983230072969 + 3 ^ 40 * 7591493 * 2
def baseEnd_7591493 : Nat := 1299361598080857327474955

theorem tailTrace_7591493 : CollatzResearch.WordTrace tailWord_7591493 prefixEnd_7591493 1299361598080857327474955 := by
  unfold tailWord_7591493
  simp only [CollatzResearch.WordTrace]
  refine ⟨276884496686324859627979133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184589664457549906418652755 276884496686324859627979133)
  ·
    refine ⟨103831686257371822360492175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276884496686324859627979133 103831686257371822360492175)
    ·
      refine ⟨155747529386057733540738263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103831686257371822360492175 155747529386057733540738263)
      ·
        refine ⟨233621294079086600311107395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155747529386057733540738263 233621294079086600311107395)
        ·
          refine ⟨350431941118629900466661093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233621294079086600311107395 350431941118629900466661093)
          ·
            refine ⟨65705988959743106337498955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350431941118629900466661093 65705988959743106337498955)
            ·
              refine ⟨98558983439614659506248433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65705988959743106337498955 98558983439614659506248433)
              ·
                refine ⟨73919237579710994629686325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98558983439614659506248433 73919237579710994629686325)
                ·
                  refine ⟨6929928523097905746533093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73919237579710994629686325 6929928523097905746533093)
                  ·
                    refine ⟨1299361598080857327474955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6929928523097905746533093 1299361598080857327474955)
                    ·
                      rfl

theorem cell23_7591493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_7591493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591493 prefixEnd_7591493 := by exact prefixLift 7591493
  have htrace : WordTrace (prefixWord ++ tailWord_7591493) baseStart_7591493 baseEnd_7591493 := by
    simpa [prefixWord, tailWord_7591493, baseEnd_7591493] using wordTrace_append hprefix tailTrace_7591493
  have hstable : (prefixWord ++ tailWord_7591493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591493).length < 2 ^ (prefixWord ++ tailWord_7591493).sum := by decide
  have hdescent : baseEnd_7591493 < baseStart_7591493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591500 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 2, 4, 2]
def baseStart_7591500 : Nat := 118140960795 + 7591500 * 2 ^ 59
def prefixEnd_7591500 : Nat := 4983230072969 + 3 ^ 40 * 7591500 * 2
def baseEnd_7591500 : Nat := 3898088388607153455037333

theorem tailTrace_7591500 : CollatzResearch.WordTrace tailWord_7591500 prefixEnd_7591500 3898088388607153455037333 := by
  unfold tailWord_7591500
  simp only [CollatzResearch.WordTrace]
  refine ⟨138442375998649749911741977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184589834664866333215655969 138442375998649749911741977)
  ·
    refine ⟨103831781998987312433806483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138442375998649749911741977 103831781998987312433806483)
    ·
      refine ⟨155747672998480968650709725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103831781998987312433806483 155747672998480968650709725)
      ·
        refine ⟨58405377374430363244016147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155747672998480968650709725 58405377374430363244016147)
        ·
          refine ⟨87608066061645544866024221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58405377374430363244016147 87608066061645544866024221)
          ·
            refine ⟨32853024773117079324759083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87608066061645544866024221 32853024773117079324759083)
            ·
              refine ⟨49279537159675618987138625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32853024773117079324759083 49279537159675618987138625)
              ·
                refine ⟨36959652869756714240353969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49279537159675618987138625 36959652869756714240353969)
                ·
                  refine ⟨27719739652317535680265477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36959652869756714240353969 27719739652317535680265477)
                  ·
                    refine ⟨5197451184809537940049777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27719739652317535680265477 5197451184809537940049777)
                    ·
                      refine ⟨3898088388607153455037333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5197451184809537940049777 3898088388607153455037333)
                      ·
                        rfl

theorem cell23_7591500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_7591500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591500 prefixEnd_7591500 := by exact prefixLift 7591500
  have htrace : WordTrace (prefixWord ++ tailWord_7591500) baseStart_7591500 baseEnd_7591500 := by
    simpa [prefixWord, tailWord_7591500, baseEnd_7591500] using wordTrace_append hprefix tailTrace_7591500
  have hstable : (prefixWord ++ tailWord_7591500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591500).length < 2 ^ (prefixWord ++ tailWord_7591500).sum := by decide
  have hdescent : baseEnd_7591500 < baseStart_7591500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591503 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 3]
def baseStart_7591503 : Nat := 118140960795 + 7591503 * 2 ^ 59
def prefixEnd_7591503 : Nat := 4983230072969 + 3 ^ 40 * 7591503 * 2
def baseEnd_7591503 : Nat := 3898089929049116943299819

theorem tailTrace_7591503 : CollatzResearch.WordTrace tailWord_7591503 prefixEnd_7591503 3898089929049116943299819 := by
  unfold tailWord_7591503
  simp only [CollatzResearch.WordTrace]
  refine ⟨276884861416288631335843163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184589907610859087557228775 276884861416288631335843163)
  ·
    refine ⟨415327292124432947003764745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276884861416288631335843163 415327292124432947003764745)
    ·
      refine ⟨311495469093324710252823559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415327292124432947003764745 311495469093324710252823559)
      ·
        refine ⟨467243203639987065379235339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311495469093324710252823559 467243203639987065379235339)
        ·
          refine ⟨700864805459980598068853009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467243203639987065379235339 700864805459980598068853009)
          ·
            refine ⟨525648604094985448551639757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700864805459980598068853009 525648604094985448551639757)
            ·
              refine ⟨197118226535619543206864909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 525648604094985448551639757 197118226535619543206864909)
              ·
                refine ⟨73919334950857328702574341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197118226535619543206864909 73919334950857328702574341)
                ·
                  refine ⟨13859875303285749131732689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73919334950857328702574341 13859875303285749131732689)
                  ·
                    refine ⟨10394906477464311848799517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13859875303285749131732689 10394906477464311848799517)
                    ·
                      refine ⟨3898089929049116943299819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10394906477464311848799517 3898089929049116943299819)
                      ·
                        rfl

theorem cell23_7591503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 3].length) (baseStart_7591503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591503 prefixEnd_7591503 := by exact prefixLift 7591503
  have htrace : WordTrace (prefixWord ++ tailWord_7591503) baseStart_7591503 baseEnd_7591503 := by
    simpa [prefixWord, tailWord_7591503, baseEnd_7591503] using wordTrace_append hprefix tailTrace_7591503
  have hstable : (prefixWord ++ tailWord_7591503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591503).length < 2 ^ (prefixWord ++ tailWord_7591503).sum := by decide
  have hdescent : baseEnd_7591503 < baseStart_7591503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591610 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5]
def baseStart_7591610 : Nat := 118140960795 + 7591610 * 2 ^ 59
def prefixEnd_7591610 : Nat := 4983230072969 + 3 ^ 40 * 7591610 * 2
def baseEnd_7591610 : Nat := 3898144871479148024661827

theorem tailTrace_7591610 : CollatzResearch.WordTrace tailWord_7591610 prefixEnd_7591610 3898144871479148024661827 := by
  unfold tailWord_7591610
  simp only [CollatzResearch.WordTrace]
  refine ⟨69222191006725247152497071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184592509351267325739992189 69222191006725247152497071)
  ·
    refine ⟨103833286510087870728745607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69222191006725247152497071 103833286510087870728745607)
    ·
      refine ⟨155749929765131806093118411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103833286510087870728745607 155749929765131806093118411)
      ·
        refine ⟨233624894647697709139677617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155749929765131806093118411 233624894647697709139677617)
        ·
          refine ⟨175218670985773281854758213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233624894647697709139677617 175218670985773281854758213)
          ·
            refine ⟨32853500809832490347767165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175218670985773281854758213 32853500809832490347767165)
            ·
              refine ⟨12320062803687183880412687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32853500809832490347767165 12320062803687183880412687)
              ·
                refine ⟨18480094205530775820619031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12320062803687183880412687 18480094205530775820619031)
                ·
                  refine ⟨27720141308296163730928547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18480094205530775820619031 27720141308296163730928547)
                  ·
                    refine ⟨41580211962444245596392821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27720141308296163730928547 41580211962444245596392821)
                    ·
                      refine ⟨3898144871479148024661827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41580211962444245596392821 3898144871479148024661827)
                      ·
                        rfl

theorem cell23_7591610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_7591610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591610 prefixEnd_7591610 := by exact prefixLift 7591610
  have htrace : WordTrace (prefixWord ++ tailWord_7591610) baseStart_7591610 baseEnd_7591610 := by
    simpa [prefixWord, tailWord_7591610, baseEnd_7591610] using wordTrace_append hprefix tailTrace_7591610
  have hstable : (prefixWord ++ tailWord_7591610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591610).length < 2 ^ (prefixWord ++ tailWord_7591610).sum := by decide
  have hdescent : baseEnd_7591610 < baseStart_7591610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591620 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_7591620 : Nat := 118140960795 + 7591620 * 2 ^ 59
def prefixEnd_7591620 : Nat := 4983230072969 + 3 ^ 40 * 7591620 * 2
def baseEnd_7591620 : Nat := 3898150006285692985536781

theorem tailTrace_7591620 : CollatzResearch.WordTrace tailWord_7591620 prefixEnd_7591620 3898150006285692985536781 := by
  unfold tailWord_7591620
  simp only [CollatzResearch.WordTrace]
  refine ⟨138444564378432380158926157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184592752504576506878568209 138444564378432380158926157)
  ·
    refine ⟨51916711641912142559597309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138444564378432380158926157 51916711641912142559597309)
    ·
      refine ⟨19468766865717053459848991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51916711641912142559597309 19468766865717053459848991)
      ·
        refine ⟨29203150298575580189773487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19468766865717053459848991 29203150298575580189773487)
        ·
          refine ⟨43804725447863370284660231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29203150298575580189773487 43804725447863370284660231)
          ·
            refine ⟨65707088171795055426990347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43804725447863370284660231 65707088171795055426990347)
            ·
              refine ⟨98560632257692583140485521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65707088171795055426990347 98560632257692583140485521)
              ·
                refine ⟨73920474193269437355364141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98560632257692583140485521 73920474193269437355364141)
                ·
                  refine ⟨27720177822476039008261553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73920474193269437355364141 27720177822476039008261553)
                  ·
                    refine ⟨20790133366857029256196165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27720177822476039008261553 20790133366857029256196165)
                    ·
                      refine ⟨3898150006285692985536781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20790133366857029256196165 3898150006285692985536781)
                      ·
                        rfl

theorem cell23_7591620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_7591620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591620 prefixEnd_7591620 := by exact prefixLift 7591620
  have htrace : WordTrace (prefixWord ++ tailWord_7591620) baseStart_7591620 baseEnd_7591620 := by
    simpa [prefixWord, tailWord_7591620, baseEnd_7591620] using wordTrace_append hprefix tailTrace_7591620
  have hstable : (prefixWord ++ tailWord_7591620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591620).length < 2 ^ (prefixWord ++ tailWord_7591620).sum := by decide
  have hdescent : baseEnd_7591620 < baseStart_7591620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591661 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_7591661 : Nat := 118140960795 + 7591661 * 2 ^ 59
def prefixEnd_7591661 : Nat := 4983230072969 + 3 ^ 40 * 7591661 * 2
def baseEnd_7591661 : Nat := 3898171058992527325124093

theorem tailTrace_7591661 : CollatzResearch.WordTrace tailWord_7591661 prefixEnd_7591661 3898171058992527325124093 := by
  unfold tailWord_7591661
  simp only [CollatzResearch.WordTrace]
  refine ⟨276890624149716224320094837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184593749433144149546729891 276890624149716224320094837)
  ·
    refine ⟨25958496014035896030008891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276890624149716224320094837 25958496014035896030008891)
    ·
      refine ⟨38937744021053844045013337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25958496014035896030008891 38937744021053844045013337)
      ·
        refine ⟨29203308015790383033760003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38937744021053844045013337 29203308015790383033760003)
        ·
          refine ⟨43804962023685574550640005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29203308015790383033760003 43804962023685574550640005)
          ·
            refine ⟨8213430379441045228245001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43804962023685574550640005 8213430379441045228245001)
            ·
              refine ⟨6160072784580783921183751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8213430379441045228245001 6160072784580783921183751)
              ·
                refine ⟨9240109176871175881775627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6160072784580783921183751 9240109176871175881775627)
                ·
                  refine ⟨13860163765306763822663441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9240109176871175881775627 13860163765306763822663441)
                  ·
                    refine ⟨10395122823980072866997581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13860163765306763822663441 10395122823980072866997581)
                    ·
                      refine ⟨3898171058992527325124093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10395122823980072866997581 3898171058992527325124093)
                      ·
                        rfl

theorem cell23_7591661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_7591661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591661 prefixEnd_7591661 := by exact prefixLift 7591661
  have htrace : WordTrace (prefixWord ++ tailWord_7591661) baseStart_7591661 baseEnd_7591661 := by
    simpa [prefixWord, tailWord_7591661, baseEnd_7591661] using wordTrace_append hprefix tailTrace_7591661
  have hstable : (prefixWord ++ tailWord_7591661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591661).length < 2 ^ (prefixWord ++ tailWord_7591661).sum := by decide
  have hdescent : baseEnd_7591661 < baseStart_7591661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591668 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_7591668 : Nat := 118140960795 + 7591668 * 2 ^ 59
def prefixEnd_7591668 : Nat := 4983230072969 + 3 ^ 40 * 7591668 * 2
def baseEnd_7591668 : Nat := 1299391551119036265912187

theorem tailTrace_7591668 : CollatzResearch.WordTrace tailWord_7591668 prefixEnd_7591668 1299391551119036265912187 := by
  unfold tailWord_7591668
  simp only [CollatzResearch.WordTrace]
  refine ⟨138445439730345432257799829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184593919640460576343733105 138445439730345432257799829)
  ·
    refine ⟨6489629987359942137084367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138445439730345432257799829 6489629987359942137084367)
    ·
      refine ⟨9734444981039913205626551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6489629987359942137084367 9734444981039913205626551)
      ·
        refine ⟨14601667471559869808439827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9734444981039913205626551 14601667471559869808439827)
        ·
          refine ⟨21902501207339804712659741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14601667471559869808439827 21902501207339804712659741)
          ·
            refine ⟨8213437952752426767247403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21902501207339804712659741 8213437952752426767247403)
            ·
              refine ⟨12320156929128640150871105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8213437952752426767247403 12320156929128640150871105)
              ·
                refine ⟨9240117696846480113153329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12320156929128640150871105 9240117696846480113153329)
                ·
                  refine ⟨6930088272634860084864997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9240117696846480113153329 6930088272634860084864997)
                  ·
                    refine ⟨1299391551119036265912187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6930088272634860084864997 1299391551119036265912187)
                    ·
                      rfl

theorem cell23_7591668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_7591668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591668 prefixEnd_7591668 := by exact prefixLift 7591668
  have htrace : WordTrace (prefixWord ++ tailWord_7591668) baseStart_7591668 baseEnd_7591668 := by
    simpa [prefixWord, tailWord_7591668, baseEnd_7591668] using wordTrace_append hprefix tailTrace_7591668
  have hstable : (prefixWord ++ tailWord_7591668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591668).length < 2 ^ (prefixWord ++ tailWord_7591668).sum := by decide
  have hdescent : baseEnd_7591668 < baseStart_7591668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591690 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_7591690 : Nat := 118140960795 + 7591690 * 2 ^ 59
def prefixEnd_7591690 : Nat := 4983230072969 + 3 ^ 40 * 7591690 * 2
def baseEnd_7591690 : Nat := 1299395316643835903887153

theorem tailTrace_7591690 : CollatzResearch.WordTrace tailWord_7591690 prefixEnd_7591690 1299395316643835903887153 := by
  unfold tailWord_7591690
  simp only [CollatzResearch.WordTrace]
  refine ⟨69222920466652790568225131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184594454577740774848600349 69222920466652790568225131)
  ·
    refine ⟨103834380699979185852337697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69222920466652790568225131 103834380699979185852337697)
    ·
      refine ⟨77875785524984389389253273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103834380699979185852337697 77875785524984389389253273)
      ·
        refine ⟨58406839143738292041939955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77875785524984389389253273 58406839143738292041939955)
        ·
          refine ⟨87610258715607438062909933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58406839143738292041939955 87610258715607438062909933)
          ·
            refine ⟨32853847018352789273591225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87610258715607438062909933 32853847018352789273591225)
            ·
              refine ⟨24640385263764591955193419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32853847018352789273591225 24640385263764591955193419)
              ·
                refine ⟨36960577895646887932790129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24640385263764591955193419 36960577895646887932790129)
                ·
                  refine ⟨27720433421735165949592597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36960577895646887932790129 27720433421735165949592597)
                  ·
                    refine ⟨1299395316643835903887153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27720433421735165949592597 1299395316643835903887153)
                    ·
                      rfl

theorem cell23_7591690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_7591690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591690 prefixEnd_7591690 := by exact prefixLift 7591690
  have htrace : WordTrace (prefixWord ++ tailWord_7591690) baseStart_7591690 baseEnd_7591690 := by
    simpa [prefixWord, tailWord_7591690, baseEnd_7591690] using wordTrace_append hprefix tailTrace_7591690
  have hstable : (prefixWord ++ tailWord_7591690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591690).length < 2 ^ (prefixWord ++ tailWord_7591690).sum := by decide
  have hdescent : baseEnd_7591690 < baseStart_7591690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591714 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_7591714 : Nat := 118140960795 + 7591714 * 2 ^ 59
def prefixEnd_7591714 : Nat := 4983230072969 + 3 ^ 40 * 7591714 * 2
def baseEnd_7591714 : Nat := 3898198273467215617761349

theorem tailTrace_7591714 : CollatzResearch.WordTrace tailWord_7591714 prefixEnd_7591714 3898198273467215617761349 := by
  unfold tailWord_7591714
  simp only [CollatzResearch.WordTrace]
  refine ⟨69223139304631053592943549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184595038145682809581182797 69223139304631053592943549)
  ·
    refine ⟨25958677239236645097353831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69223139304631053592943549 25958677239236645097353831)
    ·
      refine ⟨38938015858854967646030747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25958677239236645097353831 38938015858854967646030747)
      ·
        refine ⟨58407023788282451469046121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38938015858854967646030747 58407023788282451469046121)
        ·
          refine ⟨43805267841211838601784591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58407023788282451469046121 43805267841211838601784591)
          ·
            refine ⟨65707901761817757902676887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43805267841211838601784591 65707901761817757902676887)
            ·
              refine ⟨98561852642726636854015331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65707901761817757902676887 98561852642726636854015331)
              ·
                refine ⟨147842778964089955281022997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98561852642726636854015331 147842778964089955281022997)
                ·
                  refine ⟨6930130263941716653797953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147842778964089955281022997 6930130263941716653797953)
                  ·
                    refine ⟨5197597697956287490348465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6930130263941716653797953 5197597697956287490348465)
                    ·
                      refine ⟨3898198273467215617761349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5197597697956287490348465 3898198273467215617761349)
                      ·
                        rfl

theorem cell23_7591714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_7591714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591714 prefixEnd_7591714 := by exact prefixLift 7591714
  have htrace : WordTrace (prefixWord ++ tailWord_7591714) baseStart_7591714 baseEnd_7591714 := by
    simpa [prefixWord, tailWord_7591714, baseEnd_7591714] using wordTrace_append hprefix tailTrace_7591714
  have hstable : (prefixWord ++ tailWord_7591714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591714).length < 2 ^ (prefixWord ++ tailWord_7591714).sum := by decide
  have hdescent : baseEnd_7591714 < baseStart_7591714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591723 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 8]
def baseStart_7591723 : Nat := 118140960795 + 7591723 * 2 ^ 59
def prefixEnd_7591723 : Nat := 4983230072969 + 3 ^ 40 * 7591723 * 2
def baseEnd_7591723 : Nat := 3898202894793106082548807

theorem tailTrace_7591723 : CollatzResearch.WordTrace tailWord_7591723 prefixEnd_7591723 3898202894793106082548807 := by
  unfold tailWord_7591723
  simp only [CollatzResearch.WordTrace]
  refine ⟨276892885475491608908851823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184595256983661072605901215 276892885475491608908851823)
  ·
    refine ⟨415339328213237413363277735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276892885475491608908851823 415339328213237413363277735)
    ·
      refine ⟨623008992319856120044916603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415339328213237413363277735 623008992319856120044916603)
      ·
        refine ⟨934513488479784180067374905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623008992319856120044916603 934513488479784180067374905)
        ·
          refine ⟨700885116359838135050531179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934513488479784180067374905 700885116359838135050531179)
          ·
            refine ⟨1051327674539757202575796769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700885116359838135050531179 1051327674539757202575796769)
            ·
              refine ⟨788495755904817901931847577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051327674539757202575796769 788495755904817901931847577)
              ·
                refine ⟨591371816928613426448885683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788495755904817901931847577 591371816928613426448885683)
                ·
                  refine ⟨887057725392920139673328525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591371816928613426448885683 887057725392920139673328525)
                  ·
                    refine ⟨332646647022345052377498197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 887057725392920139673328525 332646647022345052377498197)
                    ·
                      refine ⟨3898202894793106082548807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 332646647022345052377498197 3898202894793106082548807)
                      ·
                        rfl

theorem cell23_7591723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_7591723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591723 prefixEnd_7591723 := by exact prefixLift 7591723
  have htrace : WordTrace (prefixWord ++ tailWord_7591723) baseStart_7591723 baseEnd_7591723 := by
    simpa [prefixWord, tailWord_7591723, baseEnd_7591723] using wordTrace_append hprefix tailTrace_7591723
  have hstable : (prefixWord ++ tailWord_7591723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591723).length < 2 ^ (prefixWord ++ tailWord_7591723).sum := by decide
  have hdescent : baseEnd_7591723 < baseStart_7591723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591787 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 2, 4, 2]
def baseStart_7591787 : Nat := 118140960795 + 7591787 * 2 ^ 59
def prefixEnd_7591787 : Nat := 4983230072969 + 3 ^ 40 * 7591787 * 2
def baseEnd_7591787 : Nat := 3898235757554993832148513

theorem tailTrace_7591787 : CollatzResearch.WordTrace tailWord_7591787 prefixEnd_7591787 3898235757554993832148513 := by
  unfold tailWord_7591787
  simp only [CollatzResearch.WordTrace]
  refine ⟨276895219747259747839181615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184596813164839831892787743 276895219747259747839181615)
  ·
    refine ⟨415342829620889621758772423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276895219747259747839181615 415342829620889621758772423)
    ·
      refine ⟨623014244431334432638158635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415342829620889621758772423 623014244431334432638158635)
      ·
        refine ⟨934521366647001648957237953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623014244431334432638158635 934521366647001648957237953)
        ·
          refine ⟨700891024985251236717928465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934521366647001648957237953 700891024985251236717928465)
          ·
            refine ⟨525668268738938427538446349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700891024985251236717928465 525668268738938427538446349)
            ·
              refine ⟨197125600777101910326917381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 525668268738938427538446349 197125600777101910326917381)
              ·
                refine ⟨36961050145706608186297009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197125600777101910326917381 36961050145706608186297009)
                ·
                  refine ⟨27720787609279956139722757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36961050145706608186297009 27720787609279956139722757)
                  ·
                    refine ⟨5197647676739991776198017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27720787609279956139722757 5197647676739991776198017)
                    ·
                      refine ⟨3898235757554993832148513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5197647676739991776198017 3898235757554993832148513)
                      ·
                        rfl

theorem cell23_7591787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 4, 2].length) (baseStart_7591787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591787 prefixEnd_7591787 := by exact prefixLift 7591787
  have htrace : WordTrace (prefixWord ++ tailWord_7591787) baseStart_7591787 baseEnd_7591787 := by
    simpa [prefixWord, tailWord_7591787, baseEnd_7591787] using wordTrace_append hprefix tailTrace_7591787
  have hstable : (prefixWord ++ tailWord_7591787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591787).length < 2 ^ (prefixWord ++ tailWord_7591787).sum := by decide
  have hdescent : baseEnd_7591787 < baseStart_7591787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591831 : List Nat := [1, 1, 3, 3, 1, 4, 2, 3, 1, 4]
def baseStart_7591831 : Nat := 118140960795 + 7591831 * 2 ^ 59
def prefixEnd_7591831 : Nat := 4983230072969 + 3 ^ 40 * 7591831 * 2
def baseEnd_7591831 : Nat := 1299419450234597219999437

theorem tailTrace_7591831 : CollatzResearch.WordTrace tailWord_7591831 prefixEnd_7591831 1299419450234597219999437 := by
  unfold tailWord_7591831
  simp only [CollatzResearch.WordTrace]
  refine ⟨276896824559100343353783347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184597883039400228902522231 276896824559100343353783347)
  ·
    refine ⟨415345236838650515030675021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276896824559100343353783347 415345236838650515030675021)
    ·
      refine ⟨155754463814493943136503133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415345236838650515030675021 155754463814493943136503133)
      ·
        refine ⟨58407923930435228676188675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155754463814493943136503133 58407923930435228676188675)
        ·
          refine ⟨87611885895652843014283013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58407923930435228676188675 87611885895652843014283013)
          ·
            refine ⟨16427228605434908065178065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87611885895652843014283013 16427228605434908065178065)
            ·
              refine ⟨12320421454076181048883549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16427228605434908065178065 12320421454076181048883549)
              ·
                refine ⟨4620158045278567893331331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12320421454076181048883549 4620158045278567893331331)
                ·
                  refine ⟨6930237067917851839996997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4620158045278567893331331 6930237067917851839996997)
                  ·
                    refine ⟨1299419450234597219999437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6930237067917851839996997 1299419450234597219999437)
                    ·
                      rfl

theorem cell23_7591831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_7591831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591831 prefixEnd_7591831 := by exact prefixLift 7591831
  have htrace : WordTrace (prefixWord ++ tailWord_7591831) baseStart_7591831 baseEnd_7591831 := by
    simpa [prefixWord, tailWord_7591831, baseEnd_7591831] using wordTrace_append hprefix tailTrace_7591831
  have hstable : (prefixWord ++ tailWord_7591831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591831).length < 2 ^ (prefixWord ++ tailWord_7591831).sum := by decide
  have hdescent : baseEnd_7591831 < baseStart_7591831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591844 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 6]
def baseStart_7591844 : Nat := 118140960795 + 7591844 * 2 ^ 59
def prefixEnd_7591844 : Nat := 4983230072969 + 3 ^ 40 * 7591844 * 2
def baseEnd_7591844 : Nat := 433140558439144456570639

theorem tailTrace_7591844 : CollatzResearch.WordTrace tailWord_7591844 prefixEnd_7591844 433140558439144456570639 := by
  unfold tailWord_7591844
  simp only [CollatzResearch.WordTrace]
  refine ⟨138448649354026623287003293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184598199138702164382671057 138448649354026623287003293)
  ·
    refine ⟨51918243507759983732626235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138448649354026623287003293 51918243507759983732626235)
    ·
      refine ⟨77877365261639975598939353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51918243507759983732626235 77877365261639975598939353)
      ·
        refine ⟨58408023946229981699204515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77877365261639975598939353 58408023946229981699204515)
        ·
          refine ⟨87612035919344972548806773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58408023946229981699204515 87612035919344972548806773)
          ·
            refine ⟨8213628367438591176450635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87612035919344972548806773 8213628367438591176450635)
            ·
              refine ⟨12320442551157886764675953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8213628367438591176450635 12320442551157886764675953)
              ·
                refine ⟨9240331913368415073506965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12320442551157886764675953 9240331913368415073506965)
                ·
                  refine ⟨433140558439144456570639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9240331913368415073506965 433140558439144456570639)
                  ·
                    rfl

theorem cell23_7591844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_7591844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591844 prefixEnd_7591844 := by exact prefixLift 7591844
  have htrace : WordTrace (prefixWord ++ tailWord_7591844) baseStart_7591844 baseEnd_7591844 := by
    simpa [prefixWord, tailWord_7591844, baseEnd_7591844] using wordTrace_append hprefix tailTrace_7591844
  have hstable : (prefixWord ++ tailWord_7591844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591844).length < 2 ^ (prefixWord ++ tailWord_7591844).sum := by decide
  have hdescent : baseEnd_7591844 < baseStart_7591844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591847 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_7591847 : Nat := 118140960795 + 7591847 * 2 ^ 59
def prefixEnd_7591847 : Nat := 4983230072969 + 3 ^ 40 * 7591847 * 2
def baseEnd_7591847 : Nat := 3898266566394263597398237

theorem tailTrace_7591847 : CollatzResearch.WordTrace tailWord_7591847 prefixEnd_7591847 3898266566394263597398237 := by
  unfold tailWord_7591847
  simp only [CollatzResearch.WordTrace]
  refine ⟨276897408127042378086365795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184598272084694918724243863 276897408127042378086365795)
  ·
    refine ⟨415346112190563567129548693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276897408127042378086365795 415346112190563567129548693)
    ·
      refine ⟨19469349008932667209197595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 415346112190563567129548693 19469349008932667209197595)
      ·
        refine ⟨29204023513399000813796393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19469349008932667209197595 29204023513399000813796393)
        ·
          refine ⟨21903017635049250610347295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29204023513399000813796393 21903017635049250610347295)
          ·
            refine ⟨32854526452573875915520943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21903017635049250610347295 32854526452573875915520943)
            ·
              refine ⟨49281789678860813873281415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32854526452573875915520943 49281789678860813873281415)
              ·
                refine ⟨73922684518291220809922123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49281789678860813873281415 73922684518291220809922123)
                ·
                  refine ⟨110884026777436831214883185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73922684518291220809922123 110884026777436831214883185)
                  ·
                    refine ⟨83163020083077623411162389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110884026777436831214883185 83163020083077623411162389)
                    ·
                      refine ⟨3898266566394263597398237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83163020083077623411162389 3898266566394263597398237)
                      ·
                        rfl

theorem cell23_7591847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_7591847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591847 prefixEnd_7591847 := by exact prefixLift 7591847
  have htrace : WordTrace (prefixWord ++ tailWord_7591847) baseStart_7591847 baseEnd_7591847 := by
    simpa [prefixWord, tailWord_7591847, baseEnd_7591847] using wordTrace_append hprefix tailTrace_7591847
  have hstable : (prefixWord ++ tailWord_7591847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591847).length < 2 ^ (prefixWord ++ tailWord_7591847).sum := by decide
  have hdescent : baseEnd_7591847 < baseStart_7591847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591848 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 3, 4]
def baseStart_7591848 : Nat := 118140960795 + 7591848 * 2 ^ 59
def prefixEnd_7591848 : Nat := 4983230072969 + 3 ^ 40 * 7591848 * 2
def baseEnd_7591848 : Nat := 1299422359958306031161911

theorem tailTrace_7591848 : CollatzResearch.WordTrace tailWord_7591848 prefixEnd_7591848 1299422359958306031161911 := by
  unfold tailWord_7591848
  simp only [CollatzResearch.WordTrace]
  refine ⟨138448722300019377628576099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184598296400025836838101465 138448722300019377628576099)
  ·
    refine ⟨207673083450029066442864149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138448722300019377628576099 207673083450029066442864149)
    ·
      refine ⟨9734675786720112489509257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 207673083450029066442864149 9734675786720112489509257)
      ·
        refine ⟨7301006840040084367131943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9734675786720112489509257 7301006840040084367131943)
        ·
          refine ⟨10951510260060126550697915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301006840040084367131943 10951510260060126550697915)
          ·
            refine ⟨16427265390090189826046873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10951510260060126550697915 16427265390090189826046873)
            ·
              refine ⟨12320449042567642369535155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16427265390090189826046873 12320449042567642369535155)
              ·
                refine ⟨18480673563851463554302733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12320449042567642369535155 18480673563851463554302733)
                ·
                  refine ⟨6930252586444298832863525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18480673563851463554302733 6930252586444298832863525)
                  ·
                    refine ⟨1299422359958306031161911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6930252586444298832863525 1299422359958306031161911)
                    ·
                      rfl

theorem cell23_7591848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_7591848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591848 prefixEnd_7591848 := by exact prefixLift 7591848
  have htrace : WordTrace (prefixWord ++ tailWord_7591848) baseStart_7591848 baseEnd_7591848 := by
    simpa [prefixWord, tailWord_7591848, baseEnd_7591848] using wordTrace_append hprefix tailTrace_7591848
  have hstable : (prefixWord ++ tailWord_7591848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591848).length < 2 ^ (prefixWord ++ tailWord_7591848).sum := by decide
  have hdescent : baseEnd_7591848 < baseStart_7591848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591887 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 6, 4]
def baseStart_7591887 : Nat := 118140960795 + 7591887 * 2 ^ 59
def prefixEnd_7591887 : Nat := 4983230072969 + 3 ^ 40 * 7591887 * 2
def baseEnd_7591887 : Nat := 1299429035206814480299351

theorem tailTrace_7591887 : CollatzResearch.WordTrace tailWord_7591887 prefixEnd_7591887 1299429035206814480299351 := by
  unfold tailWord_7591887
  simp only [CollatzResearch.WordTrace]
  refine ⟨276898867046897464917821915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184599244697931643278547943 276898867046897464917821915)
  ·
    refine ⟨415348300570346197376732873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276898867046897464917821915 415348300570346197376732873)
    ·
      refine ⟨311511225427759648032549655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415348300570346197376732873 311511225427759648032549655)
      ·
        refine ⟨467266838141639472048824483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311511225427759648032549655 467266838141639472048824483)
        ·
          refine ⟨700900257212459208073236725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467266838141639472048824483 700900257212459208073236725)
          ·
            refine ⟨65709399113668050756865943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 700900257212459208073236725 65709399113668050756865943)
            ·
              refine ⟨98564098670502076135298915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65709399113668050756865943 98564098670502076135298915)
              ·
                refine ⟨147846148005753114202948373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98564098670502076135298915 147846148005753114202948373)
                ·
                  refine ⟨6930288187769677228263205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147846148005753114202948373 6930288187769677228263205)
                  ·
                    refine ⟨1299429035206814480299351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6930288187769677228263205 1299429035206814480299351)
                    ·
                      rfl

theorem cell23_7591887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 4].length) (baseStart_7591887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591887 prefixEnd_7591887 := by exact prefixLift 7591887
  have htrace : WordTrace (prefixWord ++ tailWord_7591887) baseStart_7591887 baseEnd_7591887 := by
    simpa [prefixWord, tailWord_7591887, baseEnd_7591887] using wordTrace_append hprefix tailTrace_7591887
  have hstable : (prefixWord ++ tailWord_7591887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591887).length < 2 ^ (prefixWord ++ tailWord_7591887).sum := by decide
  have hdescent : baseEnd_7591887 < baseStart_7591887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591907 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 6]
def baseStart_7591907 : Nat := 118140960795 + 7591907 * 2 ^ 59
def prefixEnd_7591907 : Nat := 4983230072969 + 3 ^ 40 * 7591907 * 2
def baseEnd_7591907 : Nat := 3898297375233533362647961

theorem tailTrace_7591907 : CollatzResearch.WordTrace tailWord_7591907 prefixEnd_7591907 3898297375233533362647961 := by
  unfold tailWord_7591907
  simp only [CollatzResearch.WordTrace]
  refine ⟨276899596506825008333549975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184599731004550005555699983 276899596506825008333549975)
  ·
    refine ⟨415349394760237512500324963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276899596506825008333549975 415349394760237512500324963)
    ·
      refine ⟨623024092140356268750487445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415349394760237512500324963 623024092140356268750487445)
      ·
        refine ⟨29204254319079200097679099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 623024092140356268750487445 29204254319079200097679099)
        ·
          refine ⟨43806381478618800146518649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29204254319079200097679099 43806381478618800146518649)
          ·
            refine ⟨32854786108964100109888987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43806381478618800146518649 32854786108964100109888987)
            ·
              refine ⟨49282179163446150164833481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32854786108964100109888987 49282179163446150164833481)
              ·
                refine ⟨36961634372584612623625111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49282179163446150164833481 36961634372584612623625111)
                ·
                  refine ⟨55442451558876918935437667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36961634372584612623625111 55442451558876918935437667)
                  ·
                    refine ⟨83163677338315378403156501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55442451558876918935437667 83163677338315378403156501)
                    ·
                      refine ⟨3898297375233533362647961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83163677338315378403156501 3898297375233533362647961)
                      ·
                        rfl

theorem cell23_7591907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_7591907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591907 prefixEnd_7591907 := by exact prefixLift 7591907
  have htrace : WordTrace (prefixWord ++ tailWord_7591907) baseStart_7591907 baseEnd_7591907 := by
    simpa [prefixWord, tailWord_7591907, baseEnd_7591907] using wordTrace_append hprefix tailTrace_7591907
  have hstable : (prefixWord ++ tailWord_7591907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591907).length < 2 ^ (prefixWord ++ tailWord_7591907).sum := by decide
  have hdescent : baseEnd_7591907 < baseStart_7591907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591914 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_7591914 : Nat := 118140960795 + 7591914 * 2 ^ 59
def prefixEnd_7591914 : Nat := 4983230072969 + 3 ^ 40 * 7591914 * 2
def baseEnd_7591914 : Nat := 3898300969598114835260429

theorem tailTrace_7591914 : CollatzResearch.WordTrace tailWord_7591914 prefixEnd_7591914 3898300969598114835260429 := by
  unfold tailWord_7591914
  simp only [CollatzResearch.WordTrace]
  refine ⟨69224962954449912132263699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184599901211866432352703197 69224962954449912132263699)
  ·
    refine ⟨103837444431674868198395549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69224962954449912132263699 103837444431674868198395549)
    ·
      refine ⟨38939041661878075574398331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103837444431674868198395549 38939041661878075574398331)
      ·
        refine ⟨58408562492817113361597497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38939041661878075574398331 58408562492817113361597497)
        ·
          refine ⟨43806421869612835021198123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58408562492817113361597497 43806421869612835021198123)
          ·
            refine ⟨65709632804419252531797185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43806421869612835021198123 65709632804419252531797185)
            ·
              refine ⟨49282224603314439398847889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65709632804419252531797185 49282224603314439398847889)
              ·
                refine ⟨36961668452485829549135917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49282224603314439398847889 36961668452485829549135917)
                ·
                  refine ⟨13860625669682186080925969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36961668452485829549135917 13860625669682186080925969)
                  ·
                    refine ⟨10395469252261639560694477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13860625669682186080925969 10395469252261639560694477)
                    ·
                      refine ⟨3898300969598114835260429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10395469252261639560694477 3898300969598114835260429)
                      ·
                        rfl

theorem cell23_7591914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_7591914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591914 prefixEnd_7591914 := by exact prefixLift 7591914
  have htrace : WordTrace (prefixWord ++ tailWord_7591914) baseStart_7591914 baseEnd_7591914 := by
    simpa [prefixWord, tailWord_7591914, baseEnd_7591914] using wordTrace_append hprefix tailTrace_7591914
  have hstable : (prefixWord ++ tailWord_7591914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591914).length < 2 ^ (prefixWord ++ tailWord_7591914).sum := by decide
  have hdescent : baseEnd_7591914 < baseStart_7591914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591921 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 2, 4]
def baseStart_7591921 : Nat := 118140960795 + 7591921 * 2 ^ 59
def prefixEnd_7591921 : Nat := 4983230072969 + 3 ^ 40 * 7591921 * 2
def baseEnd_7591921 : Nat := 1299434854654232102624299

theorem tailTrace_7591921 : CollatzResearch.WordTrace tailWord_7591921 prefixEnd_7591921 1299434854654232102624299 := by
  unfold tailWord_7591921
  simp only [CollatzResearch.WordTrace]
  refine ⟨276900107128774288724559617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184600071419182859149706411 276900107128774288724559617)
  ·
    refine ⟨207675080346580716543419713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276900107128774288724559617 207675080346580716543419713)
    ·
      refine ⟨155756310259935537407564785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207675080346580716543419713 155756310259935537407564785)
      ·
        refine ⟨116817232694951653055673589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155756310259935537407564785 116817232694951653055673589)
        ·
          refine ⟨10951615565151717473969399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116817232694951653055673589 10951615565151717473969399)
          ·
            refine ⟨16427423347727576210954099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10951615565151717473969399 16427423347727576210954099)
            ·
              refine ⟨24641135021591364316431149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16427423347727576210954099 24641135021591364316431149)
              ·
                refine ⟨9240425633096761618661681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24641135021591364316431149 9240425633096761618661681)
                ·
                  refine ⟨6930319224822571213996261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9240425633096761618661681 6930319224822571213996261)
                  ·
                    refine ⟨1299434854654232102624299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6930319224822571213996261 1299434854654232102624299)
                    ·
                      rfl

theorem cell23_7591921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_7591921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591921 prefixEnd_7591921 := by exact prefixLift 7591921
  have htrace : WordTrace (prefixWord ++ tailWord_7591921) baseStart_7591921 baseEnd_7591921 := by
    simpa [prefixWord, tailWord_7591921, baseEnd_7591921] using wordTrace_append hprefix tailTrace_7591921
  have hstable : (prefixWord ++ tailWord_7591921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591921).length < 2 ^ (prefixWord ++ tailWord_7591921).sum := by decide
  have hdescent : baseEnd_7591921 < baseStart_7591921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591927 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 3]
def baseStart_7591927 : Nat := 118140960795 + 7591927 * 2 ^ 59
def prefixEnd_7591927 : Nat := 4983230072969 + 3 ^ 40 * 7591927 * 2
def baseEnd_7591927 : Nat := 3898307644846623284397869

theorem tailTrace_7591927 : CollatzResearch.WordTrace tailWord_7591927 prefixEnd_7591927 3898307644846623284397869 := by
  unfold tailWord_7591927
  simp only [CollatzResearch.WordTrace]
  refine ⟨276900325966752551749278035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184600217311168367832852023 276900325966752551749278035)
  ·
    refine ⟨415350488950128827623917053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276900325966752551749278035 415350488950128827623917053)
    ·
      refine ⟨155756433356298310358968895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415350488950128827623917053 155756433356298310358968895)
      ·
        refine ⟨233634650034447465538453343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155756433356298310358968895 233634650034447465538453343)
        ·
          refine ⟨350451975051671198307680015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233634650034447465538453343 350451975051671198307680015)
          ·
            refine ⟨525677962577506797461520023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350451975051671198307680015 525677962577506797461520023)
            ·
              refine ⟨788516943866260196192280035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525677962577506797461520023 788516943866260196192280035)
              ·
                refine ⟨1182775415799390294288420053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788516943866260196192280035 1182775415799390294288420053)
                ·
                  refine ⟨27721298807798210022384845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1182775415799390294288420053 27721298807798210022384845)
                  ·
                    refine ⟨10395487052924328758394317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27721298807798210022384845 10395487052924328758394317)
                    ·
                      refine ⟨3898307644846623284397869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10395487052924328758394317 3898307644846623284397869)
                      ·
                        rfl

theorem cell23_7591927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_7591927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591927 prefixEnd_7591927 := by exact prefixLift 7591927
  have htrace : WordTrace (prefixWord ++ tailWord_7591927) baseStart_7591927 baseEnd_7591927 := by
    simpa [prefixWord, tailWord_7591927, baseEnd_7591927] using wordTrace_append hprefix tailTrace_7591927
  have hstable : (prefixWord ++ tailWord_7591927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591927).length < 2 ^ (prefixWord ++ tailWord_7591927).sum := by decide
  have hdescent : baseEnd_7591927 < baseStart_7591927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591934 : List Nat := [4, 2, 2, 2, 1, 1, 2, 9]
def baseStart_7591934 : Nat := 118140960795 + 7591934 * 2 ^ 59
def prefixEnd_7591934 : Nat := 4983230072969 + 3 ^ 40 * 7591934 * 2
def baseEnd_7591934 : Nat := 144381897748563139148531

theorem tailTrace_7591934 : CollatzResearch.WordTrace tailWord_7591934 prefixEnd_7591934 144381897748563139148531 := by
  unfold tailWord_7591934
  simp only [CollatzResearch.WordTrace]
  refine ⟨34612572659715898993097857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184600387518484794629855237 34612572659715898993097857)
  ·
    refine ⟨25959429494786924244823393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34612572659715898993097857 25959429494786924244823393)
    ·
      refine ⟨19469572121090193183617545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25959429494786924244823393 19469572121090193183617545)
      ·
        refine ⟨14602179090817644887713159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19469572121090193183617545 14602179090817644887713159)
        ·
          refine ⟨21903268636226467331569739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14602179090817644887713159 21903268636226467331569739)
          ·
            refine ⟨32854902954339700997354609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21903268636226467331569739 32854902954339700997354609)
            ·
              refine ⟨24641177215754775748015957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32854902954339700997354609 24641177215754775748015957)
              ·
                refine ⟨144381897748563139148531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24641177215754775748015957 144381897748563139148531)
                ·
                  rfl

theorem cell23_7591934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_7591934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591934 prefixEnd_7591934 := by exact prefixLift 7591934
  have htrace : WordTrace (prefixWord ++ tailWord_7591934) baseStart_7591934 baseEnd_7591934 := by
    simpa [prefixWord, tailWord_7591934, baseEnd_7591934] using wordTrace_append hprefix tailTrace_7591934
  have hstable : (prefixWord ++ tailWord_7591934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591934).length < 2 ^ (prefixWord ++ tailWord_7591934).sum := by decide
  have hdescent : baseEnd_7591934 < baseStart_7591934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591944 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_7591944 : Nat := 118140960795 + 7591944 * 2 ^ 59
def prefixEnd_7591944 : Nat := 4983230072969 + 3 ^ 40 * 7591944 * 2
def baseEnd_7591944 : Nat := 3898316374017749717885291

theorem tailTrace_7591944 : CollatzResearch.WordTrace tailWord_7591944 prefixEnd_7591944 3898316374017749717885291 := by
  unfold tailWord_7591944
  simp only [CollatzResearch.WordTrace]
  refine ⟨138450473003845481826323443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184600630671793975768431257 138450473003845481826323443)
  ·
    refine ⟨207675709505768222739485165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138450473003845481826323443 207675709505768222739485165)
    ·
      refine ⟨77878391064663083527306937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207675709505768222739485165 77878391064663083527306937)
      ·
        refine ⟨58408793298497312645480203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77878391064663083527306937 58408793298497312645480203)
        ·
          refine ⟨87613189947745968968220305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58408793298497312645480203 87613189947745968968220305)
          ·
            refine ⟨65709892460809476726165229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87613189947745968968220305 65709892460809476726165229)
            ·
              refine ⟨24641209672803553772311961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65709892460809476726165229 24641209672803553772311961)
              ·
                refine ⟨18480907254602665329233971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24641209672803553772311961 18480907254602665329233971)
                ·
                  refine ⟨27721360881903997993850957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18480907254602665329233971 27721360881903997993850957)
                  ·
                    refine ⟨10395510330713999247694109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27721360881903997993850957 10395510330713999247694109)
                    ·
                      refine ⟨3898316374017749717885291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10395510330713999247694109 3898316374017749717885291)
                      ·
                        rfl

theorem cell23_7591944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_7591944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591944 prefixEnd_7591944 := by exact prefixLift 7591944
  have htrace : WordTrace (prefixWord ++ tailWord_7591944) baseStart_7591944 baseEnd_7591944 := by
    simpa [prefixWord, tailWord_7591944, baseEnd_7591944] using wordTrace_append hprefix tailTrace_7591944
  have hstable : (prefixWord ++ tailWord_7591944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591944).length < 2 ^ (prefixWord ++ tailWord_7591944).sum := by decide
  have hdescent : baseEnd_7591944 < baseStart_7591944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591956 : List Nat := [2, 4, 3, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_7591956 : Nat := 118140960795 + 7591956 * 2 ^ 59
def prefixEnd_7591956 : Nat := 4983230072969 + 3 ^ 40 * 7591956 * 2
def baseEnd_7591956 : Nat := 3898322535785603670935237

theorem tailTrace_7591956 : CollatzResearch.WordTrace tailWord_7591956 prefixEnd_7591956 3898322535785603670935237 := by
  unfold tailWord_7591956
  simp only [CollatzResearch.WordTrace]
  refine ⟨138450691841823744851041861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184600922455764993134722481 138450691841823744851041861)
  ·
    refine ⟨25959504720341952159570349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138450691841823744851041861 25959504720341952159570349)
    ·
      refine ⟨9734814270128232059838881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25959504720341952159570349 9734814270128232059838881)
      ·
        refine ⟨7301110702596174044879161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9734814270128232059838881 7301110702596174044879161)
        ·
          refine ⟨5475833026947130533659371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7301110702596174044879161 5475833026947130533659371)
          ·
            refine ⟨8213749540420695800489057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5475833026947130533659371 8213749540420695800489057)
            ·
              refine ⟨6160312155315521850366793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8213749540420695800489057 6160312155315521850366793)
              ·
                refine ⟨4620234116486641387775095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6160312155315521850366793 4620234116486641387775095)
                ·
                  refine ⟨6930351174729962081662643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4620234116486641387775095 6930351174729962081662643)
                  ·
                    refine ⟨10395526762094943122493965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6930351174729962081662643 10395526762094943122493965)
                    ·
                      refine ⟨3898322535785603670935237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10395526762094943122493965 3898322535785603670935237)
                      ·
                        rfl

theorem cell23_7591956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_7591956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591956 prefixEnd_7591956 := by exact prefixLift 7591956
  have htrace : WordTrace (prefixWord ++ tailWord_7591956) baseStart_7591956 baseEnd_7591956 := by
    simpa [prefixWord, tailWord_7591956, baseEnd_7591956] using wordTrace_append hprefix tailTrace_7591956
  have hstable : (prefixWord ++ tailWord_7591956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591956).length < 2 ^ (prefixWord ++ tailWord_7591956).sum := by decide
  have hdescent : baseEnd_7591956 < baseStart_7591956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591962 : List Nat := [3, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2]
def baseStart_7591962 : Nat := 118140960795 + 7591962 * 2 ^ 59
def prefixEnd_7591962 : Nat := 4983230072969 + 3 ^ 40 * 7591962 * 2
def baseEnd_7591962 : Nat := 3898325616669530647460209

theorem tailTrace_7591962 : CollatzResearch.WordTrace tailWord_7591962 prefixEnd_7591962 3898325616669530647460209 := by
  unfold tailWord_7591962
  simp only [CollatzResearch.WordTrace]
  refine ⟨69225400630406438181700535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184601068347750501817868093 69225400630406438181700535)
  ·
    refine ⟨103838100945609657272550803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69225400630406438181700535 103838100945609657272550803)
    ·
      refine ⟨155757151418414485908826205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103838100945609657272550803 155757151418414485908826205)
      ·
        refine ⟨58408931781905432215809827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155757151418414485908826205 58408931781905432215809827)
        ·
          refine ⟨87613397672858148323714741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58408931781905432215809827 87613397672858148323714741)
          ·
            refine ⟨8213756031830451405348257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87613397672858148323714741 8213756031830451405348257)
            ·
              refine ⟨6160317023872838554011193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8213756031830451405348257 6160317023872838554011193)
              ·
                refine ⟨4620237767904628915508395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6160317023872838554011193 4620237767904628915508395)
                ·
                  refine ⟨6930356651856943373262593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4620237767904628915508395 6930356651856943373262593)
                  ·
                    refine ⟨5197767488892707529946945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6930356651856943373262593 5197767488892707529946945)
                    ·
                      refine ⟨3898325616669530647460209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5197767488892707529946945 3898325616669530647460209)
                      ·
                        rfl

theorem cell23_7591962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_7591962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591962 prefixEnd_7591962 := by exact prefixLift 7591962
  have htrace : WordTrace (prefixWord ++ tailWord_7591962) baseStart_7591962 baseEnd_7591962 := by
    simpa [prefixWord, tailWord_7591962, baseEnd_7591962] using wordTrace_append hprefix tailTrace_7591962
  have hstable : (prefixWord ++ tailWord_7591962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591962).length < 2 ^ (prefixWord ++ tailWord_7591962).sum := by decide
  have hdescent : baseEnd_7591962 < baseStart_7591962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591967 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 4]
def baseStart_7591967 : Nat := 118140960795 + 7591967 * 2 ^ 59
def prefixEnd_7591967 : Nat := 4983230072969 + 3 ^ 40 * 7591967 * 2
def baseEnd_7591967 : Nat := 3898328184072803127897685

theorem tailTrace_7591967 : CollatzResearch.WordTrace tailWord_7591967 prefixEnd_7591967 3898328184072803127897685 := by
  unfold tailWord_7591967
  simp only [CollatzResearch.WordTrace]
  refine ⟨276901784886607638580734155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184601189924405092387156103 276901784886607638580734155)
  ·
    refine ⟨415352677329911457871101233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276901784886607638580734155 415352677329911457871101233)
    ·
      refine ⟨311514507997433593403325925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415352677329911457871101233 311514507997433593403325925)
      ·
        refine ⟨58408970249518798763123611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311514507997433593403325925 58408970249518798763123611)
        ·
          refine ⟨87613455374278198144685417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58408970249518798763123611 87613455374278198144685417)
          ·
            refine ⟨65710091530708648608514063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87613455374278198144685417 65710091530708648608514063)
            ·
              refine ⟨98565137296062972912771095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65710091530708648608514063 98565137296062972912771095)
              ·
                refine ⟨147847705944094459369156643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98565137296062972912771095 147847705944094459369156643)
                ·
                  refine ⟨221771558916141689053734965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147847705944094459369156643 221771558916141689053734965)
                  ·
                    refine ⟨20791083648388283348787653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 221771558916141689053734965 20791083648388283348787653)
                    ·
                      refine ⟨3898328184072803127897685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20791083648388283348787653 3898328184072803127897685)
                      ·
                        rfl

theorem cell23_7591967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_7591967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591967 prefixEnd_7591967 := by exact prefixLift 7591967
  have htrace : WordTrace (prefixWord ++ tailWord_7591967) baseStart_7591967 baseEnd_7591967 := by
    simpa [prefixWord, tailWord_7591967, baseEnd_7591967] using wordTrace_append hprefix tailTrace_7591967
  have hstable : (prefixWord ++ tailWord_7591967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591967).length < 2 ^ (prefixWord ++ tailWord_7591967).sum := by decide
  have hdescent : baseEnd_7591967 < baseStart_7591967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591978 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_7591978 : Nat := 118140960795 + 7591978 * 2 ^ 59
def prefixEnd_7591978 : Nat := 4983230072969 + 3 ^ 40 * 7591978 * 2
def baseEnd_7591978 : Nat := 3898333832360002584860135

theorem tailTrace_7591978 : CollatzResearch.WordTrace tailWord_7591978 prefixEnd_7591978 3898333832360002584860135 := by
  unfold tailWord_7591978
  simp only [CollatzResearch.WordTrace]
  refine ⟨69225546522391946864846147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184601457393045191639589725 69225546522391946864846147)
  ·
    refine ⟨103838319783587920297269221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69225546522391946864846147 103838319783587920297269221)
    ·
      refine ⟨19469684959422735055737979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103838319783587920297269221 19469684959422735055737979)
      ·
        refine ⟨29204527439134102583606969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19469684959422735055737979 29204527439134102583606969)
        ·
          refine ⟨21903395579350576937705227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29204527439134102583606969 21903395579350576937705227)
          ·
            refine ⟨32855093369025865406557841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21903395579350576937705227 32855093369025865406557841)
            ·
              refine ⟨24641320026769399054918381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32855093369025865406557841 24641320026769399054918381)
              ·
                refine ⟨9240495010038524645594393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24641320026769399054918381 9240495010038524645594393)
                ·
                  refine ⟨6930371257528893484195795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9240495010038524645594393 6930371257528893484195795)
                  ·
                    refine ⟨10395556886293340226293693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6930371257528893484195795 10395556886293340226293693)
                    ·
                      refine ⟨3898333832360002584860135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10395556886293340226293693 3898333832360002584860135)
                      ·
                        rfl

theorem cell23_7591978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_7591978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591978 prefixEnd_7591978 := by exact prefixLift 7591978
  have htrace : WordTrace (prefixWord ++ tailWord_7591978) baseStart_7591978 baseEnd_7591978 := by
    simpa [prefixWord, tailWord_7591978, baseEnd_7591978] using wordTrace_append hprefix tailTrace_7591978
  have hstable : (prefixWord ++ tailWord_7591978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591978).length < 2 ^ (prefixWord ++ tailWord_7591978).sum := by decide
  have hdescent : baseEnd_7591978 < baseStart_7591978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591987 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 5]
def baseStart_7591987 : Nat := 118140960795 + 7591987 * 2 ^ 59
def prefixEnd_7591987 : Nat := 4983230072969 + 3 ^ 40 * 7591987 * 2
def baseEnd_7591987 : Nat := 3898338453685893049647593

theorem tailTrace_7591987 : CollatzResearch.WordTrace tailWord_7591987 prefixEnd_7591987 3898338453685893049647593 := by
  unfold tailWord_7591987
  simp only [CollatzResearch.WordTrace]
  refine ⟨276902514346535181996462215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184601676231023454664308143 276902514346535181996462215)
  ·
    refine ⟨415353771519802772994693323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276902514346535181996462215 415353771519802772994693323)
    ·
      refine ⟨623030657279704159492039985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415353771519802772994693323 623030657279704159492039985)
      ·
        refine ⟨467272992959778119619029989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623030657279704159492039985 467272992959778119619029989)
        ·
          refine ⟨87613686179958397428568123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 467272992959778119619029989 87613686179958397428568123)
          ·
            refine ⟨131420529269937596142852185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87613686179958397428568123 131420529269937596142852185)
            ·
              refine ⟨98565396952453197107139139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131420529269937596142852185 98565396952453197107139139)
              ·
                refine ⟨147848095428679795660708709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98565396952453197107139139 147848095428679795660708709)
                ·
                  refine ⟨27721517892877461686382883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147848095428679795660708709 27721517892877461686382883)
                  ·
                    refine ⟨41582276839316192529574325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27721517892877461686382883 41582276839316192529574325)
                    ·
                      refine ⟨3898338453685893049647593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41582276839316192529574325 3898338453685893049647593)
                      ·
                        rfl

theorem cell23_7591987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_7591987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7591987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7591987 prefixEnd_7591987 := by exact prefixLift 7591987
  have htrace : WordTrace (prefixWord ++ tailWord_7591987) baseStart_7591987 baseEnd_7591987 := by
    simpa [prefixWord, tailWord_7591987, baseEnd_7591987] using wordTrace_append hprefix tailTrace_7591987
  have hstable : (prefixWord ++ tailWord_7591987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591987).length < 2 ^ (prefixWord ++ tailWord_7591987).sum := by decide
  have hdescent : baseEnd_7591987 < baseStart_7591987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592007 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 9]
def baseStart_7592007 : Nat := 118140960795 + 7592007 * 2 ^ 59
def prefixEnd_7592007 : Nat := 4983230072969 + 3 ^ 40 * 7592007 * 2
def baseEnd_7592007 : Nat := 433149858144331441266389

theorem tailTrace_7592007 : CollatzResearch.WordTrace tailWord_7592007 prefixEnd_7592007 433149858144331441266389 := by
  unfold tailWord_7592007
  simp only [CollatzResearch.WordTrace]
  refine ⟨276903243806462725412190275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184602162537641816941460183 276903243806462725412190275)
  ·
    refine ⟨415354865709694088118285413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276903243806462725412190275 415354865709694088118285413)
    ·
      refine ⟨77879037320567641522178515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415354865709694088118285413 77879037320567641522178515)
      ·
        refine ⟨116818555980851462283267773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77879037320567641522178515 116818555980851462283267773)
        ·
          refine ⟨43806958492819298356225415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116818555980851462283267773 43806958492819298356225415)
          ·
            refine ⟨65710437739228947534338123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43806958492819298356225415 65710437739228947534338123)
            ·
              refine ⟨98565656608843421301507185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65710437739228947534338123 98565656608843421301507185)
              ·
                refine ⟨73924242456632565976130389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98565656608843421301507185 73924242456632565976130389)
                ·
                  refine ⟨433149858144331441266389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73924242456632565976130389 433149858144331441266389)
                  ·
                    rfl

theorem cell23_7592007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 9].length) (baseStart_7592007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592007 prefixEnd_7592007 := by exact prefixLift 7592007
  have htrace : WordTrace (prefixWord ++ tailWord_7592007) baseStart_7592007 baseEnd_7592007 := by
    simpa [prefixWord, tailWord_7592007, baseEnd_7592007] using wordTrace_append hprefix tailTrace_7592007
  have hstable : (prefixWord ++ tailWord_7592007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592007).length < 2 ^ (prefixWord ++ tailWord_7592007).sum := by decide
  have hdescent : baseEnd_7592007 < baseStart_7592007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592014 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_7592014 : Nat := 118140960795 + 7592014 * 2 ^ 59
def prefixEnd_7592014 : Nat := 4983230072969 + 3 ^ 40 * 7592014 * 2
def baseEnd_7592014 : Nat := 3898352317663564444009969

theorem tailTrace_7592014 : CollatzResearch.WordTrace tailWord_7592014 prefixEnd_7592014 3898352317663564444009969 := by
  unfold tailWord_7592014
  simp only [CollatzResearch.WordTrace]
  refine ⟨34612937389679670700961887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184602332744958243738463397 34612937389679670700961887)
  ·
    refine ⟨51919406084519506051442831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34612937389679670700961887 51919406084519506051442831)
    ·
      refine ⟨77879109126779259077164247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51919406084519506051442831 77879109126779259077164247)
      ·
        refine ⟨116818663690168888615746371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77879109126779259077164247 116818663690168888615746371)
        ·
          refine ⟨175227995535253332923619557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116818663690168888615746371 175227995535253332923619557)
          ·
            refine ⟨32855249162859999923178667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175227995535253332923619557 32855249162859999923178667)
            ·
              refine ⟨49282873744289999884768001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32855249162859999923178667 49282873744289999884768001)
              ·
                refine ⟨36962155308217499913576001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49282873744289999884768001 36962155308217499913576001)
                ·
                  refine ⟨27721616481163124935182001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36962155308217499913576001 27721616481163124935182001)
                  ·
                    refine ⟨20791212360872343701386501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27721616481163124935182001 20791212360872343701386501)
                    ·
                      refine ⟨3898352317663564444009969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20791212360872343701386501 3898352317663564444009969)
                      ·
                        rfl

theorem cell23_7592014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_7592014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592014 prefixEnd_7592014 := by exact prefixLift 7592014
  have htrace : WordTrace (prefixWord ++ tailWord_7592014) baseStart_7592014 baseEnd_7592014 := by
    simpa [prefixWord, tailWord_7592014, baseEnd_7592014] using wordTrace_append hprefix tailTrace_7592014
  have hstable : (prefixWord ++ tailWord_7592014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592014).length < 2 ^ (prefixWord ++ tailWord_7592014).sum := by decide
  have hdescent : baseEnd_7592014 < baseStart_7592014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592024 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 7]
def baseStart_7592024 : Nat := 118140960795 + 7592024 * 2 ^ 59
def prefixEnd_7592024 : Nat := 4983230072969 + 3 ^ 40 * 7592024 * 2
def baseEnd_7592024 : Nat := 433150828052234378320547

theorem tailTrace_7592024 : CollatzResearch.WordTrace tailWord_7592024 prefixEnd_7592024 433150828052234378320547 := by
  unfold tailWord_7592024
  simp only [CollatzResearch.WordTrace]
  refine ⟨138451931923700568657779563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184602575898267424877039417 138451931923700568657779563)
  ·
    refine ⟨207677897885550852986669345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138451931923700568657779563 207677897885550852986669345)
    ·
      refine ⟨155758423414163139740002009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207677897885550852986669345 155758423414163139740002009)
      ·
        refine ⟨116818817560622354805001507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155758423414163139740002009 116818817560622354805001507)
        ·
          refine ⟨175228226340933532207502261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116818817560622354805001507 175228226340933532207502261)
          ·
            refine ⟨16427646219462518644453337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175228226340933532207502261 16427646219462518644453337)
            ·
              refine ⟨12320734664596888983340003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16427646219462518644453337 12320734664596888983340003)
              ·
                refine ⟨18481101996895333475010005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12320734664596888983340003 18481101996895333475010005)
                ·
                  refine ⟨433150828052234378320547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18481101996895333475010005 433150828052234378320547)
                  ·
                    rfl

theorem cell23_7592024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 7].length) (baseStart_7592024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592024 prefixEnd_7592024 := by exact prefixLift 7592024
  have htrace : WordTrace (prefixWord ++ tailWord_7592024) baseStart_7592024 baseEnd_7592024 := by
    simpa [prefixWord, tailWord_7592024, baseEnd_7592024] using wordTrace_append hprefix tailTrace_7592024
  have hstable : (prefixWord ++ tailWord_7592024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592024).length < 2 ^ (prefixWord ++ tailWord_7592024).sum := by decide
  have hdescent : baseEnd_7592024 < baseStart_7592024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592151 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 1, 5, 2]
def baseStart_7592151 : Nat := 118140960795 + 7592151 * 2 ^ 59
def prefixEnd_7592151 : Nat := 4983230072969 + 3 ^ 40 * 7592151 * 2
def baseEnd_7592151 : Nat := 3898422664513230407996839

theorem tailTrace_7592151 : CollatzResearch.WordTrace tailWord_7592151 prefixEnd_7592151 3898422664513230407996839 := by
  unfold tailWord_7592151
  simp only [CollatzResearch.WordTrace]
  refine ⟨276908495917941038005432307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184605663945294025336954871 276908495917941038005432307)
  ·
    refine ⟨415362743876911557008148461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276908495917941038005432307 415362743876911557008148461)
    ·
      refine ⟨155761028953841833878055673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415362743876911557008148461 155761028953841833878055673)
      ·
        refine ⟨116820771715381375408541755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155761028953841833878055673 116820771715381375408541755)
        ·
          refine ⟨175231157573072063112812633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116820771715381375408541755 175231157573072063112812633)
          ·
            refine ⟨131423368179804047334609475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175231157573072063112812633 131423368179804047334609475)
            ·
              refine ⟨197135052269706071001914213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131423368179804047334609475 197135052269706071001914213)
              ·
                refine ⟨36962822300569888312858915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197135052269706071001914213 36962822300569888312858915)
                ·
                  refine ⟨55444233450854832469288373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36962822300569888312858915 55444233450854832469288373)
                  ·
                    refine ⟨5197896886017640543995785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55444233450854832469288373 5197896886017640543995785)
                    ·
                      refine ⟨3898422664513230407996839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5197896886017640543995785 3898422664513230407996839)
                      ·
                        rfl

theorem cell23_7592151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_7592151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592151 prefixEnd_7592151 := by exact prefixLift 7592151
  have htrace : WordTrace (prefixWord ++ tailWord_7592151) baseStart_7592151 baseEnd_7592151 := by
    simpa [prefixWord, tailWord_7592151, baseEnd_7592151] using wordTrace_append hprefix tailTrace_7592151
  have hstable : (prefixWord ++ tailWord_7592151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592151).length < 2 ^ (prefixWord ++ tailWord_7592151).sum := by decide
  have hdescent : baseEnd_7592151 < baseStart_7592151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592161 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 1, 5]
def baseStart_7592161 : Nat := 118140960795 + 7592161 * 2 ^ 59
def prefixEnd_7592161 : Nat := 4983230072969 + 3 ^ 40 * 7592161 * 2
def baseEnd_7592161 : Nat := 1299475933106591789623931

theorem tailTrace_7592161 : CollatzResearch.WordTrace tailWord_7592161 prefixEnd_7592161 1299475933106591789623931 := by
  unfold tailWord_7592161
  simp only [CollatzResearch.WordTrace]
  refine ⟨276908860647904809713296337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184605907098603206475530891 276908860647904809713296337)
  ·
    refine ⟨207681645485928607284972253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276908860647904809713296337 207681645485928607284972253)
    ·
      refine ⟨77880617057223227731864595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207681645485928607284972253 77880617057223227731864595)
      ·
        refine ⟨116820925585834841597796893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77880617057223227731864595 116820925585834841597796893)
        ·
          refine ⟨43807847094688065599173835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116820925585834841597796893 43807847094688065599173835)
          ·
            refine ⟨65711770642032098398760753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43807847094688065599173835 65711770642032098398760753)
            ·
              refine ⟨49283827981524073799070565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65711770642032098398760753 49283827981524073799070565)
              ·
                refine ⟨9240717746535763837325731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49283827981524073799070565 9240717746535763837325731)
                ·
                  refine ⟨13861076619803645755988597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9240717746535763837325731 13861076619803645755988597)
                  ·
                    refine ⟨1299475933106591789623931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13861076619803645755988597 1299475933106591789623931)
                    ·
                      rfl

theorem cell23_7592161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_7592161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592161 prefixEnd_7592161 := by exact prefixLift 7592161
  have htrace : WordTrace (prefixWord ++ tailWord_7592161) baseStart_7592161 baseEnd_7592161 := by
    simpa [prefixWord, tailWord_7592161, baseEnd_7592161] using wordTrace_append hprefix tailTrace_7592161
  have hstable : (prefixWord ++ tailWord_7592161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592161).length < 2 ^ (prefixWord ++ tailWord_7592161).sum := by decide
  have hdescent : baseEnd_7592161 < baseStart_7592161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592162 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7592162 : Nat := 118140960795 + 7592162 * 2 ^ 59
def prefixEnd_7592162 : Nat := 4983230072969 + 3 ^ 40 * 7592162 * 2
def baseEnd_7592162 : Nat := 3898428312800429864959289

theorem tailTrace_7592162 : CollatzResearch.WordTrace tailWord_7592162 prefixEnd_7592162 3898428312800429864959289 := by
  unfold tailWord_7592162
  simp only [CollatzResearch.WordTrace]
  refine ⟨69227224280225296721020685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184605931413934124589388493 69227224280225296721020685)
  ·
    refine ⟨25960209105084486270382757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69227224280225296721020685 25960209105084486270382757)
    ·
      refine ⟨4867539207203341175696767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25960209105084486270382757 4867539207203341175696767)
      ·
        refine ⟨7301308810805011763545151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867539207203341175696767 7301308810805011763545151)
        ·
          refine ⟨10951963216207517645317727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301308810805011763545151 10951963216207517645317727)
          ·
            refine ⟨16427944824311276467976591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10951963216207517645317727 16427944824311276467976591)
            ·
              refine ⟨24641917236466914701964887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16427944824311276467976591 24641917236466914701964887)
              ·
                refine ⟨36962875854700372052947331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24641917236466914701964887 36962875854700372052947331)
                ·
                  refine ⟨55444313782050558079420997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36962875854700372052947331 55444313782050558079420997)
                  ·
                    refine ⟨10395808834134479639891437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55444313782050558079420997 10395808834134479639891437)
                    ·
                      refine ⟨3898428312800429864959289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10395808834134479639891437 3898428312800429864959289)
                      ·
                        rfl

theorem cell23_7592162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7592162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592162 prefixEnd_7592162 := by exact prefixLift 7592162
  have htrace : WordTrace (prefixWord ++ tailWord_7592162) baseStart_7592162 baseEnd_7592162 := by
    simpa [prefixWord, tailWord_7592162, baseEnd_7592162] using wordTrace_append hprefix tailTrace_7592162
  have hstable : (prefixWord ++ tailWord_7592162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592162).length < 2 ^ (prefixWord ++ tailWord_7592162).sum := by decide
  have hdescent : baseEnd_7592162 < baseStart_7592162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592168 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_7592168 : Nat := 118140960795 + 7592168 * 2 ^ 59
def prefixEnd_7592168 : Nat := 4983230072969 + 3 ^ 40 * 7592168 * 2
def baseEnd_7592168 : Nat := 3898431393684356841484261

theorem tailTrace_7592168 : CollatzResearch.WordTrace tailWord_7592168 prefixEnd_7592168 3898431393684356841484261 := by
  unfold tailWord_7592168
  simp only [CollatzResearch.WordTrace]
  refine ⟨138454557979439724954400579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184606077305919633272534105 138454557979439724954400579)
  ·
    refine ⟨207681836969159587431600869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138454557979439724954400579 207681836969159587431600869)
    ·
      refine ⟨38940344431717422643425163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207681836969159587431600869 38940344431717422643425163)
      ·
        refine ⟨58410516647576133965137745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38940344431717422643425163 58410516647576133965137745)
        ·
          refine ⟨43807887485682100473853309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58410516647576133965137745 43807887485682100473853309)
          ·
            refine ⟨16427957807130787677694991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43807887485682100473853309 16427957807130787677694991)
            ·
              refine ⟨24641936710696181516542487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16427957807130787677694991 24641936710696181516542487)
              ·
                refine ⟨36962905066044272274813731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24641936710696181516542487 36962905066044272274813731)
                ·
                  refine ⟨55444357599066408412220597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36962905066044272274813731 55444357599066408412220597)
                  ·
                    refine ⟨5197908524912475788645681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55444357599066408412220597 5197908524912475788645681)
                    ·
                      refine ⟨3898431393684356841484261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5197908524912475788645681 3898431393684356841484261)
                      ·
                        rfl

theorem cell23_7592168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_7592168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592168 prefixEnd_7592168 := by exact prefixLift 7592168
  have htrace : WordTrace (prefixWord ++ tailWord_7592168) baseStart_7592168 baseEnd_7592168 := by
    simpa [prefixWord, tailWord_7592168, baseEnd_7592168] using wordTrace_append hprefix tailTrace_7592168
  have hstable : (prefixWord ++ tailWord_7592168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592168).length < 2 ^ (prefixWord ++ tailWord_7592168).sum := by decide
  have hdescent : baseEnd_7592168 < baseStart_7592168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592175 : List Nat := [1, 1, 2, 1, 6, 1, 1, 5, 1, 1, 3]
def baseStart_7592175 : Nat := 118140960795 + 7592175 * 2 ^ 59
def prefixEnd_7592175 : Nat := 4983230072969 + 3 ^ 40 * 7592175 * 2
def baseEnd_7592175 : Nat := 3898434988048938314096729

theorem tailTrace_7592175 : CollatzResearch.WordTrace tailWord_7592175 prefixEnd_7592175 3898434988048938314096729 := by
  unfold tailWord_7592175
  simp only [CollatzResearch.WordTrace]
  refine ⟨276909371269854090104305979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184606247513236060069537319 276909371269854090104305979)
  ·
    refine ⟨415364056904781135156458969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276909371269854090104305979 415364056904781135156458969)
    ·
      refine ⟨311523042678585851367344227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415364056904781135156458969 311523042678585851367344227)
      ·
        refine ⟨467284564017878777051016341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311523042678585851367344227 467284564017878777051016341)
        ·
          refine ⟨21903963938338067674266391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 467284564017878777051016341 21903963938338067674266391)
          ·
            refine ⟨32855945907507101511399587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21903963938338067674266391 32855945907507101511399587)
            ·
              refine ⟨49283918861260652267099381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32855945907507101511399587 49283918861260652267099381)
              ·
                refine ⟨4620367393243186150040567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49283918861260652267099381 4620367393243186150040567)
                ·
                  refine ⟨6930551089864779225060851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4620367393243186150040567 6930551089864779225060851)
                  ·
                    refine ⟨10395826634797168837591277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6930551089864779225060851 10395826634797168837591277)
                    ·
                      refine ⟨3898434988048938314096729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10395826634797168837591277 3898434988048938314096729)
                      ·
                        rfl

theorem cell23_7592175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 1, 1, 3].length) (baseStart_7592175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592175 prefixEnd_7592175 := by exact prefixLift 7592175
  have htrace : WordTrace (prefixWord ++ tailWord_7592175) baseStart_7592175 baseEnd_7592175 := by
    simpa [prefixWord, tailWord_7592175, baseEnd_7592175] using wordTrace_append hprefix tailTrace_7592175
  have hstable : (prefixWord ++ tailWord_7592175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592175).length < 2 ^ (prefixWord ++ tailWord_7592175).sum := by decide
  have hdescent : baseEnd_7592175 < baseStart_7592175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592178 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_7592178 : Nat := 118140960795 + 7592178 * 2 ^ 59
def prefixEnd_7592178 : Nat := 4983230072969 + 3 ^ 40 * 7592178 * 2
def baseEnd_7592178 : Nat := 1299478842830300600786405

theorem tailTrace_7592178 : CollatzResearch.WordTrace tailWord_7592178 prefixEnd_7592178 1299478842830300600786405 := by
  unfold tailWord_7592178
  simp only [CollatzResearch.WordTrace]
  refine ⟨69227370172210805404166297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184606320459228814411110125 69227370172210805404166297)
  ·
    refine ⟨51920527629158104053124723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69227370172210805404166297 51920527629158104053124723)
    ·
      refine ⟨77880791443737156079687085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51920527629158104053124723 77880791443737156079687085)
      ·
        refine ⟨29205296791401433529882657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77880791443737156079687085 29205296791401433529882657)
        ·
          refine ⟨21903972593551075147411993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29205296791401433529882657 21903972593551075147411993)
          ·
            refine ⟨16427979445163306360558995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21903972593551075147411993 16427979445163306360558995)
            ·
              refine ⟨24641969167744959540838493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16427979445163306360558995 24641969167744959540838493)
              ·
                refine ⟨9240738437904359827814435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24641969167744959540838493 9240738437904359827814435)
                ·
                  refine ⟨13861107656856539741721653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9240738437904359827814435 13861107656856539741721653)
                  ·
                    refine ⟨1299478842830300600786405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13861107656856539741721653 1299478842830300600786405)
                    ·
                      rfl

theorem cell23_7592178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_7592178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592178 prefixEnd_7592178 := by exact prefixLift 7592178
  have htrace : WordTrace (prefixWord ++ tailWord_7592178) baseStart_7592178 baseEnd_7592178 := by
    simpa [prefixWord, tailWord_7592178, baseEnd_7592178] using wordTrace_append hprefix tailTrace_7592178
  have hstable : (prefixWord ++ tailWord_7592178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592178).length < 2 ^ (prefixWord ++ tailWord_7592178).sum := by decide
  have hdescent : baseEnd_7592178 < baseStart_7592178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592184 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_7592184 : Nat := 118140960795 + 7592184 * 2 ^ 59
def prefixEnd_7592184 : Nat := 4983230072969 + 3 ^ 40 * 7592184 * 2
def baseEnd_7592184 : Nat := 3898439609374828778884187

theorem tailTrace_7592184 : CollatzResearch.WordTrace tailWord_7592184 prefixEnd_7592184 3898439609374828778884187 := by
  unfold tailWord_7592184
  simp only [CollatzResearch.WordTrace]
  refine ⟨138454849763410742320691803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184606466351214323094255737 138454849763410742320691803)
  ·
    refine ⟨207682274645116113481037705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138454849763410742320691803 207682274645116113481037705)
    ·
      refine ⟨155761705983837085110778279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207682274645116113481037705 155761705983837085110778279)
      ·
        refine ⟨233642558975755627666167419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155761705983837085110778279 233642558975755627666167419)
        ·
          refine ⟨350463838463633441499251129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233642558975755627666167419 350463838463633441499251129)
          ·
            refine ⟨262847878847725081124438347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350463838463633441499251129 262847878847725081124438347)
            ·
              refine ⟨394271818271587621686657521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262847878847725081124438347 394271818271587621686657521)
              ·
                refine ⟨295703863703690716264993141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394271818271587621686657521 295703863703690716264993141)
                ·
                  refine ⟨27722237222221004649843107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 295703863703690716264993141 27722237222221004649843107)
                  ·
                    refine ⟨41583355833331506974764661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27722237222221004649843107 41583355833331506974764661)
                    ·
                      refine ⟨3898439609374828778884187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41583355833331506974764661 3898439609374828778884187)
                      ·
                        rfl

theorem cell23_7592184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_7592184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592184 prefixEnd_7592184 := by exact prefixLift 7592184
  have htrace : WordTrace (prefixWord ++ tailWord_7592184) baseStart_7592184 baseEnd_7592184 := by
    simpa [prefixWord, tailWord_7592184, baseEnd_7592184] using wordTrace_append hprefix tailTrace_7592184
  have hstable : (prefixWord ++ tailWord_7592184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592184).length < 2 ^ (prefixWord ++ tailWord_7592184).sum := by decide
  have hdescent : baseEnd_7592184 < baseStart_7592184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592191 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 4, 4]
def baseStart_7592191 : Nat := 118140960795 + 7592191 * 2 ^ 59
def prefixEnd_7592191 : Nat := 4983230072969 + 3 ^ 40 * 7592191 * 2
def baseEnd_7592191 : Nat := 1299481067913136750498885

theorem tailTrace_7592191 : CollatzResearch.WordTrace tailWord_7592191 prefixEnd_7592191 1299481067913136750498885 := by
  unfold tailWord_7592191
  simp only [CollatzResearch.WordTrace]
  refine ⟨276909954837796124836888427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184606636558530749891258951 276909954837796124836888427)
  ·
    refine ⟨415364932256694187255332641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276909954837796124836888427 415364932256694187255332641)
    ·
      refine ⟨311523699192520640441499481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415364932256694187255332641 311523699192520640441499481)
      ·
        refine ⟨233642774394390480331124611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311523699192520640441499481 233642774394390480331124611)
        ·
          refine ⟨350464161591585720496686917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233642774394390480331124611 350464161591585720496686917)
          ·
            refine ⟨65712030298422322593128797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350464161591585720496686917 65712030298422322593128797)
            ·
              refine ⟨24642011361908370972423299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65712030298422322593128797 24642011361908370972423299)
              ·
                refine ⟨36963017042862556458634949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24642011361908370972423299 36963017042862556458634949)
                ·
                  refine ⟨6930565695536729335994053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36963017042862556458634949 6930565695536729335994053)
                  ·
                    refine ⟨1299481067913136750498885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6930565695536729335994053 1299481067913136750498885)
                    ·
                      rfl

theorem cell23_7592191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 4].length) (baseStart_7592191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592191 prefixEnd_7592191 := by exact prefixLift 7592191
  have htrace : WordTrace (prefixWord ++ tailWord_7592191) baseStart_7592191 baseEnd_7592191 := by
    simpa [prefixWord, tailWord_7592191, baseEnd_7592191] using wordTrace_append hprefix tailTrace_7592191
  have hstable : (prefixWord ++ tailWord_7592191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592191).length < 2 ^ (prefixWord ++ tailWord_7592191).sum := by decide
  have hdescent : baseEnd_7592191 < baseStart_7592191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592201 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 5]
def baseStart_7592201 : Nat := 118140960795 + 7592201 * 2 ^ 59
def prefixEnd_7592201 : Nat := 4983230072969 + 3 ^ 40 * 7592201 * 2
def baseEnd_7592201 : Nat := 3898448338545955212371609

theorem tailTrace_7592201 : CollatzResearch.WordTrace tailWord_7592201 prefixEnd_7592201 3898448338545955212371609 := by
  unfold tailWord_7592201
  simp only [CollatzResearch.WordTrace]
  refine ⟨276910319567759896544752457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184606879711839931029834971 276910319567759896544752457)
  ·
    refine ⟨207682739675819922408564343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276910319567759896544752457 207682739675819922408564343)
    ·
      refine ⟨311524109513729883612846515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207682739675819922408564343 311524109513729883612846515)
      ·
        refine ⟨467286164270594825419269773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311524109513729883612846515 467286164270594825419269773)
        ·
          refine ⟨175232311601473059532226165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467286164270594825419269773 175232311601473059532226165)
          ·
            refine ⟨16428029212638099331146203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175232311601473059532226165 16428029212638099331146203)
            ·
              refine ⟨24642043818957148996719305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16428029212638099331146203 24642043818957148996719305)
              ·
                refine ⟨18481532864217861747539479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24642043818957148996719305 18481532864217861747539479)
                ·
                  refine ⟨27722299296326792621309219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18481532864217861747539479 27722299296326792621309219)
                  ·
                    refine ⟨41583448944490188931963829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27722299296326792621309219 41583448944490188931963829)
                    ·
                      refine ⟨3898448338545955212371609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41583448944490188931963829 3898448338545955212371609)
                      ·
                        rfl

theorem cell23_7592201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_7592201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592201 prefixEnd_7592201 := by exact prefixLift 7592201
  have htrace : WordTrace (prefixWord ++ tailWord_7592201) baseStart_7592201 baseEnd_7592201 := by
    simpa [prefixWord, tailWord_7592201, baseEnd_7592201] using wordTrace_append hprefix tailTrace_7592201
  have hstable : (prefixWord ++ tailWord_7592201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592201).length < 2 ^ (prefixWord ++ tailWord_7592201).sum := by decide
  have hdescent : baseEnd_7592201 < baseStart_7592201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592204 : List Nat := [2, 2, 1, 2, 2, 2, 2, 10]
def baseStart_7592204 : Nat := 118140960795 + 7592204 * 2 ^ 59
def prefixEnd_7592204 : Nat := 4983230072969 + 3 ^ 40 * 7592204 * 2
def baseEnd_7592204 : Nat := 144387032555108100023485

theorem tailTrace_7592204 : CollatzResearch.WordTrace tailWord_7592204 prefixEnd_7592204 144387032555108100023485 := by
  unfold tailWord_7592204
  simp only [CollatzResearch.WordTrace]
  refine ⟨138455214493374514028555833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184606952657832685371407777 138455214493374514028555833)
  ·
    refine ⟨103841410870030885521416875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138455214493374514028555833 103841410870030885521416875)
    ·
      refine ⟨155762116305046328282125313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103841410870030885521416875 155762116305046328282125313)
      ·
        refine ⟨116821587228784746211593985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155762116305046328282125313 116821587228784746211593985)
        ·
          refine ⟨87616190421588559658695489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116821587228784746211593985 87616190421588559658695489)
          ·
            refine ⟨65712142816191419744021617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87616190421588559658695489 65712142816191419744021617)
            ·
              refine ⟨49284107112143564808016213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65712142816191419744021617 49284107112143564808016213)
              ·
                refine ⟨144387032555108100023485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49284107112143564808016213 144387032555108100023485)
                ·
                  rfl

theorem cell23_7592204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 10].length) (baseStart_7592204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592204 prefixEnd_7592204 := by exact prefixLift 7592204
  have htrace : WordTrace (prefixWord ++ tailWord_7592204) baseStart_7592204 baseEnd_7592204 := by
    simpa [prefixWord, tailWord_7592204, baseEnd_7592204] using wordTrace_append hprefix tailTrace_7592204
  have hstable : (prefixWord ++ tailWord_7592204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592204).length < 2 ^ (prefixWord ++ tailWord_7592204).sum := by decide
  have hdescent : baseEnd_7592204 < baseStart_7592204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592215 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 3, 2, 2]
def baseStart_7592215 : Nat := 118140960795 + 7592215 * 2 ^ 59
def prefixEnd_7592215 : Nat := 4983230072969 + 3 ^ 40 * 7592215 * 2
def baseEnd_7592215 : Nat := 3898455527275118157596545

theorem tailTrace_7592215 : CollatzResearch.WordTrace tailWord_7592215 prefixEnd_7592215 3898455527275118157596545 := by
  unfold tailWord_7592215
  simp only [CollatzResearch.WordTrace]
  refine ⟨276910830189709176935762099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184607220126472784623841399 276910830189709176935762099)
  ·
    refine ⟨415366245284563765403643149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276910830189709176935762099 415366245284563765403643149)
    ·
      refine ⟨155762341981711412026366181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415366245284563765403643149 155762341981711412026366181)
      ·
        refine ⟨29205439121570889754943659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155762341981711412026366181 29205439121570889754943659)
        ·
          refine ⟨43808158682356334632415489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29205439121570889754943659 43808158682356334632415489)
          ·
            refine ⟨32856119011767250974311617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43808158682356334632415489 32856119011767250974311617)
            ·
              refine ⟨24642089258825438230733713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32856119011767250974311617 24642089258825438230733713)
              ·
                refine ⟨18481566944119078673050285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24642089258825438230733713 18481566944119078673050285)
                ·
                  refine ⟨6930587604044654502393857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18481566944119078673050285 6930587604044654502393857)
                  ·
                    refine ⟨5197940703033490876795393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6930587604044654502393857 5197940703033490876795393)
                    ·
                      refine ⟨3898455527275118157596545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5197940703033490876795393 3898455527275118157596545)
                      ·
                        rfl

theorem cell23_7592215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_7592215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592215 prefixEnd_7592215 := by exact prefixLift 7592215
  have htrace : WordTrace (prefixWord ++ tailWord_7592215) baseStart_7592215 baseEnd_7592215 := by
    simpa [prefixWord, tailWord_7592215, baseEnd_7592215] using wordTrace_append hprefix tailTrace_7592215
  have hstable : (prefixWord ++ tailWord_7592215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592215).length < 2 ^ (prefixWord ++ tailWord_7592215).sum := by decide
  have hdescent : baseEnd_7592215 < baseStart_7592215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592248 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 4, 1, 3]
def baseStart_7592248 : Nat := 118140960795 + 7592248 * 2 ^ 59
def prefixEnd_7592248 : Nat := 4983230072969 + 3 ^ 40 * 7592248 * 2
def baseEnd_7592248 : Nat := 3898472472136716528483893

theorem tailTrace_7592248 : CollatzResearch.WordTrace tailWord_7592248 prefixEnd_7592248 3898472472136716528483893 := by
  unfold tailWord_7592248
  simp only [CollatzResearch.WordTrace]
  refine ⟨138456016899294811785856699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184608022532393082381142265 138456016899294811785856699)
  ·
    refine ⟨207684025348942217678785049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138456016899294811785856699 207684025348942217678785049)
    ·
      refine ⟨155763019011706663259088787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207684025348942217678785049 155763019011706663259088787)
      ·
        refine ⟨233644528517559994888633181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155763019011706663259088787 233644528517559994888633181)
        ·
          refine ⟨87616698194084998083237443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233644528517559994888633181 87616698194084998083237443)
          ·
            refine ⟨131425047291127497124856165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87616698194084998083237443 131425047291127497124856165)
            ·
              refine ⟨24642196367086405710910531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131425047291127497124856165 24642196367086405710910531)
              ·
                refine ⟨36963294550629608566365797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24642196367086405710910531 36963294550629608566365797)
                ·
                  refine ⟨6930617728243051606193587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36963294550629608566365797 6930617728243051606193587)
                  ·
                    refine ⟨10395926592364577409290381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6930617728243051606193587 10395926592364577409290381)
                    ·
                      refine ⟨3898472472136716528483893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10395926592364577409290381 3898472472136716528483893)
                      ·
                        rfl

theorem cell23_7592248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_7592248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592248 prefixEnd_7592248 := by exact prefixLift 7592248
  have htrace : WordTrace (prefixWord ++ tailWord_7592248) baseStart_7592248 baseEnd_7592248 := by
    simpa [prefixWord, tailWord_7592248, baseEnd_7592248] using wordTrace_append hprefix tailTrace_7592248
  have hstable : (prefixWord ++ tailWord_7592248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592248).length < 2 ^ (prefixWord ++ tailWord_7592248).sum := by decide
  have hdescent : baseEnd_7592248 < baseStart_7592248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592286 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_7592286 : Nat := 118140960795 + 7592286 * 2 ^ 59
def prefixEnd_7592286 : Nat := 4983230072969 + 3 ^ 40 * 7592286 * 2
def baseEnd_7592286 : Nat := 3898491984401587379808719

theorem tailTrace_7592286 : CollatzResearch.WordTrace tailWord_7592286 prefixEnd_7592286 3898491984401587379808719 := by
  unfold tailWord_7592286
  simp only [CollatzResearch.WordTrace]
  refine ⟨34614177471556494507699589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184608946514967970707731141 34614177471556494507699589)
  ·
    refine ⟨6490158275916842720193673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34614177471556494507699589 6490158275916842720193673)
    ·
      refine ⟨4867618706937632040145255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6490158275916842720193673 4867618706937632040145255)
      ·
        refine ⟨7301428060406448060217883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867618706937632040145255 7301428060406448060217883)
        ·
          refine ⟨10952142090609672090326825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301428060406448060217883 10952142090609672090326825)
          ·
            refine ⟨8214106567957254067745119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10952142090609672090326825 8214106567957254067745119)
            ·
              refine ⟨12321159851935881101617679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8214106567957254067745119 12321159851935881101617679)
              ·
                refine ⟨18481739777903821652426519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12321159851935881101617679 18481739777903821652426519)
                ·
                  refine ⟨27722609666855732478639779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18481739777903821652426519 27722609666855732478639779)
                  ·
                    refine ⟨41583914500283598717959669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27722609666855732478639779 41583914500283598717959669)
                    ·
                      refine ⟨3898491984401587379808719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41583914500283598717959669 3898491984401587379808719)
                      ·
                        rfl

theorem cell23_7592286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_7592286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592286 prefixEnd_7592286 := by exact prefixLift 7592286
  have htrace : WordTrace (prefixWord ++ tailWord_7592286) baseStart_7592286 baseEnd_7592286 := by
    simpa [prefixWord, tailWord_7592286, baseEnd_7592286] using wordTrace_append hprefix tailTrace_7592286
  have hstable : (prefixWord ++ tailWord_7592286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592286).length < 2 ^ (prefixWord ++ tailWord_7592286).sum := by decide
  have hdescent : baseEnd_7592286 < baseStart_7592286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592291 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 5]
def baseStart_7592291 : Nat := 118140960795 + 7592291 * 2 ^ 59
def prefixEnd_7592291 : Nat := 4983230072969 + 3 ^ 40 * 7592291 * 2
def baseEnd_7592291 : Nat := 3898494551804859860246195

theorem tailTrace_7592291 : CollatzResearch.WordTrace tailWord_7592291 prefixEnd_7592291 3898494551804859860246195 := by
  unfold tailWord_7592291
  simp only [CollatzResearch.WordTrace]
  refine ⟨276913602137433841915528727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184609068091622561277019151 276913602137433841915528727)
  ·
    refine ⟨415370403206150762873293091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276913602137433841915528727 415370403206150762873293091)
    ·
      refine ⟨623055604809226144309939637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415370403206150762873293091 623055604809226144309939637)
      ·
        refine ⟨58411462950864951029056841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 623055604809226144309939637 58411462950864951029056841)
        ·
          refine ⟨43808597213148713271792631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58411462950864951029056841 43808597213148713271792631)
          ·
            refine ⟨65712895819723069907688947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43808597213148713271792631 65712895819723069907688947)
            ·
              refine ⟨98569343729584604861533421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65712895819723069907688947 98569343729584604861533421)
              ·
                refine ⟨36963503898594226823075033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98569343729584604861533421 36963503898594226823075033)
                ·
                  refine ⟨27722627923945670117306275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36963503898594226823075033 27722627923945670117306275)
                  ·
                    refine ⟨41583941885918505175959413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27722627923945670117306275 41583941885918505175959413)
                    ·
                      refine ⟨3898494551804859860246195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41583941885918505175959413 3898494551804859860246195)
                      ·
                        rfl

theorem cell23_7592291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_7592291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592291 prefixEnd_7592291 := by exact prefixLift 7592291
  have htrace : WordTrace (prefixWord ++ tailWord_7592291) baseStart_7592291 baseEnd_7592291 := by
    simpa [prefixWord, tailWord_7592291, baseEnd_7592291] using wordTrace_append hprefix tailTrace_7592291
  have hstable : (prefixWord ++ tailWord_7592291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592291).length < 2 ^ (prefixWord ++ tailWord_7592291).sum := by decide
  have hdescent : baseEnd_7592291 < baseStart_7592291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592292 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 1, 3, 2]
def baseStart_7592292 : Nat := 118140960795 + 7592292 * 2 ^ 59
def prefixEnd_7592292 : Nat := 4983230072969 + 3 ^ 40 * 7592292 * 2
def baseEnd_7592292 : Nat := 3898495065285514356333691

theorem tailTrace_7592292 : CollatzResearch.WordTrace tailWord_7592292 prefixEnd_7592292 3898495065285514356333691 := by
  unfold tailWord_7592292
  simp only [CollatzResearch.WordTrace]
  refine ⟨138456819305215109543157565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184609092406953479390876753 138456819305215109543157565)
  ·
    refine ⟨51921307239455666078684087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138456819305215109543157565 51921307239455666078684087)
    ·
      refine ⟨77881960859183499118026131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51921307239455666078684087 77881960859183499118026131)
      ·
        refine ⟨116822941288775248677039197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77881960859183499118026131 116822941288775248677039197)
        ·
          refine ⟨43808602983290718253889699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116822941288775248677039197 43808602983290718253889699)
          ·
            refine ⟨65712904474936077380834549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43808602983290718253889699 65712904474936077380834549)
            ·
              refine ⟨6160584794525257254453239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65712904474936077380834549 6160584794525257254453239)
              ·
                refine ⟨9240877191787885881679859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6160584794525257254453239 9240877191787885881679859)
                ·
                  refine ⟨13861315787681828822519789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9240877191787885881679859 13861315787681828822519789)
                  ·
                    refine ⟨5197993420380685808444921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13861315787681828822519789 5197993420380685808444921)
                    ·
                      refine ⟨3898495065285514356333691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5197993420380685808444921 3898495065285514356333691)
                      ·
                        rfl

theorem cell23_7592292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_7592292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592292 prefixEnd_7592292 := by exact prefixLift 7592292
  have htrace : WordTrace (prefixWord ++ tailWord_7592292) baseStart_7592292 baseEnd_7592292 := by
    simpa [prefixWord, tailWord_7592292, baseEnd_7592292] using wordTrace_append hprefix tailTrace_7592292
  have hstable : (prefixWord ++ tailWord_7592292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592292).length < 2 ^ (prefixWord ++ tailWord_7592292).sum := by decide
  have hdescent : baseEnd_7592292 < baseStart_7592292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592415 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 3]
def baseStart_7592415 : Nat := 118140960795 + 7592415 * 2 ^ 59
def prefixEnd_7592415 : Nat := 4983230072969 + 3 ^ 40 * 7592415 * 2
def baseEnd_7592415 : Nat := 3898558223406017375095625

theorem tailTrace_7592415 : CollatzResearch.WordTrace tailWord_7592415 prefixEnd_7592415 3898558223406017375095625 := by
  unfold tailWord_7592415
  simp only [CollatzResearch.WordTrace]
  refine ⟨276918124788984611093042699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184612083192656407395361799 276918124788984611093042699)
  ·
    refine ⟨415377187183476916639564049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276918124788984611093042699 415377187183476916639564049)
    ·
      refine ⟨311532890387607687479673037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415377187183476916639564049 311532890387607687479673037)
      ·
        refine ⟨116824833895352882804877389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311532890387607687479673037 116824833895352882804877389)
        ·
          refine ⟨43809312710757331051829021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116824833895352882804877389 43809312710757331051829021)
          ·
            refine ⟨16428492266533999144435883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43809312710757331051829021 16428492266533999144435883)
            ·
              refine ⟨24642738399800998716653825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16428492266533999144435883 24642738399800998716653825)
              ·
                refine ⟨18482053799850749037490369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24642738399800998716653825 18482053799850749037490369)
                ·
                  refine ⟨13861540349888061778117777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18482053799850749037490369 13861540349888061778117777)
                  ·
                    refine ⟨10396155262416046333588333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13861540349888061778117777 10396155262416046333588333)
                    ·
                      refine ⟨3898558223406017375095625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10396155262416046333588333 3898558223406017375095625)
                      ·
                        rfl

theorem cell23_7592415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_7592415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592415 prefixEnd_7592415 := by exact prefixLift 7592415
  have htrace : WordTrace (prefixWord ++ tailWord_7592415) baseStart_7592415 baseEnd_7592415 := by
    simpa [prefixWord, tailWord_7592415, baseEnd_7592415] using wordTrace_append hprefix tailTrace_7592415
  have hstable : (prefixWord ++ tailWord_7592415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592415).length < 2 ^ (prefixWord ++ tailWord_7592415).sum := by decide
  have hdescent : baseEnd_7592415 < baseStart_7592415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592431 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 2, 9]
def baseStart_7592431 : Nat := 118140960795 + 7592431 * 2 ^ 59
def prefixEnd_7592431 : Nat := 4983230072969 + 3 ^ 40 * 7592431 * 2
def baseEnd_7592431 : Nat := 1299522146365496437498517

theorem tailTrace_7592431 : CollatzResearch.WordTrace tailWord_7592431 prefixEnd_7592431 1299522146365496437498517 := by
  unfold tailWord_7592431
  simp only [CollatzResearch.WordTrace]
  refine ⟨276918708356926645825625147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184612472237951097217083431 276918708356926645825625147)
  ·
    refine ⟨415378062535389968738437721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276918708356926645825625147 415378062535389968738437721)
    ·
      refine ⟨311533546901542476553828291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415378062535389968738437721 311533546901542476553828291)
      ·
        refine ⟨467300320352313714830742437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311533546901542476553828291 467300320352313714830742437)
        ·
          refine ⟨87618810066058821530764207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 467300320352313714830742437 87618810066058821530764207)
          ·
            refine ⟨131428215099088232296146311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87618810066058821530764207 131428215099088232296146311)
            ·
              refine ⟨197142322648632348444219467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131428215099088232296146311 197142322648632348444219467)
              ·
                refine ⟨295713483972948522666329201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197142322648632348444219467 295713483972948522666329201)
                ·
                  refine ⟨221785112979711391999746901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295713483972948522666329201 221785112979711391999746901)
                  ·
                    refine ⟨1299522146365496437498517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 221785112979711391999746901 1299522146365496437498517)
                    ·
                      rfl

theorem cell23_7592431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_7592431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592431 prefixEnd_7592431 := by exact prefixLift 7592431
  have htrace : WordTrace (prefixWord ++ tailWord_7592431) baseStart_7592431 baseEnd_7592431 := by
    simpa [prefixWord, tailWord_7592431, baseEnd_7592431] using wordTrace_append hprefix tailTrace_7592431
  have hstable : (prefixWord ++ tailWord_7592431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592431).length < 2 ^ (prefixWord ++ tailWord_7592431).sum := by decide
  have hdescent : baseEnd_7592431 < baseStart_7592431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592445 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_7592445 : Nat := 118140960795 + 7592445 * 2 ^ 59
def prefixEnd_7592445 : Nat := 4983230072969 + 3 ^ 40 * 7592445 * 2
def baseEnd_7592445 : Nat := 3898573627825652257720487

theorem tailTrace_7592445 : CollatzResearch.WordTrace tailWord_7592445 prefixEnd_7592445 3898573627825652257720487 := by
  unfold tailWord_7592445
  simp only [CollatzResearch.WordTrace]
  refine ⟨276919218978875926216634789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184612812652583950811089859 276919218978875926216634789)
  ·
    refine ⟨51922353558539236165619023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276919218978875926216634789 51922353558539236165619023)
    ·
      refine ⟨77883530337808854248428535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51922353558539236165619023 77883530337808854248428535)
      ·
        refine ⟨116825295506713281372642803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77883530337808854248428535 116825295506713281372642803)
        ·
          refine ⟨175237943260069922058964205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116825295506713281372642803 175237943260069922058964205)
          ·
            refine ⟨65714228722526220772111577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175237943260069922058964205 65714228722526220772111577)
            ·
              refine ⟨49285671541894665579083683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65714228722526220772111577 49285671541894665579083683)
              ·
                refine ⟨73928507312841998368625525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49285671541894665579083683 73928507312841998368625525)
                ·
                  refine ⟨6930797560578937347058643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73928507312841998368625525 6930797560578937347058643)
                  ·
                    refine ⟨10396196340868406020587965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6930797560578937347058643 10396196340868406020587965)
                    ·
                      refine ⟨3898573627825652257720487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10396196340868406020587965 3898573627825652257720487)
                      ·
                        rfl

theorem cell23_7592445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_7592445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592445 prefixEnd_7592445 := by exact prefixLift 7592445
  have htrace : WordTrace (prefixWord ++ tailWord_7592445) baseStart_7592445 baseEnd_7592445 := by
    simpa [prefixWord, tailWord_7592445, baseEnd_7592445] using wordTrace_append hprefix tailTrace_7592445
  have hstable : (prefixWord ++ tailWord_7592445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592445).length < 2 ^ (prefixWord ++ tailWord_7592445).sum := by decide
  have hdescent : baseEnd_7592445 < baseStart_7592445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592472 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 2, 3, 2]
def baseStart_7592472 : Nat := 118140960795 + 7592472 * 2 ^ 59
def prefixEnd_7592472 : Nat := 4983230072969 + 3 ^ 40 * 7592472 * 2
def baseEnd_7592472 : Nat := 3898587491803323652082863

theorem tailTrace_7592472 : CollatzResearch.WordTrace tailWord_7592472 prefixEnd_7592472 3898587491803323652082863 := by
  unfold tailWord_7592472
  simp only [CollatzResearch.WordTrace]
  refine ⟨138460101874889054913933835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184613469166518739885245113 138460101874889054913933835)
  ·
    refine ⟨207690152812333582370900753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138460101874889054913933835 207690152812333582370900753)
    ·
      refine ⟨155767614609250186778175565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207690152812333582370900753 155767614609250186778175565)
      ·
        refine ⟨58412855478468820041815837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155767614609250186778175565 58412855478468820041815837)
        ·
          refine ⟨21904820804425807515680939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58412855478468820041815837 21904820804425807515680939)
          ·
            refine ⟨32857231206638711273521409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21904820804425807515680939 32857231206638711273521409)
            ·
              refine ⟨24642923404979033455141057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32857231206638711273521409 24642923404979033455141057)
              ·
                refine ⟨18482192553734275091355793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24642923404979033455141057 18482192553734275091355793)
                ·
                  refine ⟨13861644415300706318516845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18482192553734275091355793 13861644415300706318516845)
                  ·
                    refine ⟨5198116655737764869443817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13861644415300706318516845 5198116655737764869443817)
                    ·
                      refine ⟨3898587491803323652082863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198116655737764869443817 3898587491803323652082863)
                      ·
                        rfl

theorem cell23_7592472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_7592472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592472 prefixEnd_7592472 := by exact prefixLift 7592472
  have htrace : WordTrace (prefixWord ++ tailWord_7592472) baseStart_7592472 baseEnd_7592472 := by
    simpa [prefixWord, tailWord_7592472, baseEnd_7592472] using wordTrace_append hprefix tailTrace_7592472
  have hstable : (prefixWord ++ tailWord_7592472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592472).length < 2 ^ (prefixWord ++ tailWord_7592472).sum := by decide
  have hdescent : baseEnd_7592472 < baseStart_7592472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592498 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_7592498 : Nat := 118140960795 + 7592498 * 2 ^ 59
def prefixEnd_7592498 : Nat := 4983230072969 + 3 ^ 40 * 7592498 * 2
def baseEnd_7592498 : Nat := 3898600842300340550357743

theorem tailTrace_7592498 : CollatzResearch.WordTrace tailWord_7592498 prefixEnd_7592498 3898600842300340550357743 := by
  unfold tailWord_7592498
  simp only [CollatzResearch.WordTrace]
  refine ⟨69230288011920979067078537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184614101365122610845542765 69230288011920979067078537)
  ·
    refine ⟨51922716008940734300308903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69230288011920979067078537 51922716008940734300308903)
    ·
      refine ⟨77884074013411101450463355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51922716008940734300308903 77884074013411101450463355)
      ·
        refine ⟨116826111020116652175695033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77884074013411101450463355 116826111020116652175695033)
        ·
          refine ⟨87619583265087489131771275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116826111020116652175695033 87619583265087489131771275)
          ·
            refine ⟨131429374897631233697656913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87619583265087489131771275 131429374897631233697656913)
            ·
              refine ⟨98572031173223425273242685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131429374897631233697656913 98572031173223425273242685)
              ·
                refine ⟨36964511689958784477466007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98572031173223425273242685 36964511689958784477466007)
                ·
                  refine ⟨55446767534938176716199011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36964511689958784477466007 55446767534938176716199011)
                  ·
                    refine ⟨83170151302407265074298517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55446767534938176716199011 83170151302407265074298517)
                    ·
                      refine ⟨3898600842300340550357743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83170151302407265074298517 3898600842300340550357743)
                      ·
                        rfl

theorem cell23_7592498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_7592498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592498 prefixEnd_7592498 := by exact prefixLift 7592498
  have htrace : WordTrace (prefixWord ++ tailWord_7592498) baseStart_7592498 baseEnd_7592498 := by
    simpa [prefixWord, tailWord_7592498, baseEnd_7592498] using wordTrace_append hprefix tailTrace_7592498
  have hstable : (prefixWord ++ tailWord_7592498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592498).length < 2 ^ (prefixWord ++ tailWord_7592498).sum := by decide
  have hdescent : baseEnd_7592498 < baseStart_7592498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592502 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_7592502 : Nat := 118140960795 + 7592502 * 2 ^ 59
def prefixEnd_7592502 : Nat := 4983230072969 + 3 ^ 40 * 7592502 * 2
def baseEnd_7592502 : Nat := 3898602896222958534707725

theorem tailTrace_7592502 : CollatzResearch.WordTrace tailWord_7592502 prefixEnd_7592502 3898602896222958534707725 := by
  unfold tailWord_7592502
  simp only [CollatzResearch.WordTrace]
  refine ⟨17307581121229339059466235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184614198626446283300973173 17307581121229339059466235)
  ·
    refine ⟨25961371681844008589199353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17307581121229339059466235 25961371681844008589199353)
    ·
      refine ⟨19471028761383006441899515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25961371681844008589199353 19471028761383006441899515)
      ·
        refine ⟨29206543142074509662849273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19471028761383006441899515 29206543142074509662849273)
        ·
          refine ⟨21904907356555882247136955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29206543142074509662849273 21904907356555882247136955)
          ·
            refine ⟨32857361034833823370705433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21904907356555882247136955 32857361034833823370705433)
            ·
              refine ⟨24643020776125367528029075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32857361034833823370705433 24643020776125367528029075)
              ·
                refine ⟨36964531164188051292043613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24643020776125367528029075 36964531164188051292043613)
                ·
                  refine ⟨13861699186570519234516355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36964531164188051292043613 13861699186570519234516355)
                  ·
                    refine ⟨20792548779855778851774533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13861699186570519234516355 20792548779855778851774533)
                    ·
                      refine ⟨3898602896222958534707725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20792548779855778851774533 3898602896222958534707725)
                      ·
                        rfl

theorem cell23_7592502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_7592502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592502 prefixEnd_7592502 := by exact prefixLift 7592502
  have htrace : WordTrace (prefixWord ++ tailWord_7592502) baseStart_7592502 baseEnd_7592502 := by
    simpa [prefixWord, tailWord_7592502, baseEnd_7592502] using wordTrace_append hprefix tailTrace_7592502
  have hstable : (prefixWord ++ tailWord_7592502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592502).length < 2 ^ (prefixWord ++ tailWord_7592502).sum := by decide
  have hdescent : baseEnd_7592502 < baseStart_7592502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592505 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 3, 2, 3]
def baseStart_7592505 : Nat := 118140960795 + 7592505 * 2 ^ 59
def prefixEnd_7592505 : Nat := 4983230072969 + 3 ^ 40 * 7592505 * 2
def baseEnd_7592505 : Nat := 3898604436664922022970211

theorem tailTrace_7592505 : CollatzResearch.WordTrace tailWord_7592505 prefixEnd_7592505 3898604436664922022970211 := by
  unfold tailWord_7592505
  simp only [CollatzResearch.WordTrace]
  refine ⟨276921407358658556463818969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184614271572439037642545979 276921407358658556463818969)
  ·
    refine ⟨207691055518993917347864227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276921407358658556463818969 207691055518993917347864227)
    ·
      refine ⟨311536583278490876021796341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207691055518993917347864227 311536583278490876021796341)
      ·
        refine ⟨29206554682358519627043407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311536583278490876021796341 29206554682358519627043407)
        ·
          refine ⟨43809832023537779440565111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29206554682358519627043407 43809832023537779440565111)
          ·
            refine ⟨65714748035306669160847667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43809832023537779440565111 65714748035306669160847667)
            ·
              refine ⟨98572122052960003741271501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65714748035306669160847667 98572122052960003741271501)
              ·
                refine ⟨36964545769860001402976813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98572122052960003741271501 36964545769860001402976813)
                ·
                  refine ⟨13861704663697500526116305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36964545769860001402976813 13861704663697500526116305)
                  ·
                    refine ⟨10396278497773125394587229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13861704663697500526116305 10396278497773125394587229)
                    ·
                      refine ⟨3898604436664922022970211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10396278497773125394587229 3898604436664922022970211)
                      ·
                        rfl

theorem cell23_7592505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_7592505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592505 prefixEnd_7592505 := by exact prefixLift 7592505
  have htrace : WordTrace (prefixWord ++ tailWord_7592505) baseStart_7592505 baseEnd_7592505 := by
    simpa [prefixWord, tailWord_7592505, baseEnd_7592505] using wordTrace_append hprefix tailTrace_7592505
  have hstable : (prefixWord ++ tailWord_7592505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592505).length < 2 ^ (prefixWord ++ tailWord_7592505).sum := by decide
  have hdescent : baseEnd_7592505 < baseStart_7592505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592516 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7592516 : Nat := 118140960795 + 7592516 * 2 ^ 59
def prefixEnd_7592516 : Nat := 4983230072969 + 3 ^ 40 * 7592516 * 2
def baseEnd_7592516 : Nat := 1299536694984040493310887

theorem tailTrace_7592516 : CollatzResearch.WordTrace tailWord_7592516 prefixEnd_7592516 1299536694984040493310887 := by
  unfold tailWord_7592516
  simp only [CollatzResearch.WordTrace]
  refine ⟨138460904280809352671234701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184614539041079136894979601 138460904280809352671234701)
  ·
    refine ⟨51922839105303507251713013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138460904280809352671234701 51922839105303507251713013)
    ·
      refine ⟨4867766166122203804848095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51922839105303507251713013 4867766166122203804848095)
      ·
        refine ⟨7301649249183305707272143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867766166122203804848095 7301649249183305707272143)
        ·
          refine ⟨10952473873774958560908215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301649249183305707272143 10952473873774958560908215)
          ·
            refine ⟨16428710810662437841362323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10952473873774958560908215 16428710810662437841362323)
            ·
              refine ⟨24643066215993656762043485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16428710810662437841362323 24643066215993656762043485)
              ·
                refine ⟨9241149830997621285766307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24643066215993656762043485 9241149830997621285766307)
                ·
                  refine ⟨13861724746496431928649461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9241149830997621285766307 13861724746496431928649461)
                  ·
                    refine ⟨1299536694984040493310887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13861724746496431928649461 1299536694984040493310887)
                    ·
                      rfl

theorem cell23_7592516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7592516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592516 prefixEnd_7592516 := by exact prefixLift 7592516
  have htrace : WordTrace (prefixWord ++ tailWord_7592516) baseStart_7592516 baseEnd_7592516 := by
    simpa [prefixWord, tailWord_7592516, baseEnd_7592516] using wordTrace_append hprefix tailTrace_7592516
  have hstable : (prefixWord ++ tailWord_7592516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592516).length < 2 ^ (prefixWord ++ tailWord_7592516).sum := by decide
  have hdescent : baseEnd_7592516 < baseStart_7592516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592519 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 1, 1, 4]
def baseStart_7592519 : Nat := 118140960795 + 7592519 * 2 ^ 59
def prefixEnd_7592519 : Nat := 4983230072969 + 3 ^ 40 * 7592519 * 2
def baseEnd_7592519 : Nat := 3898611625394084968195147

theorem tailTrace_7592519 : CollatzResearch.WordTrace tailWord_7592519 prefixEnd_7592519 3898611625394084968195147 := by
  unfold tailWord_7592519
  simp only [CollatzResearch.WordTrace]
  refine ⟨276921917980607836854828611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184614611987071891236552407 276921917980607836854828611)
  ·
    refine ⟨415382876970911755282242917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276921917980607836854828611 415382876970911755282242917)
    ·
      refine ⟨77884289432045954115420547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415382876970911755282242917 77884289432045954115420547)
      ·
        refine ⟨116826434148068931173130821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77884289432045954115420547 116826434148068931173130821)
        ·
          refine ⟨21904956402762924594962029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116826434148068931173130821 21904956402762924594962029)
          ·
            refine ⟨8214358651036096723110761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21904956402762924594962029 8214358651036096723110761)
            ·
              refine ⟨6160768988277072542333071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8214358651036096723110761 6160768988277072542333071)
              ·
                refine ⟨9241153482415608813499607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6160768988277072542333071 9241153482415608813499607)
                ·
                  refine ⟨13861730223623413220249411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9241153482415608813499607 13861730223623413220249411)
                  ·
                    refine ⟨20792595335435119830374117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13861730223623413220249411 20792595335435119830374117)
                    ·
                      refine ⟨3898611625394084968195147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20792595335435119830374117 3898611625394084968195147)
                      ·
                        rfl

theorem cell23_7592519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_7592519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592519 prefixEnd_7592519 := by exact prefixLift 7592519
  have htrace : WordTrace (prefixWord ++ tailWord_7592519) baseStart_7592519 baseEnd_7592519 := by
    simpa [prefixWord, tailWord_7592519, baseEnd_7592519] using wordTrace_append hprefix tailTrace_7592519
  have hstable : (prefixWord ++ tailWord_7592519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592519).length < 2 ^ (prefixWord ++ tailWord_7592519).sum := by decide
  have hdescent : baseEnd_7592519 < baseStart_7592519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592522 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_7592522 : Nat := 118140960795 + 7592522 * 2 ^ 59
def prefixEnd_7592522 : Nat := 4983230072969 + 3 ^ 40 * 7592522 * 2
def baseEnd_7592522 : Nat := 3898613165836048456457633

theorem tailTrace_7592522 : CollatzResearch.WordTrace tailWord_7592522 prefixEnd_7592522 3898613165836048456457633 := by
  unfold tailWord_7592522
  simp only [CollatzResearch.WordTrace]
  refine ⟨69230506849899242091796955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184614684933064645578125213 69230506849899242091796955)
  ·
    refine ⟨103845760274848863137695433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69230506849899242091796955 103845760274848863137695433)
    ·
      refine ⟨77884320206136647353271575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103845760274848863137695433 77884320206136647353271575)
      ·
        refine ⟨116826480309204971029907363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77884320206136647353271575 116826480309204971029907363)
        ·
          refine ⟨175239720463807456544861045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116826480309204971029907363 175239720463807456544861045)
          ·
            refine ⟨16428723793481949051080723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175239720463807456544861045 16428723793481949051080723)
            ·
              refine ⟨24643085690222923576621085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16428723793481949051080723 24643085690222923576621085)
              ·
                refine ⟨9241157133833596341232907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24643085690222923576621085 9241157133833596341232907)
                ·
                  refine ⟨13861735700750394511849361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9241157133833596341232907 13861735700750394511849361)
                  ·
                    refine ⟨10396301775562795883887021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13861735700750394511849361 10396301775562795883887021)
                    ·
                      refine ⟨3898613165836048456457633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10396301775562795883887021 3898613165836048456457633)
                      ·
                        rfl

theorem cell23_7592522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_7592522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592522 prefixEnd_7592522 := by exact prefixLift 7592522
  have htrace : WordTrace (prefixWord ++ tailWord_7592522) baseStart_7592522 baseEnd_7592522 := by
    simpa [prefixWord, tailWord_7592522, baseEnd_7592522] using wordTrace_append hprefix tailTrace_7592522
  have hstable : (prefixWord ++ tailWord_7592522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592522).length < 2 ^ (prefixWord ++ tailWord_7592522).sum := by decide
  have hdescent : baseEnd_7592522 < baseStart_7592522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592525 : List Nat := [1, 6, 1, 1, 2, 2, 10]
def baseStart_7592525 : Nat := 118140960795 + 7592525 * 2 ^ 59
def prefixEnd_7592525 : Nat := 4983230072969 + 3 ^ 40 * 7592525 * 2
def baseEnd_7592525 : Nat := 48131045756518665984199

theorem tailTrace_7592525 : CollatzResearch.WordTrace tailWord_7592525 prefixEnd_7592525 48131045756518665984199 := by
  unfold tailWord_7592525
  simp only [CollatzResearch.WordTrace]
  refine ⟨276922136818586099879547029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184614757879057399919698019 276922136818586099879547029)
  ·
    refine ⟨12980725163371223431853767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 276922136818586099879547029 12980725163371223431853767)
    ·
      refine ⟨19471087745056835147780651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12980725163371223431853767 19471087745056835147780651)
      ·
        refine ⟨29206631617585252721670977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19471087745056835147780651 29206631617585252721670977)
        ·
          refine ⟨21904973713188939541253233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29206631617585252721670977 21904973713188939541253233)
          ·
            refine ⟨16428730284891704655939925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21904973713188939541253233 16428730284891704655939925)
            ·
              refine ⟨48131045756518665984199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16428730284891704655939925 48131045756518665984199)
              ·
                rfl

theorem cell23_7592525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 10].length) (baseStart_7592525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592525 prefixEnd_7592525 := by exact prefixLift 7592525
  have htrace : WordTrace (prefixWord ++ tailWord_7592525) baseStart_7592525 baseEnd_7592525 := by
    simpa [prefixWord, tailWord_7592525, baseEnd_7592525] using wordTrace_append hprefix tailTrace_7592525
  have hstable : (prefixWord ++ tailWord_7592525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592525).length < 2 ^ (prefixWord ++ tailWord_7592525).sum := by decide
  have hdescent : baseEnd_7592525 < baseStart_7592525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592546 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_7592546 : Nat := 118140960795 + 7592546 * 2 ^ 59
def prefixEnd_7592546 : Nat := 4983230072969 + 3 ^ 40 * 7592546 * 2
def baseEnd_7592546 : Nat := 1299541829790585454185841

theorem tailTrace_7592546 : CollatzResearch.WordTrace tailWord_7592546 prefixEnd_7592546 1299541829790585454185841 := by
  unfold tailWord_7592546
  simp only [CollatzResearch.WordTrace]
  refine ⟨69230725687877505116515373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184615268501006680310707661 69230725687877505116515373)
  ·
    refine ⟨25961522132954064418693265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69230725687877505116515373 25961522132954064418693265)
    ·
      refine ⟨19471141599715548314019949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25961522132954064418693265 19471141599715548314019949)
      ·
        refine ⟨7301678099893330617757481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19471141599715548314019949 7301678099893330617757481)
        ·
          refine ⟨5476258574919997963318111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7301678099893330617757481 5476258574919997963318111)
          ·
            refine ⟨8214387862379996944977167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5476258574919997963318111 8214387862379996944977167)
            ·
              refine ⟨12321581793569995417465751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8214387862379996944977167 12321581793569995417465751)
              ·
                refine ⟨18482372690354993126198627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12321581793569995417465751 18482372690354993126198627)
                ·
                  refine ⟨27723559035532489689297941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18482372690354993126198627 27723559035532489689297941)
                  ·
                    refine ⟨1299541829790585454185841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27723559035532489689297941 1299541829790585454185841)
                    ·
                      rfl

theorem cell23_7592546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_7592546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592546 prefixEnd_7592546 := by exact prefixLift 7592546
  have htrace : WordTrace (prefixWord ++ tailWord_7592546) baseStart_7592546 baseEnd_7592546 := by
    simpa [prefixWord, tailWord_7592546, baseEnd_7592546] using wordTrace_append hprefix tailTrace_7592546
  have hstable : (prefixWord ++ tailWord_7592546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592546).length < 2 ^ (prefixWord ++ tailWord_7592546).sum := by decide
  have hdescent : baseEnd_7592546 < baseStart_7592546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592549 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 1, 2, 4]
def baseStart_7592549 : Nat := 118140960795 + 7592549 * 2 ^ 59
def prefixEnd_7592549 : Nat := 4983230072969 + 3 ^ 40 * 7592549 * 2
def baseEnd_7592549 : Nat := 3898627029813719850820009

theorem tailTrace_7592549 : CollatzResearch.WordTrace tailWord_7592549 prefixEnd_7592549 3898627029813719850820009 := by
  unfold tailWord_7592549
  simp only [CollatzResearch.WordTrace]
  refine ⟨276923012170499151978420701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184615341446999434652280467 276923012170499151978420701)
  ·
    refine ⟨103846129563937181991907763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276923012170499151978420701 103846129563937181991907763)
    ·
      refine ⟨155769194345905772987861645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103846129563937181991907763 155769194345905772987861645)
      ·
        refine ⟨58413447879714664870448117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155769194345905772987861645 58413447879714664870448117)
        ·
          refine ⟨5476260738723249831604511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58413447879714664870448117 5476260738723249831604511)
          ·
            refine ⟨8214391108084874747406767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5476260738723249831604511 8214391108084874747406767)
            ·
              refine ⟨12321586662127312121110151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8214391108084874747406767 12321586662127312121110151)
              ·
                refine ⟨18482379993190968181665227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12321586662127312121110151 18482379993190968181665227)
                ·
                  refine ⟨27723569989786452272497841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18482379993190968181665227 27723569989786452272497841)
                  ·
                    refine ⟨20792677492339839204373381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27723569989786452272497841 20792677492339839204373381)
                    ·
                      refine ⟨3898627029813719850820009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20792677492339839204373381 3898627029813719850820009)
                      ·
                        rfl

theorem cell23_7592549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_7592549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592549 prefixEnd_7592549 := by exact prefixLift 7592549
  have htrace : WordTrace (prefixWord ++ tailWord_7592549) baseStart_7592549 baseEnd_7592549 := by
    simpa [prefixWord, tailWord_7592549, baseEnd_7592549] using wordTrace_append hprefix tailTrace_7592549
  have hstable : (prefixWord ++ tailWord_7592549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592549).length < 2 ^ (prefixWord ++ tailWord_7592549).sum := by decide
  have hdescent : baseEnd_7592549 < baseStart_7592549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592588 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_7592588 : Nat := 118140960795 + 7592588 * 2 ^ 59
def prefixEnd_7592588 : Nat := 4983230072969 + 3 ^ 40 * 7592588 * 2
def baseEnd_7592588 : Nat := 3898647055559245198232329

theorem tailTrace_7592588 : CollatzResearch.WordTrace tailWord_7592588 prefixEnd_7592588 3898647055559245198232329 := by
  unfold tailWord_7592588
  simp only [CollatzResearch.WordTrace]
  refine ⟨138462217308678930819545209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184616289744905241092726945 138462217308678930819545209)
  ·
    refine ⟨103846662981509198114658907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138462217308678930819545209 103846662981509198114658907)
    ·
      refine ⟨155769994472263797171988361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103846662981509198114658907 155769994472263797171988361)
      ·
        refine ⟨116827495854197847878991271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155769994472263797171988361 116827495854197847878991271)
        ·
          refine ⟨175241243781296771818486907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116827495854197847878991271 175241243781296771818486907)
          ·
            refine ⟨262861865671945157727730361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175241243781296771818486907 262861865671945157727730361)
            ·
              refine ⟨197146399253958868295797771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262861865671945157727730361 197146399253958868295797771)
              ·
                refine ⟨295719598880938302443696657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197146399253958868295797771 295719598880938302443696657)
                ·
                  refine ⟨221789699160703726832772493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295719598880938302443696657 221789699160703726832772493)
                  ·
                    refine ⟨83171137185263897562289685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221789699160703726832772493 83171137185263897562289685)
                    ·
                      refine ⟨3898647055559245198232329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83171137185263897562289685 3898647055559245198232329)
                      ·
                        rfl

theorem cell23_7592588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_7592588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592588 prefixEnd_7592588 := by exact prefixLift 7592588
  have htrace : WordTrace (prefixWord ++ tailWord_7592588) baseStart_7592588 baseEnd_7592588 := by
    simpa [prefixWord, tailWord_7592588, baseEnd_7592588] using wordTrace_append hprefix tailTrace_7592588
  have hstable : (prefixWord ++ tailWord_7592588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592588).length < 2 ^ (prefixWord ++ tailWord_7592588).sum := by decide
  have hdescent : baseEnd_7592588 < baseStart_7592588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592605 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_7592605 : Nat := 118140960795 + 7592605 * 2 ^ 59
def prefixEnd_7592605 : Nat := 4983230072969 + 3 ^ 40 * 7592605 * 2
def baseEnd_7592605 : Nat := 3898655784730371631719751

theorem tailTrace_7592605 : CollatzResearch.WordTrace tailWord_7592605 prefixEnd_7592605 3898655784730371631719751 := by
  unfold tailWord_7592605
  simp only [CollatzResearch.WordTrace]
  refine ⟨276925054658296273542459269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184616703105530849028306179 276925054658296273542459269)
  ·
    refine ⟨51923447748430551289211113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276925054658296273542459269 51923447748430551289211113)
    ·
      refine ⟨38942585811322913466908335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51923447748430551289211113 38942585811322913466908335)
      ·
        refine ⟨58413878716984370200362503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38942585811322913466908335 58413878716984370200362503)
        ·
          refine ⟨87620818075476555300543755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58413878716984370200362503 87620818075476555300543755)
          ·
            refine ⟨131431227113214832950815633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87620818075476555300543755 131431227113214832950815633)
            ·
              refine ⟨98573420334911124713111725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131431227113214832950815633 98573420334911124713111725)
              ·
                refine ⟨36965032625591671767416897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98573420334911124713111725 36965032625591671767416897)
                ·
                  refine ⟨27723774469193753825562673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36965032625591671767416897 27723774469193753825562673)
                  ·
                    refine ⟨20792830851895315369172005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27723774469193753825562673 20792830851895315369172005)
                    ·
                      refine ⟨3898655784730371631719751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20792830851895315369172005 3898655784730371631719751)
                      ·
                        rfl

theorem cell23_7592605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_7592605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592605 prefixEnd_7592605 := by exact prefixLift 7592605
  have htrace : WordTrace (prefixWord ++ tailWord_7592605) baseStart_7592605 baseEnd_7592605 := by
    simpa [prefixWord, tailWord_7592605, baseEnd_7592605] using wordTrace_append hprefix tailTrace_7592605
  have hstable : (prefixWord ++ tailWord_7592605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592605).length < 2 ^ (prefixWord ++ tailWord_7592605).sum := by decide
  have hdescent : baseEnd_7592605 < baseStart_7592605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592630 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_7592630 : Nat := 118140960795 + 7592630 * 2 ^ 59
def prefixEnd_7592630 : Nat := 4983230072969 + 3 ^ 40 * 7592630 * 2
def baseEnd_7592630 : Nat := 3898668621746734033907137

theorem tailTrace_7592630 : CollatzResearch.WordTrace tailWord_7592630 prefixEnd_7592630 3898668621746734033907137 := by
  unfold tailWord_7592630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17307872905200356425757459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184617310988803801874746229 17307872905200356425757459)
  ·
    refine ⟨25961809357800534638636189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17307872905200356425757459 25961809357800534638636189)
    ·
      refine ⟨9735678509175200489488571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25961809357800534638636189 9735678509175200489488571)
      ·
        refine ⟨14603517763762800734232857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9735678509175200489488571 14603517763762800734232857)
        ·
          refine ⟨10952638322822100550674643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14603517763762800734232857 10952638322822100550674643)
          ·
            refine ⟨16428957484233150826011965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10952638322822100550674643 16428957484233150826011965)
            ·
              refine ⟨6160859056587431559754487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16428957484233150826011965 6160859056587431559754487)
              ·
                refine ⟨9241288584881147339631731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6160859056587431559754487 9241288584881147339631731)
                ·
                  refine ⟨13861932877321721009447597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9241288584881147339631731 13861932877321721009447597)
                  ·
                    refine ⟨5198224828995645378542849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13861932877321721009447597 5198224828995645378542849)
                    ·
                      refine ⟨3898668621746734033907137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198224828995645378542849 3898668621746734033907137)
                      ·
                        rfl

theorem cell23_7592630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_7592630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592630 prefixEnd_7592630 := by exact prefixLift 7592630
  have htrace : WordTrace (prefixWord ++ tailWord_7592630) baseStart_7592630 baseEnd_7592630 := by
    simpa [prefixWord, tailWord_7592630, baseEnd_7592630] using wordTrace_append hprefix tailTrace_7592630
  have hstable : (prefixWord ++ tailWord_7592630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592630).length < 2 ^ (prefixWord ++ tailWord_7592630).sum := by decide
  have hdescent : baseEnd_7592630 < baseStart_7592630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592665 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 4]
def baseStart_7592665 : Nat := 118140960795 + 7592665 * 2 ^ 59
def prefixEnd_7592665 : Nat := 4983230072969 + 3 ^ 40 * 7592665 * 2
def baseEnd_7592665 : Nat := 3898686593569641396969475

theorem tailTrace_7592665 : CollatzResearch.WordTrace tailWord_7592665 prefixEnd_7592665 3898686593569641396969475 := by
  unfold tailWord_7592665
  simp only [CollatzResearch.WordTrace]
  refine ⟨276927243038078903789643449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184618162025385935859762299 276927243038078903789643449)
  ·
    refine ⟨207695432278559177842232587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276927243038078903789643449 207695432278559177842232587)
    ·
      refine ⟨311543148417838766763348881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207695432278559177842232587 311543148417838766763348881)
      ·
        refine ⟨233657361313379075072511661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311543148417838766763348881 233657361313379075072511661)
        ·
          refine ⟨87621510492517153152191873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233657361313379075072511661 87621510492517153152191873)
          ·
            refine ⟨65716132869387864864143905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87621510492517153152191873 65716132869387864864143905)
            ·
              refine ⟨49287099652040898648107929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65716132869387864864143905 49287099652040898648107929)
              ·
                refine ⟨36965324739030673986080947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49287099652040898648107929 36965324739030673986080947)
                ·
                  refine ⟨55447987108546010979121421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36965324739030673986080947 55447987108546010979121421)
                  ·
                    refine ⟨20792995165704754117170533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55447987108546010979121421 20792995165704754117170533)
                    ·
                      refine ⟨3898686593569641396969475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20792995165704754117170533 3898686593569641396969475)
                      ·
                        rfl

theorem cell23_7592665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_7592665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592665 prefixEnd_7592665 := by exact prefixLift 7592665
  have htrace : WordTrace (prefixWord ++ tailWord_7592665) baseStart_7592665 baseEnd_7592665 := by
    simpa [prefixWord, tailWord_7592665, baseEnd_7592665] using wordTrace_append hprefix tailTrace_7592665
  have hstable : (prefixWord ++ tailWord_7592665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592665).length < 2 ^ (prefixWord ++ tailWord_7592665).sum := by decide
  have hdescent : baseEnd_7592665 < baseStart_7592665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592682 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_7592682 : Nat := 118140960795 + 7592682 * 2 ^ 59
def prefixEnd_7592682 : Nat := 4983230072969 + 3 ^ 40 * 7592682 * 2
def baseEnd_7592682 : Nat := 3898695322740767830456897

theorem tailTrace_7592682 : CollatzResearch.WordTrace tailWord_7592682 prefixEnd_7592682 3898695322740767830456897 := by
  unfold tailWord_7592682
  simp only [CollatzResearch.WordTrace]
  refine ⟨69231965769754328923253075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184618575386011543795341533 69231965769754328923253075)
  ·
    refine ⟨103847948654631493384879613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69231965769754328923253075 103847948654631493384879613)
    ·
      refine ⟨38942980745486810019329855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103847948654631493384879613 38942980745486810019329855)
      ·
        refine ⟨58414471118230215028994783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38942980745486810019329855 58414471118230215028994783)
        ·
          refine ⟨87621706677345322543492175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58414471118230215028994783 87621706677345322543492175)
          ·
            refine ⟨131432560016017983815238263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87621706677345322543492175 131432560016017983815238263)
            ·
              refine ⟨197148840024026975722857395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131432560016017983815238263 197148840024026975722857395)
              ·
                refine ⟨295723260036040463584286093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197148840024026975722857395 295723260036040463584286093)
                ·
                  refine ⟨110896222513515173844107285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295723260036040463584286093 110896222513515173844107285)
                  ·
                    refine ⟨5198260430321023773942529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110896222513515173844107285 5198260430321023773942529)
                    ·
                      refine ⟨3898695322740767830456897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198260430321023773942529 3898695322740767830456897)
                      ·
                        rfl

theorem cell23_7592682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_7592682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592682 prefixEnd_7592682 := by exact prefixLift 7592682
  have htrace : WordTrace (prefixWord ++ tailWord_7592682) baseStart_7592682 baseEnd_7592682 := by
    simpa [prefixWord, tailWord_7592682, baseEnd_7592682] using wordTrace_append hprefix tailTrace_7592682
  have hstable : (prefixWord ++ tailWord_7592682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592682).length < 2 ^ (prefixWord ++ tailWord_7592682).sum := by decide
  have hdescent : baseEnd_7592682 < baseStart_7592682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592725 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_7592725 : Nat := 118140960795 + 7592725 * 2 ^ 59
def prefixEnd_7592725 : Nat := 4983230072969 + 3 ^ 40 * 7592725 * 2
def baseEnd_7592725 : Nat := 3898717402408911162219199

theorem tailTrace_7592725 : CollatzResearch.WordTrace tailWord_7592725 prefixEnd_7592725 3898717402408911162219199 := by
  unfold tailWord_7592725
  simp only [CollatzResearch.WordTrace]
  refine ⟨276929431417861534036827629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184619620945241022691218419 276929431417861534036827629)
  ·
    refine ⟨103848536781698075263810361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276929431417861534036827629 103848536781698075263810361)
    ·
      refine ⟨77886402586273556447857771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103848536781698075263810361 77886402586273556447857771)
      ·
        refine ⟨116829603879410334671786657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77886402586273556447857771 116829603879410334671786657)
        ·
          refine ⟨87622202909557751003839993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116829603879410334671786657 87622202909557751003839993)
          ·
            refine ⟨65716652182168313252879995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87622202909557751003839993 65716652182168313252879995)
            ·
              refine ⟨98574978273252469879319993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65716652182168313252879995 98574978273252469879319993)
              ·
                refine ⟨73931233704939352409489995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98574978273252469879319993 73931233704939352409489995)
                ·
                  refine ⟨110896850557409028614234993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73931233704939352409489995 110896850557409028614234993)
                  ·
                    refine ⟨83172637918056771460676245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110896850557409028614234993 83172637918056771460676245)
                    ·
                      refine ⟨3898717402408911162219199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83172637918056771460676245 3898717402408911162219199)
                      ·
                        rfl

theorem cell23_7592725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_7592725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592725 prefixEnd_7592725 := by exact prefixLift 7592725
  have htrace : WordTrace (prefixWord ++ tailWord_7592725) baseStart_7592725 baseEnd_7592725 := by
    simpa [prefixWord, tailWord_7592725, baseEnd_7592725] using wordTrace_append hprefix tailTrace_7592725
  have hstable : (prefixWord ++ tailWord_7592725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592725).length < 2 ^ (prefixWord ++ tailWord_7592725).sum := by decide
  have hdescent : baseEnd_7592725 < baseStart_7592725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592759 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 2, 3, 2]
def baseStart_7592759 : Nat := 118140960795 + 7592759 * 2 ^ 59
def prefixEnd_7592759 : Nat := 4983230072969 + 3 ^ 40 * 7592759 * 2
def baseEnd_7592759 : Nat := 3898734860751164029194043

theorem tailTrace_7592759 : CollatzResearch.WordTrace tailWord_7592759 prefixEnd_7592759 3898734860751164029194043 := by
  unfold tailWord_7592759
  simp only [CollatzResearch.WordTrace]
  refine ⟨276930671499738357843565331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184620447666492238562376887 276930671499738357843565331)
  ·
    refine ⟨415396007249607536765347997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276930671499738357843565331 415396007249607536765347997)
    ·
      refine ⟨155773502718602826287005499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415396007249607536765347997 155773502718602826287005499)
      ·
        refine ⟨233660254077904239430508249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155773502718602826287005499 233660254077904239430508249)
        ·
          refine ⟨175245190558428179572881187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233660254077904239430508249 175245190558428179572881187)
          ·
            refine ⟨262867785837642269359321781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175245190558428179572881187 262867785837642269359321781)
            ·
              refine ⟨24643854922278962752436417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262867785837642269359321781 24643854922278962752436417)
              ·
                refine ⟨18482891191709222064327313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24643854922278962752436417 18482891191709222064327313)
                ·
                  refine ⟨13862168393781916548245485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18482891191709222064327313 13862168393781916548245485)
                  ·
                    refine ⟨5198313147668218705592057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13862168393781916548245485 5198313147668218705592057)
                    ·
                      refine ⟨3898734860751164029194043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198313147668218705592057 3898734860751164029194043)
                      ·
                        rfl

theorem cell23_7592759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 3, 2].length) (baseStart_7592759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592759 prefixEnd_7592759 := by exact prefixLift 7592759
  have htrace : WordTrace (prefixWord ++ tailWord_7592759) baseStart_7592759 baseEnd_7592759 := by
    simpa [prefixWord, tailWord_7592759, baseEnd_7592759] using wordTrace_append hprefix tailTrace_7592759
  have hstable : (prefixWord ++ tailWord_7592759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592759).length < 2 ^ (prefixWord ++ tailWord_7592759).sum := by decide
  have hdescent : baseEnd_7592759 < baseStart_7592759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592839 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_7592839 : Nat := 118140960795 + 7592839 * 2 ^ 59
def prefixEnd_7592839 : Nat := 4983230072969 + 3 ^ 40 * 7592839 * 2
def baseEnd_7592839 : Nat := 3898775939203523716193675

theorem tailTrace_7592839 : CollatzResearch.WordTrace tailWord_7592839 prefixEnd_7592839 3898775939203523716193675 := by
  unfold tailWord_7592839
  simp only [CollatzResearch.WordTrace]
  refine ⟨276933589339448531506477571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184622392892965687670985047 276933589339448531506477571)
  ·
    refine ⟨415400384009172797259716357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276933589339448531506477571 415400384009172797259716357)
    ·
      refine ⟨77887572001719899486196817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415400384009172797259716357 77887572001719899486196817)
      ·
        refine ⟨58415679001289924614647613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77887572001719899486196817 58415679001289924614647613)
        ·
          refine ⟨21905879625483721730492855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58415679001289924614647613 21905879625483721730492855)
          ·
            refine ⟨32858819438225582595739283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21905879625483721730492855 32858819438225582595739283)
            ·
              refine ⟨49288229157338373893608925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32858819438225582595739283 49288229157338373893608925)
              ·
                refine ⟨18483085934001890210103347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49288229157338373893608925 18483085934001890210103347)
                ·
                  refine ⟨27724628901002835315155021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18483085934001890210103347 27724628901002835315155021)
                  ·
                    refine ⟨10396735837876063243183133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27724628901002835315155021 10396735837876063243183133)
                    ·
                      refine ⟨3898775939203523716193675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10396735837876063243183133 3898775939203523716193675)
                      ·
                        rfl

theorem cell23_7592839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_7592839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592839 prefixEnd_7592839 := by exact prefixLift 7592839
  have htrace : WordTrace (prefixWord ++ tailWord_7592839) baseStart_7592839 baseEnd_7592839 := by
    simpa [prefixWord, tailWord_7592839, baseEnd_7592839] using wordTrace_append hprefix tailTrace_7592839
  have hstable : (prefixWord ++ tailWord_7592839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592839).length < 2 ^ (prefixWord ++ tailWord_7592839).sum := by decide
  have hdescent : baseEnd_7592839 < baseStart_7592839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592860 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_7592860 : Nat := 118140960795 + 7592860 * 2 ^ 59
def prefixEnd_7592860 : Nat := 4983230072969 + 3 ^ 40 * 7592860 * 2
def baseEnd_7592860 : Nat := 3898786722297268134031079

theorem tailTrace_7592860 : CollatzResearch.WordTrace tailWord_7592860 prefixEnd_7592860 3898786722297268134031079 := by
  unfold tailWord_7592860
  simp only [CollatzResearch.WordTrace]
  refine ⟨138467177636186226046496017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184622903514914968061994689 138467177636186226046496017)
  ·
    refine ⟨103850383227139669534872013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138467177636186226046496017 103850383227139669534872013)
    ·
      refine ⟨38943893710177376075577005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103850383227139669534872013 38943893710177376075577005)
      ·
        refine ⟨14603960141316516028341377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38943893710177376075577005 14603960141316516028341377)
        ·
          refine ⟨10952970105987387021256033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14603960141316516028341377 10952970105987387021256033)
          ·
            refine ⟨8214727579490540265942025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10952970105987387021256033 8214727579490540265942025)
            ·
              refine ⟨6161045684617905199456519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8214727579490540265942025 6161045684617905199456519)
              ·
                refine ⟨9241568526926857799184779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6161045684617905199456519 9241568526926857799184779)
                ·
                  refine ⟨13862352790390286698777169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9241568526926857799184779 13862352790390286698777169)
                  ·
                    refine ⟨10396764592792715024082877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13862352790390286698777169 10396764592792715024082877)
                    ·
                      refine ⟨3898786722297268134031079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10396764592792715024082877 3898786722297268134031079)
                      ·
                        rfl

theorem cell23_7592860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_7592860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592860 prefixEnd_7592860 := by exact prefixLift 7592860
  have htrace : WordTrace (prefixWord ++ tailWord_7592860) baseStart_7592860 baseEnd_7592860 := by
    simpa [prefixWord, tailWord_7592860, baseEnd_7592860] using wordTrace_append hprefix tailTrace_7592860
  have hstable : (prefixWord ++ tailWord_7592860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592860).length < 2 ^ (prefixWord ++ tailWord_7592860).sum := by decide
  have hdescent : baseEnd_7592860 < baseStart_7592860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592882 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_7592882 : Nat := 118140960795 + 7592882 * 2 ^ 59
def prefixEnd_7592882 : Nat := 4983230072969 + 3 ^ 40 * 7592882 * 2
def baseEnd_7592882 : Nat := 3898798018871667047955977

theorem tailTrace_7592882 : CollatzResearch.WordTrace tailWord_7592882 prefixEnd_7592882 3898798018871667047955977 := by
  unfold tailWord_7592882
  simp only [CollatzResearch.WordTrace]
  refine ⟨69233789419573187462573225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184623438452195166566861933 69233789419573187462573225)
  ·
    refine ⟨51925342064679890596929919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69233789419573187462573225 51925342064679890596929919)
    ·
      refine ⟨77888013097019835895394879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51925342064679890596929919 77888013097019835895394879)
      ·
        refine ⟨116832019645529753843092319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77888013097019835895394879 116832019645529753843092319)
        ·
          refine ⟨175248029468294630764638479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116832019645529753843092319 175248029468294630764638479)
          ·
            refine ⟨262872044202441946146957719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175248029468294630764638479 262872044202441946146957719)
            ·
              refine ⟨394308066303662919220436579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262872044202441946146957719 394308066303662919220436579)
              ·
                refine ⟨591462099455494378830654869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394308066303662919220436579 591462099455494378830654869)
                ·
                  refine ⟨27724785911976299007686947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 591462099455494378830654869 27724785911976299007686947)
                  ·
                    refine ⟨41587178867964448511530421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27724785911976299007686947 41587178867964448511530421)
                    ·
                      refine ⟨3898798018871667047955977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41587178867964448511530421 3898798018871667047955977)
                      ·
                        rfl

theorem cell23_7592882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_7592882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592882 prefixEnd_7592882 := by exact prefixLift 7592882
  have htrace : WordTrace (prefixWord ++ tailWord_7592882) baseStart_7592882 baseEnd_7592882 := by
    simpa [prefixWord, tailWord_7592882, baseEnd_7592882] using wordTrace_append hprefix tailTrace_7592882
  have hstable : (prefixWord ++ tailWord_7592882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592882).length < 2 ^ (prefixWord ++ tailWord_7592882).sum := by decide
  have hdescent : baseEnd_7592882 < baseStart_7592882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592896 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 1, 4, 2]
def baseStart_7592896 : Nat := 118140960795 + 7592896 * 2 ^ 59
def prefixEnd_7592896 : Nat := 4983230072969 + 3 ^ 40 * 7592896 * 2
def baseEnd_7592896 : Nat := 3898805207600829993180913

theorem tailTrace_7592896 : CollatzResearch.WordTrace tailWord_7592896 prefixEnd_7592896 3898805207600829993180913 := by
  unfold tailWord_7592896
  simp only [CollatzResearch.WordTrace]
  refine ⟨138467834150121015120651271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184623778866828020160868361 138467834150121015120651271)
  ·
    refine ⟨207701751225181522680976907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138467834150121015120651271 207701751225181522680976907)
    ·
      refine ⟨311552626837772284021465361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207701751225181522680976907 311552626837772284021465361)
      ·
        refine ⟨233664470128329213016099021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311552626837772284021465361 233664470128329213016099021)
        ·
          refine ⟨87624176298123454881037133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233664470128329213016099021 87624176298123454881037133)
          ·
            refine ⟨32859066111796295580388925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87624176298123454881037133 32859066111796295580388925)
            ·
              refine ⟨12322149791923610842645847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32859066111796295580388925 12322149791923610842645847)
              ·
                refine ⟨18483224687885416263968771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12322149791923610842645847 18483224687885416263968771)
                ·
                  refine ⟨27724837031828124395953157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18483224687885416263968771 27724837031828124395953157)
                  ·
                    refine ⟨5198406943467773324241217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27724837031828124395953157 5198406943467773324241217)
                    ·
                      refine ⟨3898805207600829993180913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198406943467773324241217 3898805207600829993180913)
                      ·
                        rfl

theorem cell23_7592896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 4, 2].length) (baseStart_7592896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592896 prefixEnd_7592896 := by exact prefixLift 7592896
  have htrace : WordTrace (prefixWord ++ tailWord_7592896) baseStart_7592896 baseEnd_7592896 := by
    simpa [prefixWord, tailWord_7592896, baseEnd_7592896] using wordTrace_append hprefix tailTrace_7592896
  have hstable : (prefixWord ++ tailWord_7592896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592896).length < 2 ^ (prefixWord ++ tailWord_7592896).sum := by decide
  have hdescent : baseEnd_7592896 < baseStart_7592896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592919 : List Nat := [1, 1, 3, 2, 1, 1, 2, 7, 5]
def baseStart_7592919 : Nat := 118140960795 + 7592919 * 2 ^ 59
def prefixEnd_7592919 : Nat := 4983230072969 + 3 ^ 40 * 7592919 * 2
def baseEnd_7592919 : Nat := 433201890850653711465923

theorem tailTrace_7592919 : CollatzResearch.WordTrace tailWord_7592919 prefixEnd_7592919 433201890850653711465923 := by
  unfold tailWord_7592919
  simp only [CollatzResearch.WordTrace]
  refine ⟨276936507179158705169389811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184624338119439136779593207 276936507179158705169389811)
  ·
    refine ⟨415404760768738057754084717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276936507179158705169389811 415404760768738057754084717)
    ·
      refine ⟨155776785288276771657781769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415404760768738057754084717 155776785288276771657781769)
      ·
        refine ⟨116832588966207578743336327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155776785288276771657781769 116832588966207578743336327)
        ·
          refine ⟨175248883449311368115004491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116832588966207578743336327 175248883449311368115004491)
          ·
            refine ⟨262873325173967052172506737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175248883449311368115004491 262873325173967052172506737)
            ·
              refine ⟨197154993880475289129380053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262873325173967052172506737 197154993880475289129380053)
              ·
                refine ⟨4620820169073639588969845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 197154993880475289129380053 4620820169073639588969845)
                ·
                  refine ⟨433201890850653711465923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4620820169073639588969845 433201890850653711465923)
                  ·
                    rfl

theorem cell23_7592919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 5].length) (baseStart_7592919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592919 prefixEnd_7592919 := by exact prefixLift 7592919
  have htrace : WordTrace (prefixWord ++ tailWord_7592919) baseStart_7592919 baseEnd_7592919 := by
    simpa [prefixWord, tailWord_7592919, baseEnd_7592919] using wordTrace_append hprefix tailTrace_7592919
  have hstable : (prefixWord ++ tailWord_7592919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592919).length < 2 ^ (prefixWord ++ tailWord_7592919).sum := by decide
  have hdescent : baseEnd_7592919 < baseStart_7592919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592930 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_7592930 : Nat := 118140960795 + 7592930 * 2 ^ 59
def prefixEnd_7592930 : Nat := 4983230072969 + 3 ^ 40 * 7592930 * 2
def baseEnd_7592930 : Nat := 3898822665943082860155757

theorem tailTrace_7592930 : CollatzResearch.WordTrace tailWord_7592930 prefixEnd_7592930 3898822665943082860155757 := by
  unfold tailWord_7592930
  simp only [CollatzResearch.WordTrace]
  refine ⟨69234227095529713512010061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184624605588079236032026829 69234227095529713512010061)
  ·
    refine ⟨25962835160823642567003773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69234227095529713512010061 25962835160823642567003773)
    ·
      refine ⟨9736063185308865962626415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25962835160823642567003773 9736063185308865962626415)
      ·
        refine ⟨14604094777963298943939623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9736063185308865962626415 14604094777963298943939623)
        ·
          refine ⟨21906142166944948415909435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14604094777963298943939623 21906142166944948415909435)
          ·
            refine ⟨32859213250417422623864153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21906142166944948415909435 32859213250417422623864153)
            ·
              refine ⟨24644409937813066967898115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32859213250417422623864153 24644409937813066967898115)
              ·
                refine ⟨36966614906719600451847173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24644409937813066967898115 36966614906719600451847173)
                ·
                  refine ⟨6931240295009925084721345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36966614906719600451847173 6931240295009925084721345)
                  ·
                    refine ⟨5198430221257443813541009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6931240295009925084721345 5198430221257443813541009)
                    ·
                      refine ⟨3898822665943082860155757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198430221257443813541009 3898822665943082860155757)
                      ·
                        rfl

theorem cell23_7592930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_7592930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592930 prefixEnd_7592930 := by exact prefixLift 7592930
  have htrace : WordTrace (prefixWord ++ tailWord_7592930) baseStart_7592930 baseEnd_7592930 := by
    simpa [prefixWord, tailWord_7592930, baseEnd_7592930] using wordTrace_append hprefix tailTrace_7592930
  have hstable : (prefixWord ++ tailWord_7592930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592930).length < 2 ^ (prefixWord ++ tailWord_7592930).sum := by decide
  have hdescent : baseEnd_7592930 < baseStart_7592930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592932 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_7592932 : Nat := 118140960795 + 7592932 * 2 ^ 59
def prefixEnd_7592932 : Nat := 4983230072969 + 3 ^ 40 * 7592932 * 2
def baseEnd_7592932 : Nat := 1299607897634797284110249

theorem tailTrace_7592932 : CollatzResearch.WordTrace tailWord_7592932 prefixEnd_7592932 1299607897634797284110249 := by
  unfold tailWord_7592932
  simp only [CollatzResearch.WordTrace]
  refine ⟨138468490664055804194806525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184624654218741072259742033 138468490664055804194806525)
  ·
    refine ⟨51925683999020926573052447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138468490664055804194806525 51925683999020926573052447)
    ·
      refine ⟨77888525998531389859578671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51925683999020926573052447 77888525998531389859578671)
      ·
        refine ⟨116832788997797084789368007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77888525998531389859578671 116832788997797084789368007)
        ·
          refine ⟨175249183496695627184052011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116832788997797084789368007 175249183496695627184052011)
          ·
            refine ⟨262873775245043440776078017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175249183496695627184052011 262873775245043440776078017)
            ·
              refine ⟨197155331433782580582058513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262873775245043440776078017 197155331433782580582058513)
              ·
                refine ⟨147866498575336935436543885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197155331433782580582058513 147866498575336935436543885)
                ·
                  refine ⟨55449936965751350788703957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147866498575336935436543885 55449936965751350788703957)
                  ·
                    refine ⟨1299607897634797284110249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55449936965751350788703957 1299607897634797284110249)
                    ·
                      rfl

theorem cell23_7592932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_7592932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592932 prefixEnd_7592932 := by exact prefixLift 7592932
  have htrace : WordTrace (prefixWord ++ tailWord_7592932) baseStart_7592932 baseEnd_7592932 := by
    simpa [prefixWord, tailWord_7592932, baseEnd_7592932] using wordTrace_append hprefix tailTrace_7592932
  have hstable : (prefixWord ++ tailWord_7592932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592932).length < 2 ^ (prefixWord ++ tailWord_7592932).sum := by decide
  have hdescent : baseEnd_7592932 < baseStart_7592932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7592986 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2]
def baseStart_7592986 : Nat := 118140960795 + 7592986 * 2 ^ 59
def prefixEnd_7592986 : Nat := 4983230072969 + 3 ^ 40 * 7592986 * 2
def baseEnd_7592986 : Nat := 3898851420859734641055499

theorem tailTrace_7592986 : CollatzResearch.WordTrace tailWord_7592986 prefixEnd_7592986 3898851420859734641055499 := by
  unfold tailWord_7592986
  simp only [CollatzResearch.WordTrace]
  refine ⟨69234737717478993903019703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184625967246610650408052541 69234737717478993903019703)
  ·
    refine ⟨103852106576218490854529555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69234737717478993903019703 103852106576218490854529555)
    ·
      refine ⟨155778159864327736281794333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103852106576218490854529555 155778159864327736281794333)
      ·
        refine ⟨58416809949122901105672875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155778159864327736281794333 58416809949122901105672875)
        ·
          refine ⟨87625214923684351658509313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58416809949122901105672875 87625214923684351658509313)
          ·
            refine ⟨65718911192763263743881985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87625214923684351658509313 65718911192763263743881985)
            ·
              refine ⟨49289183394572447807911489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65718911192763263743881985 49289183394572447807911489)
              ·
                refine ⟨36966887545929335855933617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49289183394572447807911489 36966887545929335855933617)
                ·
                  refine ⟨27725165659447001891950213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36966887545929335855933617 27725165659447001891950213)
                  ·
                    refine ⟨5198468561146312854740665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27725165659447001891950213 5198468561146312854740665)
                    ·
                      refine ⟨3898851420859734641055499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198468561146312854740665 3898851420859734641055499)
                      ·
                        rfl

theorem cell23_7592986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_7592986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7592986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7592986 prefixEnd_7592986 := by exact prefixLift 7592986
  have htrace : WordTrace (prefixWord ++ tailWord_7592986) baseStart_7592986 baseEnd_7592986 := by
    simpa [prefixWord, tailWord_7592986, baseEnd_7592986] using wordTrace_append hprefix tailTrace_7592986
  have hstable : (prefixWord ++ tailWord_7592986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7592986).length < 2 ^ (prefixWord ++ tailWord_7592986).sum := by decide
  have hdescent : baseEnd_7592986 < baseStart_7592986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7592986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593006 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_7593006 : Nat := 118140960795 + 7593006 * 2 ^ 59
def prefixEnd_7593006 : Nat := 4983230072969 + 3 ^ 40 * 7593006 * 2
def baseEnd_7593006 : Nat := 3898861690472824562805407

theorem tailTrace_7593006 : CollatzResearch.WordTrace tailWord_7593006 prefixEnd_7593006 3898861690472824562805407 := by
  unfold tailWord_7593006
  simp only [CollatzResearch.WordTrace]
  refine ⟨34617460041230439878475859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184626453553229012685204581 34617460041230439878475859)
  ·
    refine ⟨51926190061845659817713789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34617460041230439878475859 51926190061845659817713789)
    ·
      refine ⟨19472321273192122431642671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51926190061845659817713789 19472321273192122431642671)
      ·
        refine ⟨29208481909788183647464007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19472321273192122431642671 29208481909788183647464007)
        ·
          refine ⟨43812722864682275471196011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29208481909788183647464007 43812722864682275471196011)
          ·
            refine ⟨65719084297023413206794017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43812722864682275471196011 65719084297023413206794017)
            ·
              refine ⟨49289313222767559905095513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65719084297023413206794017 49289313222767559905095513)
              ·
                refine ⟨36966984917075669928821635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49289313222767559905095513 36966984917075669928821635)
                ·
                  refine ⟨55450477375613504893232453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36966984917075669928821635 55450477375613504893232453)
                  ·
                    refine ⟨10396964507927532167481085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55450477375613504893232453 10396964507927532167481085)
                    ·
                      refine ⟨3898861690472824562805407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10396964507927532167481085 3898861690472824562805407)
                      ·
                        rfl

theorem cell23_7593006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_7593006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593006 prefixEnd_7593006 := by exact prefixLift 7593006
  have htrace : WordTrace (prefixWord ++ tailWord_7593006) baseStart_7593006 baseEnd_7593006 := by
    simpa [prefixWord, tailWord_7593006, baseEnd_7593006] using wordTrace_append hprefix tailTrace_7593006
  have hstable : (prefixWord ++ tailWord_7593006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593006).length < 2 ^ (prefixWord ++ tailWord_7593006).sum := by decide
  have hdescent : baseEnd_7593006 < baseStart_7593006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593009 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 6]
def baseStart_7593009 : Nat := 118140960795 + 7593009 * 2 ^ 59
def prefixEnd_7593009 : Nat := 4983230072969 + 3 ^ 40 * 7593009 * 2
def baseEnd_7593009 : Nat := 433207025657198672340877

theorem tailTrace_7593009 : CollatzResearch.WordTrace tailWord_7593009 prefixEnd_7593009 433207025657198672340877 := by
  unfold tailWord_7593009
  simp only [CollatzResearch.WordTrace]
  refine ⟨276939789748832650540166081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184626526499221767026777387 276939789748832650540166081)
  ·
    refine ⟨207704842311624487905124561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276939789748832650540166081 207704842311624487905124561)
    ·
      refine ⟨155778631733718365928843421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207704842311624487905124561 155778631733718365928843421)
      ·
        refine ⟨58416986900144387223316283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155778631733718365928843421 58416986900144387223316283)
        ·
          refine ⟨87625480350216580834974425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58416986900144387223316283 87625480350216580834974425)
          ·
            refine ⟨65719110262662435626230819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87625480350216580834974425 65719110262662435626230819)
            ·
              refine ⟨98578665393993653439346229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65719110262662435626230819 98578665393993653439346229)
              ·
                refine ⟨9241749880686905009938709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98578665393993653439346229 9241749880686905009938709)
                ·
                  refine ⟨433207025657198672340877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9241749880686905009938709 433207025657198672340877)
                  ·
                    rfl

theorem cell23_7593009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 6].length) (baseStart_7593009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593009 prefixEnd_7593009 := by exact prefixLift 7593009
  have htrace : WordTrace (prefixWord ++ tailWord_7593009) baseStart_7593009 baseEnd_7593009 := by
    simpa [prefixWord, tailWord_7593009, baseEnd_7593009] using wordTrace_append hprefix tailTrace_7593009
  have hstable : (prefixWord ++ tailWord_7593009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593009).length < 2 ^ (prefixWord ++ tailWord_7593009).sum := by decide
  have hdescent : baseEnd_7593009 < baseStart_7593009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593036 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 7, 1, 3]
def baseStart_7593036 : Nat := 118140960795 + 7593036 * 2 ^ 59
def prefixEnd_7593036 : Nat := 4983230072969 + 3 ^ 40 * 7593036 * 2
def baseEnd_7593036 : Nat := 3898877094892459445430269

theorem tailTrace_7593036 : CollatzResearch.WordTrace tailWord_7593036 prefixEnd_7593036 3898877094892459445430269 := by
  unfold tailWord_7593036
  simp only [CollatzResearch.WordTrace]
  refine ⟨138470387259867417075699481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184627183013156556100932641 138470387259867417075699481)
  ·
    refine ⟨103852790444900562806774611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138470387259867417075699481 103852790444900562806774611)
    ·
      refine ⟨155779185667350844210161917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103852790444900562806774611 155779185667350844210161917)
      ·
        refine ⟨58417194625256566578810719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155779185667350844210161917 58417194625256566578810719)
        ·
          refine ⟨87625791937884849868216079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58417194625256566578810719 87625791937884849868216079)
          ·
            refine ⟨131438687906827274802324119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87625791937884849868216079 131438687906827274802324119)
            ·
              refine ⟨197158031860240912203486179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131438687906827274802324119 197158031860240912203486179)
              ·
                refine ⟨295737047790361368305229269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197158031860240912203486179 295737047790361368305229269)
                ·
                  refine ⟨6931337057586594569653811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 295737047790361368305229269 6931337057586594569653811)
                  ·
                    refine ⟨10397005586379891854480717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6931337057586594569653811 10397005586379891854480717)
                    ·
                      refine ⟨3898877094892459445430269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10397005586379891854480717 3898877094892459445430269)
                      ·
                        rfl

theorem cell23_7593036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_7593036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593036 prefixEnd_7593036 := by exact prefixLift 7593036
  have htrace : WordTrace (prefixWord ++ tailWord_7593036) baseStart_7593036 baseEnd_7593036 := by
    simpa [prefixWord, tailWord_7593036, baseEnd_7593036] using wordTrace_append hprefix tailTrace_7593036
  have hstable : (prefixWord ++ tailWord_7593036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593036).length < 2 ^ (prefixWord ++ tailWord_7593036).sum := by decide
  have hdescent : baseEnd_7593036 < baseStart_7593036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593079 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_7593079 : Nat := 118140960795 + 7593079 * 2 ^ 59
def prefixEnd_7593079 : Nat := 4983230072969 + 3 ^ 40 * 7593079 * 2
def baseEnd_7593079 : Nat := 3898899174560602777192571

theorem tailTrace_7593079 : CollatzResearch.WordTrace tailWord_7593079 prefixEnd_7593079 3898899174560602777192571 := by
  unfold tailWord_7593079
  simp only [CollatzResearch.WordTrace]
  refine ⟨276942342858579052495214291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184628228572386034996809527 276942342858579052495214291)
  ·
    refine ⟨415413514287868578742821437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276942342858579052495214291 415413514287868578742821437)
    ·
      refine ⟨155780067857950717028558039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415413514287868578742821437 155780067857950717028558039)
      ·
        refine ⟨233670101786926075542837059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155780067857950717028558039 233670101786926075542837059)
        ·
          refine ⟨350505152680389113314255589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233670101786926075542837059 350505152680389113314255589)
          ·
            refine ⟨65719716127572958746422923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350505152680389113314255589 65719716127572958746422923)
            ·
              refine ⟨98579574191359438119634385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65719716127572958746422923 98579574191359438119634385)
              ·
                refine ⟨73934680643519578589725789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98579574191359438119634385 73934680643519578589725789)
                ·
                  refine ⟨27725505241319841971147171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73934680643519578589725789 27725505241319841971147171)
                  ·
                    refine ⟨41588257861979762956720757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27725505241319841971147171 41588257861979762956720757)
                    ·
                      refine ⟨3898899174560602777192571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41588257861979762956720757 3898899174560602777192571)
                      ·
                        rfl

theorem cell23_7593079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_7593079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593079 prefixEnd_7593079 := by exact prefixLift 7593079
  have htrace : WordTrace (prefixWord ++ tailWord_7593079) baseStart_7593079 baseEnd_7593079 := by
    simpa [prefixWord, tailWord_7593079, baseEnd_7593079] using wordTrace_append hprefix tailTrace_7593079
  have hstable : (prefixWord ++ tailWord_7593079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593079).length < 2 ^ (prefixWord ++ tailWord_7593079).sum := by decide
  have hdescent : baseEnd_7593079 < baseStart_7593079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593106 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_7593106 : Nat := 118140960795 + 7593106 * 2 ^ 59
def prefixEnd_7593106 : Nat := 4983230072969 + 3 ^ 40 * 7593106 * 2
def baseEnd_7593106 : Nat := 3898913038538274171554947

theorem tailTrace_7593106 : CollatzResearch.WordTrace tailWord_7593106 prefixEnd_7593106 3898913038538274171554947 := by
  unfold tailWord_7593106
  simp only [CollatzResearch.WordTrace]
  refine ⟨69235831907370309026611793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184628885086320824070964781 69235831907370309026611793)
  ·
    refine ⟨51926873930527731769958845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69235831907370309026611793 51926873930527731769958845)
    ·
      refine ⟨19472577723947899413734567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51926873930527731769958845 19472577723947899413734567)
      ·
        refine ⟨29208866585921849120601851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19472577723947899413734567 29208866585921849120601851)
        ·
          refine ⟨43813299878882773680902777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29208866585921849120601851 43813299878882773680902777)
          ·
            refine ⟨32859974909162080260677083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43813299878882773680902777 32859974909162080260677083)
            ·
              refine ⟨49289962363743120391015625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32859974909162080260677083 49289962363743120391015625)
              ·
                refine ⟨36967471772807340293261719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49289962363743120391015625 36967471772807340293261719)
                ·
                  refine ⟨55451207659211010439892579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36967471772807340293261719 55451207659211010439892579)
                  ·
                    refine ⟨83176811488816515659838869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55451207659211010439892579 83176811488816515659838869)
                    ·
                      refine ⟨3898913038538274171554947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83176811488816515659838869 3898913038538274171554947)
                      ·
                        rfl

theorem cell23_7593106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_7593106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593106 prefixEnd_7593106 := by exact prefixLift 7593106
  have htrace : WordTrace (prefixWord ++ tailWord_7593106) baseStart_7593106 baseEnd_7593106 := by
    simpa [prefixWord, tailWord_7593106, baseEnd_7593106] using wordTrace_append hprefix tailTrace_7593106
  have hstable : (prefixWord ++ tailWord_7593106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593106).length < 2 ^ (prefixWord ++ tailWord_7593106).sum := by decide
  have hdescent : baseEnd_7593106 < baseStart_7593106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593116 : List Nat := [2, 2, 3, 2, 1, 3, 2, 8]
def baseStart_7593116 : Nat := 118140960795 + 7593116 * 2 ^ 59
def prefixEnd_7593116 : Nat := 4983230072969 + 3 ^ 40 * 7593116 * 2
def baseEnd_7593116 : Nat := 144404376790548856756663

theorem tailTrace_7593116 : CollatzResearch.WordTrace tailWord_7593116 prefixEnd_7593116 144404376790548856756663 := by
  unfold tailWord_7593116
  simp only [CollatzResearch.WordTrace]
  refine ⟨138471846179722503907155601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184629128239630005209540801 138471846179722503907155601)
  ·
    refine ⟨103853884634791877930366701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138471846179722503907155601 103853884634791877930366701)
    ·
      refine ⟨38945206738046954223887513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103853884634791877930366701 38945206738046954223887513)
      ·
        refine ⟨29208905053535215667915635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38945206738046954223887513 29208905053535215667915635)
        ·
          refine ⟨43813357580302823501873453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29208905053535215667915635 43813357580302823501873453)
          ·
            refine ⟨16430009092613558813202545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43813357580302823501873453 16430009092613558813202545)
            ·
              refine ⟨12322506819460169109901909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16430009092613558813202545 12322506819460169109901909)
              ·
                refine ⟨144404376790548856756663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12322506819460169109901909 144404376790548856756663)
                ·
                  rfl

theorem cell23_7593116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 8].length) (baseStart_7593116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593116 prefixEnd_7593116 := by exact prefixLift 7593116
  have htrace : WordTrace (prefixWord ++ tailWord_7593116) baseStart_7593116 baseEnd_7593116 := by
    simpa [prefixWord, tailWord_7593116, baseEnd_7593116] using wordTrace_append hprefix tailTrace_7593116
  have hstable : (prefixWord ++ tailWord_7593116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593116).length < 2 ^ (prefixWord ++ tailWord_7593116).sum := by decide
  have hdescent : baseEnd_7593116 < baseStart_7593116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593130 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7593130 : Nat := 118140960795 + 7593130 * 2 ^ 59
def prefixEnd_7593130 : Nat := 4983230072969 + 3 ^ 40 * 7593130 * 2
def baseEnd_7593130 : Nat := 3898925362073982077654837

theorem tailTrace_7593130 : CollatzResearch.WordTrace tailWord_7593130 prefixEnd_7593130 3898925362073982077654837 := by
  unfold tailWord_7593130
  simp only [CollatzResearch.WordTrace]
  refine ⟨69236050745348572051330211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184629468654262858803547229 69236050745348572051330211)
  ·
    refine ⟨103854076118022858076995317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69236050745348572051330211 103854076118022858076995317)
    ·
      refine ⟨9736319636064642944718311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103854076118022858076995317 9736319636064642944718311)
      ·
        refine ⟨14604479454096964417077467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9736319636064642944718311 14604479454096964417077467)
        ·
          refine ⟨21906719181145446625616201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14604479454096964417077467 21906719181145446625616201)
          ·
            refine ⟨16430039385859084969212151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21906719181145446625616201 16430039385859084969212151)
            ·
              refine ⟨24645059078788627453818227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16430039385859084969212151 24645059078788627453818227)
              ·
                refine ⟨36967588618182941180727341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24645059078788627453818227 36967588618182941180727341)
                ·
                  refine ⟨13862845731818602942772753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36967588618182941180727341 13862845731818602942772753)
                  ·
                    refine ⟨10397134298863952207079565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13862845731818602942772753 10397134298863952207079565)
                    ·
                      refine ⟨3898925362073982077654837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10397134298863952207079565 3898925362073982077654837)
                      ·
                        rfl

theorem cell23_7593130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7593130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593130 prefixEnd_7593130 := by exact prefixLift 7593130
  have htrace : WordTrace (prefixWord ++ tailWord_7593130) baseStart_7593130 baseEnd_7593130 := by
    simpa [prefixWord, tailWord_7593130, baseEnd_7593130] using wordTrace_append hprefix tailTrace_7593130
  have hstable : (prefixWord ++ tailWord_7593130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593130).length < 2 ^ (prefixWord ++ tailWord_7593130).sum := by decide
  have hdescent : baseEnd_7593130 < baseStart_7593130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593136 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 2, 7, 2]
def baseStart_7593136 : Nat := 118140960795 + 7593136 * 2 ^ 59
def prefixEnd_7593136 : Nat := 4983230072969 + 3 ^ 40 * 7593136 * 2
def baseEnd_7593136 : Nat := 3898928442957909054179809

theorem tailTrace_7593136 : CollatzResearch.WordTrace tailWord_7593136 prefixEnd_7593136 3898928442957909054179809 := by
  unfold tailWord_7593136
  simp only [CollatzResearch.WordTrace]
  refine ⟨138472210909686275615019631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184629614546248367486692841 138472210909686275615019631)
  ·
    refine ⟨207708316364529413422529447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138472210909686275615019631 207708316364529413422529447)
    ·
      refine ⟨311562474546794120133794171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207708316364529413422529447 311562474546794120133794171)
      ·
        refine ⟨467343711820191180200691257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311562474546794120133794171 467343711820191180200691257)
        ·
          refine ⟨350507783865143385150518443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467343711820191180200691257 350507783865143385150518443)
          ·
            refine ⟨525761675797715077725777665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350507783865143385150518443 525761675797715077725777665)
            ·
              refine ⟨394321256848286308294333249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525761675797715077725777665 394321256848286308294333249)
              ·
                refine ⟨295740942636214731220749937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394321256848286308294333249 295740942636214731220749937)
                ·
                  refine ⟨221805706977161048415562453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295740942636214731220749937 221805706977161048415562453)
                  ·
                    refine ⟨5198571257277212072239745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 221805706977161048415562453 5198571257277212072239745)
                    ·
                      refine ⟨3898928442957909054179809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198571257277212072239745 3898928442957909054179809)
                      ·
                        rfl

theorem cell23_7593136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 7, 2].length) (baseStart_7593136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593136 prefixEnd_7593136 := by exact prefixLift 7593136
  have htrace : WordTrace (prefixWord ++ tailWord_7593136) baseStart_7593136 baseEnd_7593136 := by
    simpa [prefixWord, tailWord_7593136, baseEnd_7593136] using wordTrace_append hprefix tailTrace_7593136
  have hstable : (prefixWord ++ tailWord_7593136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593136).length < 2 ^ (prefixWord ++ tailWord_7593136).sum := by decide
  have hdescent : baseEnd_7593136 < baseStart_7593136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593139 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 5]
def baseStart_7593139 : Nat := 118140960795 + 7593139 * 2 ^ 59
def prefixEnd_7593139 : Nat := 4983230072969 + 3 ^ 40 * 7593139 * 2
def baseEnd_7593139 : Nat := 3898929983399872542442295

theorem tailTrace_7593139 : CollatzResearch.WordTrace tailWord_7593139 prefixEnd_7593139 3898929983399872542442295 := by
  unfold tailWord_7593139
  simp only [CollatzResearch.WordTrace]
  refine ⟨276944531238361682742398471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184629687492241121828265647 276944531238361682742398471)
  ·
    refine ⟨415416796857542524113597707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276944531238361682742398471 415416796857542524113597707)
    ·
      refine ⟨623125195286313786170396561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415416796857542524113597707 623125195286313786170396561)
      ·
        refine ⟨467343896464735339627797421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623125195286313786170396561 467343896464735339627797421)
        ·
          refine ⟨175253961174275752360424033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467343896464735339627797421 175253961174275752360424033)
          ·
            refine ⟨131440470880706814270318025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175253961174275752360424033 131440470880706814270318025)
            ·
              refine ⟨98580353160530110702738519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131440470880706814270318025 98580353160530110702738519)
              ·
                refine ⟨147870529740795166054107779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98580353160530110702738519 147870529740795166054107779)
                ·
                  refine ⟨221805794611192749081161669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147870529740795166054107779 221805794611192749081161669)
                  ·
                    refine ⟨41588586489598640452717813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221805794611192749081161669 41588586489598640452717813)
                    ·
                      refine ⟨3898929983399872542442295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41588586489598640452717813 3898929983399872542442295)
                      ·
                        rfl

theorem cell23_7593139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_7593139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593139 prefixEnd_7593139 := by exact prefixLift 7593139
  have htrace : WordTrace (prefixWord ++ tailWord_7593139) baseStart_7593139 baseEnd_7593139 := by
    simpa [prefixWord, tailWord_7593139, baseEnd_7593139] using wordTrace_append hprefix tailTrace_7593139
  have hstable : (prefixWord ++ tailWord_7593139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593139).length < 2 ^ (prefixWord ++ tailWord_7593139).sum := by decide
  have hdescent : baseEnd_7593139 < baseStart_7593139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593154 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_7593154 : Nat := 118140960795 + 7593154 * 2 ^ 59
def prefixEnd_7593154 : Nat := 4983230072969 + 3 ^ 40 * 7593154 * 2
def baseEnd_7593154 : Nat := 1299645895203229994584909

theorem tailTrace_7593154 : CollatzResearch.WordTrace tailWord_7593154 prefixEnd_7593154 1299645895203229994584909 := by
  unfold tailWord_7593154
  simp only [CollatzResearch.WordTrace]
  refine ⟨69236269583326835076048629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184630052222204893536129677 69236269583326835076048629)
  ·
    refine ⟨6490900273436890788379559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69236269583326835076048629 6490900273436890788379559)
    ·
      refine ⟨9736350410155336182569339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6490900273436890788379559 9736350410155336182569339)
      ·
        refine ⟨14604525615233004273854009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9736350410155336182569339 14604525615233004273854009)
        ·
          refine ⟨10953394211424753205390507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14604525615233004273854009 10953394211424753205390507)
          ·
            refine ⟨16430091317137129808085761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10953394211424753205390507 16430091317137129808085761)
            ·
              refine ⟨12322568487852847356064321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16430091317137129808085761 12322568487852847356064321)
              ·
                refine ⟨9241926365889635517048241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12322568487852847356064321 9241926365889635517048241)
                ·
                  refine ⟨6931444774417226637786181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9241926365889635517048241 6931444774417226637786181)
                  ·
                    refine ⟨1299645895203229994584909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6931444774417226637786181 1299645895203229994584909)
                    ·
                      rfl

theorem cell23_7593154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_7593154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593154 prefixEnd_7593154 := by exact prefixLift 7593154
  have htrace : WordTrace (prefixWord ++ tailWord_7593154) baseStart_7593154 baseEnd_7593154 := by
    simpa [prefixWord, tailWord_7593154, baseEnd_7593154] using wordTrace_append hprefix tailTrace_7593154
  have hstable : (prefixWord ++ tailWord_7593154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593154).length < 2 ^ (prefixWord ++ tailWord_7593154).sum := by decide
  have hdescent : baseEnd_7593154 < baseStart_7593154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593159 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 3, 8]
def baseStart_7593159 : Nat := 118140960795 + 7593159 * 2 ^ 59
def prefixEnd_7593159 : Nat := 4983230072969 + 3 ^ 40 * 7593159 * 2
def baseEnd_7593159 : Nat := 1299646751004320821397401

theorem tailTrace_7593159 : CollatzResearch.WordTrace tailWord_7593159 prefixEnd_7593159 1299646751004320821397401 := by
  unfold tailWord_7593159
  simp only [CollatzResearch.WordTrace]
  refine ⟨276945260698289226158126531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184630173798859484105417687 276945260698289226158126531)
  ·
    refine ⟨415417891047433839237189797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276945260698289226158126531 415417891047433839237189797)
    ·
      refine ⟨77890854571393844856973087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415417891047433839237189797 77890854571393844856973087)
      ·
        refine ⟨116836281857090767285459631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77890854571393844856973087 116836281857090767285459631)
        ·
          refine ⟨175254422785636150928189447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116836281857090767285459631 175254422785636150928189447)
          ·
            refine ⟨262881634178454226392284171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175254422785636150928189447 262881634178454226392284171)
            ·
              refine ⟨394322451267681339588426257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262881634178454226392284171 394322451267681339588426257)
              ·
                refine ⟨295741838450761004691319693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394322451267681339588426257 295741838450761004691319693)
                ·
                  refine ⟨110903189419035376759244885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295741838450761004691319693 110903189419035376759244885)
                  ·
                    refine ⟨1299646751004320821397401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110903189419035376759244885 1299646751004320821397401)
                    ·
                      rfl

theorem cell23_7593159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_7593159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593159 prefixEnd_7593159 := by exact prefixLift 7593159
  have htrace : WordTrace (prefixWord ++ tailWord_7593159) baseStart_7593159 baseEnd_7593159 := by
    simpa [prefixWord, tailWord_7593159, baseEnd_7593159] using wordTrace_append hprefix tailTrace_7593159
  have hstable : (prefixWord ++ tailWord_7593159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593159).length < 2 ^ (prefixWord ++ tailWord_7593159).sum := by decide
  have hdescent : baseEnd_7593159 < baseStart_7593159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593183 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 1, 4, 2]
def baseStart_7593183 : Nat := 118140960795 + 7593183 * 2 ^ 59
def prefixEnd_7593183 : Nat := 4983230072969 + 3 ^ 40 * 7593183 * 2
def baseEnd_7593183 : Nat := 3898952576548670370292093

theorem tailTrace_7593183 : CollatzResearch.WordTrace tailWord_7593183 prefixEnd_7593183 3898952576548670370292093 := by
  unfold tailWord_7593183
  simp only [CollatzResearch.WordTrace]
  refine ⟨276946136050202278257000203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184630757366801518838000135 276946136050202278257000203)
  ·
    refine ⟨415419204075303417385500305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276946136050202278257000203 415419204075303417385500305)
    ·
      refine ⟨311564403056477563039125229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415419204075303417385500305 311564403056477563039125229)
      ·
        refine ⟨116836651146179086139671961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311564403056477563039125229 116836651146179086139671961)
        ·
          refine ⟨87627488359634314604753971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116836651146179086139671961 87627488359634314604753971)
          ·
            refine ⟨131441232539451471907130957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87627488359634314604753971 131441232539451471907130957)
            ·
              refine ⟨49290462202294301965174109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131441232539451471907130957 49290462202294301965174109)
              ·
                refine ⟨18483923325860363236940291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49290462202294301965174109 18483923325860363236940291)
                ·
                  refine ⟨27725884988790544855410437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18483923325860363236940291 27725884988790544855410437)
                  ·
                    refine ⟨5198603435398227160389457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27725884988790544855410437 5198603435398227160389457)
                    ·
                      refine ⟨3898952576548670370292093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198603435398227160389457 3898952576548670370292093)
                      ·
                        rfl

theorem cell23_7593183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_7593183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593183 prefixEnd_7593183 := by exact prefixLift 7593183
  have htrace : WordTrace (prefixWord ++ tailWord_7593183) baseStart_7593183 baseEnd_7593183 := by
    simpa [prefixWord, tailWord_7593183, baseEnd_7593183] using wordTrace_append hprefix tailTrace_7593183
  have hstable : (prefixWord ++ tailWord_7593183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593183).length < 2 ^ (prefixWord ++ tailWord_7593183).sum := by decide
  have hdescent : baseEnd_7593183 < baseStart_7593183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593206 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_7593206 : Nat := 118140960795 + 7593206 * 2 ^ 59
def prefixEnd_7593206 : Nat := 4983230072969 + 3 ^ 40 * 7593206 * 2
def baseEnd_7593206 : Nat := 433218265178191531144943

theorem tailTrace_7593206 : CollatzResearch.WordTrace tailWord_7593206 prefixEnd_7593206 433218265178191531144943 := by
  unfold tailWord_7593206
  simp only [CollatzResearch.WordTrace]
  refine ⟨17309185933069934574067967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184631316619412635456724981 17309185933069934574067967)
  ·
    refine ⟨25963778899604901861101951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17309185933069934574067967 25963778899604901861101951)
    ·
      refine ⟨38945668349407352791652927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25963778899604901861101951 38945668349407352791652927)
      ·
        refine ⟨58418502524111029187479391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38945668349407352791652927 58418502524111029187479391)
        ·
          refine ⟨87627753786166543781219087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58418502524111029187479391 87627753786166543781219087)
          ·
            refine ⟨131441630679249815671828631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87627753786166543781219087 131441630679249815671828631)
            ·
              refine ⟨197162446018874723507742947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131441630679249815671828631 197162446018874723507742947)
              ·
                refine ⟨295743669028312085261614421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197162446018874723507742947 295743669028312085261614421)
                ·
                  refine ⟨433218265178191531144943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 295743669028312085261614421 433218265178191531144943)
                  ·
                    rfl

theorem cell23_7593206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_7593206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593206 prefixEnd_7593206 := by exact prefixLift 7593206
  have htrace : WordTrace (prefixWord ++ tailWord_7593206) baseStart_7593206 baseEnd_7593206 := by
    simpa [prefixWord, tailWord_7593206, baseEnd_7593206] using wordTrace_append hprefix tailTrace_7593206
  have hstable : (prefixWord ++ tailWord_7593206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593206).length < 2 ^ (prefixWord ++ tailWord_7593206).sum := by decide
  have hdescent : baseEnd_7593206 < baseStart_7593206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593217 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_7593217 : Nat := 118140960795 + 7593217 * 2 ^ 59
def prefixEnd_7593217 : Nat := 4983230072969 + 3 ^ 40 * 7593217 * 2
def baseEnd_7593217 : Nat := 3898970034890923237266937

theorem tailTrace_7593217 : CollatzResearch.WordTrace tailWord_7593217 prefixEnd_7593217 3898970034890923237266937 := by
  unfold tailWord_7593217
  simp only [CollatzResearch.WordTrace]
  refine ⟨276947376132079102063737905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184631584088052734709158603 276947376132079102063737905)
  ·
    refine ⟨207710532099059326547803429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276947376132079102063737905 207710532099059326547803429)
    ·
      refine ⟨38945724768573623727713143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207710532099059326547803429 38945724768573623727713143)
      ·
        refine ⟨58418587152860435591569715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38945724768573623727713143 58418587152860435591569715)
        ·
          refine ⟨87627880729290653387354573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58418587152860435591569715 87627880729290653387354573)
          ·
            refine ⟨32860455273483995020257965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87627880729290653387354573 32860455273483995020257965)
            ·
              refine ⟨12322670727556498132596737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32860455273483995020257965 12322670727556498132596737)
              ·
                refine ⟨9242003045667373599447553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12322670727556498132596737 9242003045667373599447553)
                ·
                  refine ⟨6931502284250530199585665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9242003045667373599447553 6931502284250530199585665)
                  ·
                    refine ⟨5198626713187897649689249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6931502284250530199585665 5198626713187897649689249)
                    ·
                      refine ⟨3898970034890923237266937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198626713187897649689249 3898970034890923237266937)
                      ·
                        rfl

theorem cell23_7593217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_7593217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593217 prefixEnd_7593217 := by exact prefixLift 7593217
  have htrace : WordTrace (prefixWord ++ tailWord_7593217) baseStart_7593217 baseEnd_7593217 := by
    simpa [prefixWord, tailWord_7593217, baseEnd_7593217] using wordTrace_append hprefix tailTrace_7593217
  have hstable : (prefixWord ++ tailWord_7593217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593217).length < 2 ^ (prefixWord ++ tailWord_7593217).sum := by decide
  have hdescent : baseEnd_7593217 < baseStart_7593217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593336 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_7593336 : Nat := 118140960795 + 7593336 * 2 ^ 59
def prefixEnd_7593336 : Nat := 4983230072969 + 3 ^ 40 * 7593336 * 2
def baseEnd_7593336 : Nat := 3899031139088808271678889

theorem tailTrace_7593336 : CollatzResearch.WordTrace tailWord_7593336 prefixEnd_7593336 3899031139088808271678889 := by
  unfold tailWord_7593336
  simp only [CollatzResearch.WordTrace]
  refine ⟨138475858209323992693659931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184634477612431990258213241 138475858209323992693659931)
  ·
    refine ⟨207713787313985989040489897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138475858209323992693659931 207713787313985989040489897)
    ·
      refine ⟨155785340485489491780367423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207713787313985989040489897 155785340485489491780367423)
      ·
        refine ⟨233678010728234237670551135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155785340485489491780367423 233678010728234237670551135)
        ·
          refine ⟨350517016092351356505826703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233678010728234237670551135 350517016092351356505826703)
          ·
            refine ⟨525775524138527034758740055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350517016092351356505826703 525775524138527034758740055)
            ·
              refine ⟨788663286207790552138110083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525775524138527034758740055 788663286207790552138110083)
              ·
                refine ⟨1182994929311685828207165125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788663286207790552138110083 1182994929311685828207165125)
                ·
                  refine ⟨221811549245941092788843461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1182994929311685828207165125 221811549245941092788843461)
                  ·
                    refine ⟨41589665483613954897908149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221811549245941092788843461 41589665483613954897908149)
                    ·
                      refine ⟨3899031139088808271678889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41589665483613954897908149 3899031139088808271678889)
                      ·
                        rfl

theorem cell23_7593336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_7593336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593336 prefixEnd_7593336 := by exact prefixLift 7593336
  have htrace : WordTrace (prefixWord ++ tailWord_7593336) baseStart_7593336 baseEnd_7593336 := by
    simpa [prefixWord, tailWord_7593336, baseEnd_7593336] using wordTrace_append hprefix tailTrace_7593336
  have hstable : (prefixWord ++ tailWord_7593336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593336).length < 2 ^ (prefixWord ++ tailWord_7593336).sum := by decide
  have hdescent : baseEnd_7593336 < baseStart_7593336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593340 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_7593340 : Nat := 118140960795 + 7593340 * 2 ^ 59
def prefixEnd_7593340 : Nat := 4983230072969 + 3 ^ 40 * 7593340 * 2
def baseEnd_7593340 : Nat := 3899033193011426256028871

theorem tailTrace_7593340 : CollatzResearch.WordTrace tailWord_7593340 prefixEnd_7593340 3899033193011426256028871 := by
  unfold tailWord_7593340
  simp only [CollatzResearch.WordTrace]
  refine ⟨138475931155316747035232737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184634574873755662713643649 138475931155316747035232737)
  ·
    refine ⟨103856948366487560276424553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138475931155316747035232737 103856948366487560276424553)
    ·
      refine ⟨77892711274865670207318415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103856948366487560276424553 77892711274865670207318415)
      ·
        refine ⟨116839066912298505310977623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77892711274865670207318415 116839066912298505310977623)
        ·
          refine ⟨175258600368447757966466435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116839066912298505310977623 175258600368447757966466435)
          ·
            refine ⟨262887900552671636949699653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175258600368447757966466435 262887900552671636949699653)
            ·
              refine ⟨49291481353625931928068685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262887900552671636949699653 49291481353625931928068685)
              ·
                refine ⟨18484305507609724473025757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49291481353625931928068685 18484305507609724473025757)
                ·
                  refine ⟨6931614565353646677384659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18484305507609724473025757 6931614565353646677384659)
                  ·
                    refine ⟨10397421848030470016076989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6931614565353646677384659 10397421848030470016076989)
                    ·
                      refine ⟨3899033193011426256028871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10397421848030470016076989 3899033193011426256028871)
                      ·
                        rfl

theorem cell23_7593340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_7593340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593340 prefixEnd_7593340 := by exact prefixLift 7593340
  have htrace : WordTrace (prefixWord ++ tailWord_7593340) baseStart_7593340 baseEnd_7593340 := by
    simpa [prefixWord, tailWord_7593340, baseEnd_7593340] using wordTrace_append hprefix tailTrace_7593340
  have hstable : (prefixWord ++ tailWord_7593340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593340).length < 2 ^ (prefixWord ++ tailWord_7593340).sum := by decide
  have hdescent : baseEnd_7593340 < baseStart_7593340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593393 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_7593393 : Nat := 118140960795 + 7593393 * 2 ^ 59
def prefixEnd_7593393 : Nat := 4983230072969 + 3 ^ 40 * 7593393 * 2
def baseEnd_7593393 : Nat := 3899060407486114548666127

theorem tailTrace_7593393 : CollatzResearch.WordTrace tailWord_7593393 prefixEnd_7593393 3899060407486114548666127 := by
  unfold tailWord_7593393
  simp only [CollatzResearch.WordTrace]
  refine ⟨276953795379441484122144833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184635863586294322748096555 276953795379441484122144833)
  ·
    refine ⟨207715346534581113091608625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276953795379441484122144833 207715346534581113091608625)
    ·
      refine ⟨155786509900935834818706469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207715346534581113091608625 155786509900935834818706469)
      ·
        refine ⟨29209970606425469028507463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155786509900935834818706469 29209970606425469028507463)
        ·
          refine ⟨43814955909638203542761195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29209970606425469028507463 43814955909638203542761195)
          ·
            refine ⟨65722433864457305314141793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43814955909638203542761195 65722433864457305314141793)
            ·
              refine ⟨49291825398342978985606345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65722433864457305314141793 49291825398342978985606345)
              ·
                refine ⟨36968869048757234239204759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49291825398342978985606345 36968869048757234239204759)
                ·
                  refine ⟨55453303573135851358807139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36968869048757234239204759 55453303573135851358807139)
                  ·
                    refine ⟨83179955359703777038210709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55453303573135851358807139 83179955359703777038210709)
                    ·
                      refine ⟨3899060407486114548666127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83179955359703777038210709 3899060407486114548666127)
                      ·
                        rfl

theorem cell23_7593393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_7593393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593393 prefixEnd_7593393 := by exact prefixLift 7593393
  have htrace : WordTrace (prefixWord ++ tailWord_7593393) baseStart_7593393 baseEnd_7593393 := by
    simpa [prefixWord, tailWord_7593393, baseEnd_7593393] using wordTrace_append hprefix tailTrace_7593393
  have hstable : (prefixWord ++ tailWord_7593393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593393).length < 2 ^ (prefixWord ++ tailWord_7593393).sum := by decide
  have hdescent : baseEnd_7593393 < baseStart_7593393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593420 : List Nat := [2, 2, 1, 4, 2, 1, 4, 7]
def baseStart_7593420 : Nat := 118140960795 + 7593420 * 2 ^ 59
def prefixEnd_7593420 : Nat := 4983230072969 + 3 ^ 40 * 7593420 * 2
def baseEnd_7593420 : Nat := 144410158202362442334389

theorem tailTrace_7593420 : CollatzResearch.WordTrace tailWord_7593420 prefixEnd_7593420 144410158202362442334389 := by
  unfold tailWord_7593420
  simp only [CollatzResearch.WordTrace]
  refine ⟨138477390075171833866688857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184636520100229111822251809 138477390075171833866688857)
  ·
    refine ⟨103858042556378875400016643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138477390075171833866688857 103858042556378875400016643)
    ·
      refine ⟨155787063834568313100024965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103858042556378875400016643 155787063834568313100024965)
      ·
        refine ⟨29210074468981558706254681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155787063834568313100024965 29210074468981558706254681)
        ·
          refine ⟨21907555851736169029691011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29210074468981558706254681 21907555851736169029691011)
          ·
            refine ⟨32861333777604253544536517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21907555851736169029691011 32861333777604253544536517)
            ·
              refine ⟨6161500083300797539600597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32861333777604253544536517 6161500083300797539600597)
              ·
                refine ⟨144410158202362442334389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6161500083300797539600597 144410158202362442334389)
                ·
                  rfl

theorem cell23_7593420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 7].length) (baseStart_7593420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593420 prefixEnd_7593420 := by exact prefixLift 7593420
  have htrace : WordTrace (prefixWord ++ tailWord_7593420) baseStart_7593420 baseEnd_7593420 := by
    simpa [prefixWord, tailWord_7593420, baseEnd_7593420] using wordTrace_append hprefix tailTrace_7593420
  have hstable : (prefixWord ++ tailWord_7593420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593420).length < 2 ^ (prefixWord ++ tailWord_7593420).sum := by decide
  have hdescent : baseEnd_7593420 < baseStart_7593420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593447 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_7593447 : Nat := 118140960795 + 7593447 * 2 ^ 59
def prefixEnd_7593447 : Nat := 4983230072969 + 3 ^ 40 * 7593447 * 2
def baseEnd_7593447 : Nat := 3899088135441457337390879

theorem tailTrace_7593447 : CollatzResearch.WordTrace tailWord_7593447 prefixEnd_7593447 3899088135441457337390879 := by
  unfold tailWord_7593447
  simp only [CollatzResearch.WordTrace]
  refine ⟨276955764921245851344610595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184637176614163900896407063 276955764921245851344610595)
  ·
    refine ⟨415433647381868777016915893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276955764921245851344610595 415433647381868777016915893)
    ·
      refine ⟨38946904442050197845335865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 415433647381868777016915893 38946904442050197845335865)
      ·
        refine ⟨29210178331537648384001899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38946904442050197845335865 29210178331537648384001899)
        ·
          refine ⟨43815267497306472576002849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29210178331537648384001899 43815267497306472576002849)
          ·
            refine ⟨32861450622979854432002137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43815267497306472576002849 32861450622979854432002137)
            ·
              refine ⟨24646087967234890824001603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32861450622979854432002137 24646087967234890824001603)
              ·
                refine ⟨36969131950852336236002405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24646087967234890824001603 36969131950852336236002405)
                ·
                  refine ⟨6931712240784813044250451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36969131950852336236002405 6931712240784813044250451)
                  ·
                    refine ⟨10397568361177219566375677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6931712240784813044250451 10397568361177219566375677)
                    ·
                      refine ⟨3899088135441457337390879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10397568361177219566375677 3899088135441457337390879)
                      ·
                        rfl

theorem cell23_7593447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_7593447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593447 prefixEnd_7593447 := by exact prefixLift 7593447
  have htrace : WordTrace (prefixWord ++ tailWord_7593447) baseStart_7593447 baseEnd_7593447 := by
    simpa [prefixWord, tailWord_7593447, baseEnd_7593447] using wordTrace_append hprefix tailTrace_7593447
  have hstable : (prefixWord ++ tailWord_7593447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593447).length < 2 ^ (prefixWord ++ tailWord_7593447).sum := by decide
  have hdescent : baseEnd_7593447 < baseStart_7593447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593464 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 2, 1, 3]
def baseStart_7593464 : Nat := 118140960795 + 7593464 * 2 ^ 59
def prefixEnd_7593464 : Nat := 4983230072969 + 3 ^ 40 * 7593464 * 2
def baseEnd_7593464 : Nat := 3899096864612583770878301

theorem tailTrace_7593464 : CollatzResearch.WordTrace tailWord_7593464 prefixEnd_7593464 3899096864612583770878301 := by
  unfold tailWord_7593464
  simp only [CollatzResearch.WordTrace]
  refine ⟨138478192481092131623989723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184637589974789508831986297 138478192481092131623989723)
  ·
    refine ⟨207717288721638197435984585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138478192481092131623989723 207717288721638197435984585)
    ·
      refine ⟨155787966541228648076988439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207717288721638197435984585 155787966541228648076988439)
      ·
        refine ⟨233681949811842972115482659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155787966541228648076988439 233681949811842972115482659)
        ·
          refine ⟨350522924717764458173223989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233681949811842972115482659 350522924717764458173223989)
          ·
            refine ⟨32861524192290417953739749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 350522924717764458173223989 32861524192290417953739749)
            ·
              refine ⟨6161535786054453366326203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32861524192290417953739749 6161535786054453366326203)
              ·
                refine ⟨9242303679081680049489305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6161535786054453366326203 9242303679081680049489305)
                ·
                  refine ⟨6931727759311260037116979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9242303679081680049489305 6931727759311260037116979)
                  ·
                    refine ⟨10397591638966890055675469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6931727759311260037116979 10397591638966890055675469)
                    ·
                      refine ⟨3899096864612583770878301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10397591638966890055675469 3899096864612583770878301)
                      ·
                        rfl

theorem cell23_7593464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 2, 1, 3].length) (baseStart_7593464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593464 prefixEnd_7593464 := by exact prefixLift 7593464
  have htrace : WordTrace (prefixWord ++ tailWord_7593464) baseStart_7593464 baseEnd_7593464 := by
    simpa [prefixWord, tailWord_7593464, baseEnd_7593464] using wordTrace_append hprefix tailTrace_7593464
  have hstable : (prefixWord ++ tailWord_7593464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593464).length < 2 ^ (prefixWord ++ tailWord_7593464).sum := by decide
  have hdescent : baseEnd_7593464 < baseStart_7593464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593500 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_7593500 : Nat := 118140960795 + 7593500 * 2 ^ 59
def prefixEnd_7593500 : Nat := 4983230072969 + 3 ^ 40 * 7593500 * 2
def baseEnd_7593500 : Nat := 3899115349916145630028135

theorem tailTrace_7593500 : CollatzResearch.WordTrace tailWord_7593500 prefixEnd_7593500 3899115349916145630028135 := by
  unfold tailWord_7593500
  simp only [CollatzResearch.WordTrace]
  refine ⟨138478848995026920698144977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184638465326702560930859969 138478848995026920698144977)
  ·
    refine ⟨103859136746270190523608733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138478848995026920698144977 103859136746270190523608733)
    ·
      refine ⟨38947176279851321446353275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103859136746270190523608733 38947176279851321446353275)
      ·
        refine ⟨58420764419776982169529913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38947176279851321446353275 58420764419776982169529913)
        ·
          refine ⟨43815573314832736627147435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58420764419776982169529913 43815573314832736627147435)
          ·
            refine ⟨65723359972249104940721153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43815573314832736627147435 65723359972249104940721153)
            ·
              refine ⟨49292519979186828705540865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65723359972249104940721153 49292519979186828705540865)
              ·
                refine ⟨36969389984390121529155649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49292519979186828705540865 36969389984390121529155649)
                ·
                  refine ⟨27727042488292591146866737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36969389984390121529155649 27727042488292591146866737)
                  ·
                    refine ⟨20795281866219443360150053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27727042488292591146866737 20795281866219443360150053)
                    ·
                      refine ⟨3899115349916145630028135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20795281866219443360150053 3899115349916145630028135)
                      ·
                        rfl

theorem cell23_7593500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_7593500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593500 prefixEnd_7593500 := by exact prefixLift 7593500
  have htrace : WordTrace (prefixWord ++ tailWord_7593500) baseStart_7593500 baseEnd_7593500 := by
    simpa [prefixWord, tailWord_7593500, baseEnd_7593500] using wordTrace_append hprefix tailTrace_7593500
  have hstable : (prefixWord ++ tailWord_7593500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593500).length < 2 ^ (prefixWord ++ tailWord_7593500).sum := by decide
  have hdescent : baseEnd_7593500 < baseStart_7593500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593503 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_7593503 : Nat := 118140960795 + 7593503 * 2 ^ 59
def prefixEnd_7593503 : Nat := 4983230072969 + 3 ^ 40 * 7593503 * 2
def baseEnd_7593503 : Nat := 3899116890358109118290621

theorem tailTrace_7593503 : CollatzResearch.WordTrace tailWord_7593503 prefixEnd_7593503 3899116890358109118290621 := by
  unfold tailWord_7593503
  simp only [CollatzResearch.WordTrace]
  refine ⟨276957807409042972908649163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184638538272695315272432775 276957807409042972908649163)
  ·
    refine ⟨415436711113564459362973745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276957807409042972908649163 415436711113564459362973745)
    ·
      refine ⟨311577533335173344522230309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415436711113564459362973745 311577533335173344522230309)
      ·
        refine ⟨58420787500345002097918183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311577533335173344522230309 58420787500345002097918183)
        ·
          refine ⟨87631181250517503146877275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58420787500345002097918183 87631181250517503146877275)
          ·
            refine ⟨131446771875776254720315913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87631181250517503146877275 131446771875776254720315913)
            ·
              refine ⟨98585078906832191040236935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131446771875776254720315913 98585078906832191040236935)
              ·
                refine ⟨147877618360248286560355403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98585078906832191040236935 147877618360248286560355403)
                ·
                  refine ⟨221816427540372429840533105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147877618360248286560355403 221816427540372429840533105)
                  ·
                    refine ⟨166362320655279322380399829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221816427540372429840533105 166362320655279322380399829)
                    ·
                      refine ⟨3899116890358109118290621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166362320655279322380399829 3899116890358109118290621)
                      ·
                        rfl

theorem cell23_7593503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_7593503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593503 prefixEnd_7593503 := by exact prefixLift 7593503
  have htrace : WordTrace (prefixWord ++ tailWord_7593503) baseStart_7593503 baseEnd_7593503 := by
    simpa [prefixWord, tailWord_7593503, baseEnd_7593503] using wordTrace_append hprefix tailTrace_7593503
  have hstable : (prefixWord ++ tailWord_7593503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593503).length < 2 ^ (prefixWord ++ tailWord_7593503).sum := by decide
  have hdescent : baseEnd_7593503 < baseStart_7593503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593542 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_7593542 : Nat := 118140960795 + 7593542 * 2 ^ 59
def prefixEnd_7593542 : Nat := 4983230072969 + 3 ^ 40 * 7593542 * 2
def baseEnd_7593542 : Nat := 3899136916103634465702943

theorem tailTrace_7593542 : CollatzResearch.WordTrace tailWord_7593542 prefixEnd_7593542 3899136916103634465702943 := by
  unfold tailWord_7593542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654975932996927580291215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184639486570601121712879253 8654975932996927580291215)
  ·
    refine ⟨12982463899495391370436823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8654975932996927580291215 12982463899495391370436823)
    ·
      refine ⟨19473695849243087055655235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12982463899495391370436823 19473695849243087055655235)
      ·
        refine ⟨29210543773864630583482853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19473695849243087055655235 29210543773864630583482853)
        ·
          refine ⟨5476976957599618234403035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29210543773864630583482853 5476976957599618234403035)
          ·
            refine ⟨8215465436399427351604553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5476976957599618234403035 8215465436399427351604553)
            ·
              refine ⟨6161599077299570513703415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8215465436399427351604553 6161599077299570513703415)
              ·
                refine ⟨9242398615949355770555123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6161599077299570513703415 9242398615949355770555123)
                ·
                  refine ⟨13863597923924033655832685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9242398615949355770555123 13863597923924033655832685)
                  ·
                    refine ⟨5198849221471512620937257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13863597923924033655832685 5198849221471512620937257)
                    ·
                      refine ⟨3899136916103634465702943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198849221471512620937257 3899136916103634465702943)
                      ·
                        rfl

theorem cell23_7593542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_7593542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593542 prefixEnd_7593542 := by exact prefixLift 7593542
  have htrace : WordTrace (prefixWord ++ tailWord_7593542) baseStart_7593542 baseEnd_7593542 := by
    simpa [prefixWord, tailWord_7593542, baseEnd_7593542] using wordTrace_append hprefix tailTrace_7593542
  have hstable : (prefixWord ++ tailWord_7593542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593542).length < 2 ^ (prefixWord ++ tailWord_7593542).sum := by decide
  have hdescent : baseEnd_7593542 < baseStart_7593542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593560 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_7593560 : Nat := 118140960795 + 7593560 * 2 ^ 59
def prefixEnd_7593560 : Nat := 4983230072969 + 3 ^ 40 * 7593560 * 2
def baseEnd_7593560 : Nat := 3899146158755415395277859

theorem tailTrace_7593560 : CollatzResearch.WordTrace tailWord_7593560 prefixEnd_7593560 3899146158755415395277859 := by
  unfold tailWord_7593560
  simp only [CollatzResearch.WordTrace]
  refine ⟨138479943184918235821737067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184639924246557647762316089 138479943184918235821737067)
  ·
    refine ⟨207719914777377353732605601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138479943184918235821737067 207719914777377353732605601)
    ·
      refine ⟨155789936083033015299454201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207719914777377353732605601 155789936083033015299454201)
      ·
        refine ⟨116842452062274761474590651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155789936083033015299454201 116842452062274761474590651)
        ·
          refine ⟨175263678093412142211885977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116842452062274761474590651 175263678093412142211885977)
          ·
            refine ⟨131447758570059106658914483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175263678093412142211885977 131447758570059106658914483)
            ·
              refine ⟨197171637855088659988371725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131447758570059106658914483 197171637855088659988371725)
              ·
                refine ⟨73939364195658247495639397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197171637855088659988371725 73939364195658247495639397)
                ·
                  refine ⟨13863630786685921405432387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73939364195658247495639397 13863630786685921405432387)
                  ·
                    refine ⟨20795446180028882108148581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13863630786685921405432387 20795446180028882108148581)
                    ·
                      refine ⟨3899146158755415395277859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20795446180028882108148581 3899146158755415395277859)
                      ·
                        rfl

theorem cell23_7593560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_7593560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593560 prefixEnd_7593560 := by exact prefixLift 7593560
  have htrace : WordTrace (prefixWord ++ tailWord_7593560) baseStart_7593560 baseEnd_7593560 := by
    simpa [prefixWord, tailWord_7593560, baseEnd_7593560] using wordTrace_append hprefix tailTrace_7593560
  have hstable : (prefixWord ++ tailWord_7593560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593560).length < 2 ^ (prefixWord ++ tailWord_7593560).sum := by decide
  have hdescent : baseEnd_7593560 < baseStart_7593560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593577 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 2, 4, 2]
def baseStart_7593577 : Nat := 118140960795 + 7593577 * 2 ^ 59
def prefixEnd_7593577 : Nat := 4983230072969 + 3 ^ 40 * 7593577 * 2
def baseEnd_7593577 : Nat := 3899154887926541828765281

theorem tailTrace_7593577 : CollatzResearch.WordTrace tailWord_7593577 prefixEnd_7593577 3899154887926541828765281 := by
  unfold tailWord_7593577
  simp only [CollatzResearch.WordTrace]
  refine ⟨276960506410774883546842985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184640337607183255697895323 276960506410774883546842985)
  ·
    refine ⟨207720379808081162660132239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276960506410774883546842985 207720379808081162660132239)
    ·
      refine ⟨311580569712121743990198359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207720379808081162660132239 311580569712121743990198359)
      ·
        refine ⟨467370854568182615985297539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311580569712121743990198359 467370854568182615985297539)
        ·
          refine ⟨701056281852273923977946309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467370854568182615985297539 701056281852273923977946309)
          ·
            refine ⟨131448052847301360745864933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 701056281852273923977946309 131448052847301360745864933)
            ·
              refine ⟨24646509908869005139849675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131448052847301360745864933 24646509908869005139849675)
              ·
                refine ⟨36969764863303507709774513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24646509908869005139849675 36969764863303507709774513)
                ·
                  refine ⟨27727323647477630782330885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36969764863303507709774513 27727323647477630782330885)
                  ·
                    refine ⟨5198873183902055771687041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27727323647477630782330885 5198873183902055771687041)
                    ·
                      refine ⟨3899154887926541828765281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198873183902055771687041 3899154887926541828765281)
                      ·
                        rfl

theorem cell23_7593577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 4, 2].length) (baseStart_7593577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593577 prefixEnd_7593577 := by exact prefixLift 7593577
  have htrace : WordTrace (prefixWord ++ tailWord_7593577) baseStart_7593577 baseEnd_7593577 := by
    simpa [prefixWord, tailWord_7593577, baseEnd_7593577] using wordTrace_append hprefix tailTrace_7593577
  have hstable : (prefixWord ++ tailWord_7593577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593577).length < 2 ^ (prefixWord ++ tailWord_7593577).sum := by decide
  have hdescent : baseEnd_7593577 < baseStart_7593577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593597 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_7593597 : Nat := 118140960795 + 7593597 * 2 ^ 59
def prefixEnd_7593597 : Nat := 4983230072969 + 3 ^ 40 * 7593597 * 2
def baseEnd_7593597 : Nat := 3899165157539631750515189

theorem tailTrace_7593597 : CollatzResearch.WordTrace tailWord_7593597 prefixEnd_7593597 3899165157539631750515189 := by
  unfold tailWord_7593597
  simp only [CollatzResearch.WordTrace]
  refine ⟨276961235870702426962571045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184640823913801617975047363 276961235870702426962571045)
  ·
    refine ⟨51930231725756705055482071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276961235870702426962571045 51930231725756705055482071)
    ·
      refine ⟨77895347588635057583223107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51930231725756705055482071 77895347588635057583223107)
      ·
        refine ⟨116843021382952586374834661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77895347588635057583223107 116843021382952586374834661)
        ·
          refine ⟨21908066509303609945281499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116843021382952586374834661 21908066509303609945281499)
          ·
            refine ⟨32862099763955414917922249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21908066509303609945281499 32862099763955414917922249)
            ·
              refine ⟨24646574822966561188441687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32862099763955414917922249 24646574822966561188441687)
              ·
                refine ⟨36969862234449841782662531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24646574822966561188441687 36969862234449841782662531)
                ·
                  refine ⟨55454793351674762673993797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36969862234449841782662531 55454793351674762673993797)
                  ·
                    refine ⟨10397773753439018001373837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55454793351674762673993797 10397773753439018001373837)
                    ·
                      refine ⟨3899165157539631750515189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10397773753439018001373837 3899165157539631750515189)
                      ·
                        rfl

theorem cell23_7593597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_7593597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593597 prefixEnd_7593597 := by exact prefixLift 7593597
  have htrace : WordTrace (prefixWord ++ tailWord_7593597) baseStart_7593597 baseEnd_7593597 := by
    simpa [prefixWord, tailWord_7593597, baseEnd_7593597] using wordTrace_append hprefix tailTrace_7593597
  have hstable : (prefixWord ++ tailWord_7593597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593597).length < 2 ^ (prefixWord ++ tailWord_7593597).sum := by decide
  have hdescent : baseEnd_7593597 < baseStart_7593597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593614 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_7593614 : Nat := 118140960795 + 7593614 * 2 ^ 59
def prefixEnd_7593614 : Nat := 4983230072969 + 3 ^ 40 * 7593614 * 2
def baseEnd_7593614 : Nat := 3899173886710758184002611

theorem tailTrace_7593614 : CollatzResearch.WordTrace tailWord_7593614 prefixEnd_7593614 3899173886710758184002611 := by
  unfold tailWord_7593614
  simp only [CollatzResearch.WordTrace]
  refine ⟨34620231988955104858242487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184641237274427225910626597 34620231988955104858242487)
  ·
    refine ⟨51930347983432657287363731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34620231988955104858242487 51930347983432657287363731)
    ·
      refine ⟨77895521975148985931045597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51930347983432657287363731 77895521975148985931045597)
      ·
        refine ⟨29210820740680869724142099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77895521975148985931045597 29210820740680869724142099)
        ·
          refine ⟨43816231111021304586213149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29210820740680869724142099 43816231111021304586213149)
          ·
            refine ⟨16431086666632989219829931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43816231111021304586213149 16431086666632989219829931)
            ·
              refine ⟨24646629999949483829744897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16431086666632989219829931 24646629999949483829744897)
              ·
                refine ⟨18484972499962112872308673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24646629999949483829744897 18484972499962112872308673)
                ·
                  refine ⟨13863729374971584654231505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18484972499962112872308673 13863729374971584654231505)
                  ·
                    refine ⟨10397797031228688490673629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13863729374971584654231505 10397797031228688490673629)
                    ·
                      refine ⟨3899173886710758184002611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10397797031228688490673629 3899173886710758184002611)
                      ·
                        rfl

theorem cell23_7593614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_7593614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593614 prefixEnd_7593614 := by exact prefixLift 7593614
  have htrace : WordTrace (prefixWord ++ tailWord_7593614) baseStart_7593614 baseEnd_7593614 := by
    simpa [prefixWord, tailWord_7593614, baseEnd_7593614] using wordTrace_append hprefix tailTrace_7593614
  have hstable : (prefixWord ++ tailWord_7593614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593614).length < 2 ^ (prefixWord ++ tailWord_7593614).sum := by decide
  have hdescent : baseEnd_7593614 < baseStart_7593614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593637 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 3, 5, 2]
def baseStart_7593637 : Nat := 118140960795 + 7593637 * 2 ^ 59
def prefixEnd_7593637 : Nat := 4983230072969 + 3 ^ 40 * 7593637 * 2
def baseEnd_7593637 : Nat := 3899185696765811594015005

theorem tailTrace_7593637 : CollatzResearch.WordTrace tailWord_7593637 prefixEnd_7593637 3899185696765811594015005 := by
  unfold tailWord_7593637
  simp only [CollatzResearch.WordTrace]
  refine ⟨276962694790557513794027165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184641796527038342529351443 276962694790557513794027165)
  ·
    refine ⟨103861010546459067672760187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276962694790557513794027165 103861010546459067672760187)
    ·
      refine ⟨155791515819688601509140281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103861010546459067672760187 155791515819688601509140281)
      ·
        refine ⟨116843636864766451131855211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155791515819688601509140281 116843636864766451131855211)
        ·
          refine ⟨175265455297149676697782817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116843636864766451131855211 175265455297149676697782817)
          ·
            refine ⟨131449091472862257523337113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175265455297149676697782817 131449091472862257523337113)
            ·
              refine ⟨98586818604646693142502835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131449091472862257523337113 98586818604646693142502835)
              ·
                refine ⟨147880227906970039713754253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98586818604646693142502835 147880227906970039713754253)
                ·
                  refine ⟨55455085465113764892657845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147880227906970039713754253 55455085465113764892657845)
                  ·
                    refine ⟨5198914262354415458686673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55455085465113764892657845 5198914262354415458686673)
                    ·
                      refine ⟨3899185696765811594015005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198914262354415458686673 3899185696765811594015005)
                      ·
                        rfl

theorem cell23_7593637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_7593637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593637 prefixEnd_7593637 := by exact prefixLift 7593637
  have htrace : WordTrace (prefixWord ++ tailWord_7593637) baseStart_7593637 baseEnd_7593637 := by
    simpa [prefixWord, tailWord_7593637, baseEnd_7593637] using wordTrace_append hprefix tailTrace_7593637
  have hstable : (prefixWord ++ tailWord_7593637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593637).length < 2 ^ (prefixWord ++ tailWord_7593637).sum := by decide
  have hdescent : baseEnd_7593637 < baseStart_7593637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593661 : List Nat := [1, 4, 1, 2, 1, 2, 2, 5, 1, 1, 3]
def baseStart_7593661 : Nat := 118140960795 + 7593661 * 2 ^ 59
def prefixEnd_7593661 : Nat := 4983230072969 + 3 ^ 40 * 7593661 * 2
def baseEnd_7593661 : Nat := 3899198020301519500114895

theorem tailTrace_7593661 : CollatzResearch.WordTrace tailWord_7593661 prefixEnd_7593661 3899198020301519500114895 := by
  unfold tailWord_7593661
  simp only [CollatzResearch.WordTrace]
  refine ⟨276963570142470565892900837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184642380094980377261933891 276963570142470565892900837)
  ·
    refine ⟨51930669401713231104918907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276963570142470565892900837 51930669401713231104918907)
    ·
      refine ⟨77896004102569846657378361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51930669401713231104918907 77896004102569846657378361)
      ·
        refine ⟨58422003076927384993033771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77896004102569846657378361 58422003076927384993033771)
        ·
          refine ⟨87633004615391077489550657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58422003076927384993033771 87633004615391077489550657)
          ·
            refine ⟨65724753461543308117162993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87633004615391077489550657 65724753461543308117162993)
            ·
              refine ⟨49293565096157481087872245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65724753461543308117162993 49293565096157481087872245)
              ·
                refine ⟨4621271727764763851988023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49293565096157481087872245 4621271727764763851988023)
                ·
                  refine ⟨6931907591647145777982035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621271727764763851988023 6931907591647145777982035)
                  ·
                    refine ⟨10397861387470718666973053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6931907591647145777982035 10397861387470718666973053)
                    ·
                      refine ⟨3899198020301519500114895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10397861387470718666973053 3899198020301519500114895)
                      ·
                        rfl

theorem cell23_7593661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_7593661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593661 prefixEnd_7593661 := by exact prefixLift 7593661
  have htrace : WordTrace (prefixWord ++ tailWord_7593661) baseStart_7593661 baseEnd_7593661 := by
    simpa [prefixWord, tailWord_7593661, baseEnd_7593661] using wordTrace_append hprefix tailTrace_7593661
  have hstable : (prefixWord ++ tailWord_7593661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593661).length < 2 ^ (prefixWord ++ tailWord_7593661).sum := by decide
  have hdescent : baseEnd_7593661 < baseStart_7593661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593664 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 1, 5]
def baseStart_7593664 : Nat := 118140960795 + 7593664 * 2 ^ 59
def prefixEnd_7593664 : Nat := 4983230072969 + 3 ^ 40 * 7593664 * 2
def baseEnd_7593664 : Nat := 1299733186914494329459127

theorem tailTrace_7593664 : CollatzResearch.WordTrace tailWord_7593664 prefixEnd_7593664 1299733186914494329459127 := by
  unfold tailWord_7593664
  simp only [CollatzResearch.WordTrace]
  refine ⟨138481839780729848702630023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184642453040973131603506697 138481839780729848702630023)
  ·
    refine ⟨207722759671094773053945035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138481839780729848702630023 207722759671094773053945035)
    ·
      refine ⟨311584139506642159580917553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207722759671094773053945035 311584139506642159580917553)
      ·
        refine ⟨233688104629981619685688165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311584139506642159580917553 233688104629981619685688165)
        ·
          refine ⟨43816519618121553691066531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233688104629981619685688165 43816519618121553691066531)
          ·
            refine ⟨65724779427182330536599797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43816519618121553691066531 65724779427182330536599797)
            ·
              refine ⟨6161698071298343487806231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65724779427182330536599797 6161698071298343487806231)
              ·
                refine ⟨9242547106947515231709347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6161698071298343487806231 9242547106947515231709347)
                ·
                  refine ⟨13863820660421272847564021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9242547106947515231709347 13863820660421272847564021)
                  ·
                    refine ⟨1299733186914494329459127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13863820660421272847564021 1299733186914494329459127)
                    ·
                      rfl

theorem cell23_7593664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 5].length) (baseStart_7593664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593664 prefixEnd_7593664 := by exact prefixLift 7593664
  have htrace : WordTrace (prefixWord ++ tailWord_7593664) baseStart_7593664 baseEnd_7593664 := by
    simpa [prefixWord, tailWord_7593664, baseEnd_7593664] using wordTrace_append hprefix tailTrace_7593664
  have hstable : (prefixWord ++ tailWord_7593664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593664).length < 2 ^ (prefixWord ++ tailWord_7593664).sum := by decide
  have hdescent : baseEnd_7593664 < baseStart_7593664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593680 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 6]
def baseStart_7593680 : Nat := 118140960795 + 7593680 * 2 ^ 59
def prefixEnd_7593680 : Nat := 4983230072969 + 3 ^ 40 * 7593680 * 2
def baseEnd_7593680 : Nat := 3899207776433954925777307

theorem tailTrace_7593680 : CollatzResearch.WordTrace tailWord_7593680 prefixEnd_7593680 3899207776433954925777307 := by
  unfold tailWord_7593680
  simp only [CollatzResearch.WordTrace]
  refine ⟨138482131564700866068921247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184642842086267821425228329 138482131564700866068921247)
  ·
    refine ⟨207723197347051299103381871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138482131564700866068921247 207723197347051299103381871)
    ·
      refine ⟨311584796020576948655072807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207723197347051299103381871 311584796020576948655072807)
      ·
        refine ⟨467377194030865422982609211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311584796020576948655072807 467377194030865422982609211)
        ·
          refine ⟨701065791046298134473913817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467377194030865422982609211 701065791046298134473913817)
          ·
            refine ⟨525799343284723600855435363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701065791046298134473913817 525799343284723600855435363)
            ·
              refine ⟨788699014927085401283153045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525799343284723600855435363 788699014927085401283153045)
              ·
                refine ⟨36970266324707128185147799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 788699014927085401283153045 36970266324707128185147799)
                ·
                  refine ⟨55455399487060692277721699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36970266324707128185147799 55455399487060692277721699)
                  ·
                    refine ⟨83183099230591038416582549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55455399487060692277721699 83183099230591038416582549)
                    ·
                      refine ⟨3899207776433954925777307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83183099230591038416582549 3899207776433954925777307)
                      ·
                        rfl

theorem cell23_7593680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_7593680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593680 prefixEnd_7593680 := by exact prefixLift 7593680
  have htrace : WordTrace (prefixWord ++ tailWord_7593680) baseStart_7593680 baseEnd_7593680 := by
    simpa [prefixWord, tailWord_7593680, baseEnd_7593680] using wordTrace_append hprefix tailTrace_7593680
  have hstable : (prefixWord ++ tailWord_7593680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593680).length < 2 ^ (prefixWord ++ tailWord_7593680).sum := by decide
  have hdescent : baseEnd_7593680 < baseStart_7593680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593684 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7593684 : Nat := 118140960795 + 7593684 * 2 ^ 59
def prefixEnd_7593684 : Nat := 4983230072969 + 3 ^ 40 * 7593684 * 2
def baseEnd_7593684 : Nat := 3899209830356572910127289

theorem tailTrace_7593684 : CollatzResearch.WordTrace tailWord_7593684 prefixEnd_7593684 3899209830356572910127289 := by
  unfold tailWord_7593684
  simp only [CollatzResearch.WordTrace]
  refine ⟨138482204510693620410494053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184642939347591493880658737 138482204510693620410494053)
  ·
    refine ⟨25965413345755053826967635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138482204510693620410494053 25965413345755053826967635)
    ·
      refine ⟨38948120018632580740451453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25965413345755053826967635 38948120018632580740451453)
      ·
        refine ⟨14605545006987217777669295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38948120018632580740451453 14605545006987217777669295)
        ·
          refine ⟨21908317510480826666503943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14605545006987217777669295 21908317510480826666503943)
          ·
            refine ⟨32862476265721239999755915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21908317510480826666503943 32862476265721239999755915)
            ·
              refine ⟨49293714398581859999633873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32862476265721239999755915 49293714398581859999633873)
              ·
                refine ⟨36970285798936394999725405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49293714398581859999633873 36970285798936394999725405)
                ·
                  refine ⟨13863857174601148124897027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36970285798936394999725405 13863857174601148124897027)
                  ·
                    refine ⟨20795785761901722187345541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13863857174601148124897027 20795785761901722187345541)
                    ·
                      refine ⟨3899209830356572910127289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20795785761901722187345541 3899209830356572910127289)
                      ·
                        rfl

theorem cell23_7593684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7593684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593684 prefixEnd_7593684 := by exact prefixLift 7593684
  have htrace : WordTrace (prefixWord ++ tailWord_7593684) baseStart_7593684 baseEnd_7593684 := by
    simpa [prefixWord, tailWord_7593684, baseEnd_7593684] using wordTrace_append hprefix tailTrace_7593684
  have hstable : (prefixWord ++ tailWord_7593684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593684).length < 2 ^ (prefixWord ++ tailWord_7593684).sum := by decide
  have hdescent : baseEnd_7593684 < baseStart_7593684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593687 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 3]
def baseStart_7593687 : Nat := 118140960795 + 7593687 * 2 ^ 59
def prefixEnd_7593687 : Nat := 4983230072969 + 3 ^ 40 * 7593687 * 2
def baseEnd_7593687 : Nat := 3899211370798536398389775

theorem tailTrace_7593687 : CollatzResearch.WordTrace tailWord_7593687 prefixEnd_7593687 3899211370798536398389775 := by
  unfold tailWord_7593687
  simp only [CollatzResearch.WordTrace]
  refine ⟨276964518440376372333347315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184643012293584248222231543 276964518440376372333347315)
  ·
    refine ⟨415446777660564558500020973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276964518440376372333347315 415446777660564558500020973)
    ·
      refine ⟨155792541622711709437507865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415446777660564558500020973 155792541622711709437507865)
      ·
        refine ⟨116844406217033782078130899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155792541622711709437507865 116844406217033782078130899)
        ·
          refine ⟨175266609325550673117196349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116844406217033782078130899 175266609325550673117196349)
          ·
            refine ⟨65724978497081502418948631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175266609325550673117196349 65724978497081502418948631)
            ·
              refine ⟨98587467745622253628422947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65724978497081502418948631 98587467745622253628422947)
              ·
                refine ⟨147881201618433380442634421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98587467745622253628422947 147881201618433380442634421)
                ·
                  refine ⟨13863862651728129416496977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147881201618433380442634421 13863862651728129416496977)
                  ·
                    refine ⟨10397896988796097062372733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13863862651728129416496977 10397896988796097062372733)
                    ·
                      refine ⟨3899211370798536398389775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10397896988796097062372733 3899211370798536398389775)
                      ·
                        rfl

theorem cell23_7593687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_7593687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593687 prefixEnd_7593687 := by exact prefixLift 7593687
  have htrace : WordTrace (prefixWord ++ tailWord_7593687) baseStart_7593687 baseEnd_7593687 := by
    simpa [prefixWord, tailWord_7593687, baseEnd_7593687] using wordTrace_append hprefix tailTrace_7593687
  have hstable : (prefixWord ++ tailWord_7593687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593687).length < 2 ^ (prefixWord ++ tailWord_7593687).sum := by decide
  have hdescent : baseEnd_7593687 < baseStart_7593687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593701 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 3, 2, 2]
def baseStart_7593701 : Nat := 118140960795 + 7593701 * 2 ^ 59
def prefixEnd_7593701 : Nat := 4983230072969 + 3 ^ 40 * 7593701 * 2
def baseEnd_7593701 : Nat := 3899218559527699343614711

theorem tailTrace_7593701 : CollatzResearch.WordTrace tailWord_7593701 prefixEnd_7593701 3899218559527699343614711 := by
  unfold tailWord_7593701
  simp only [CollatzResearch.WordTrace]
  refine ⟨276965029062325652724356957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184643352708217101816237971 276965029062325652724356957)
  ·
    refine ⟨103861885898372119771633859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276965029062325652724356957 103861885898372119771633859)
    ·
      refine ⟨155792828847558179657450789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103861885898372119771633859 155792828847558179657450789)
      ·
        refine ⟨29211155408917158685772023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155792828847558179657450789 29211155408917158685772023)
        ·
          refine ⟨43816733113375738028658035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29211155408917158685772023 43816733113375738028658035)
          ·
            refine ⟨65725099670063607042987053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43816733113375738028658035 65725099670063607042987053)
            ·
              refine ⟨24646912376273852641120145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65725099670063607042987053 24646912376273852641120145)
              ·
                refine ⟨18485184282205389480840109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24646912376273852641120145 18485184282205389480840109)
                ·
                  refine ⟨6931944105827021055315041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18485184282205389480840109 6931944105827021055315041)
                  ·
                    refine ⟨5198958079370265791486281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6931944105827021055315041 5198958079370265791486281)
                    ·
                      refine ⟨3899218559527699343614711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198958079370265791486281 3899218559527699343614711)
                      ·
                        rfl

theorem cell23_7593701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_7593701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593701 prefixEnd_7593701 := by exact prefixLift 7593701
  have htrace : WordTrace (prefixWord ++ tailWord_7593701) baseStart_7593701 baseEnd_7593701 := by
    simpa [prefixWord, tailWord_7593701, baseEnd_7593701] using wordTrace_append hprefix tailTrace_7593701
  have hstable : (prefixWord ++ tailWord_7593701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593701).length < 2 ^ (prefixWord ++ tailWord_7593701).sum := by decide
  have hdescent : baseEnd_7593701 < baseStart_7593701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593704 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_7593704 : Nat := 118140960795 + 7593704 * 2 ^ 59
def prefixEnd_7593704 : Nat := 4983230072969 + 3 ^ 40 * 7593704 * 2
def baseEnd_7593704 : Nat := 3899220099969662831877197

theorem tailTrace_7593704 : CollatzResearch.WordTrace tailWord_7593704 prefixEnd_7593704 3899220099969662831877197 := by
  unfold tailWord_7593704
  simp only [CollatzResearch.WordTrace]
  refine ⟨138482569240657392118358083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184643425654209856157810777 138482569240657392118358083)
  ·
    refine ⟨207723853860986088177537125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138482569240657392118358083 207723853860986088177537125)
    ·
      refine ⟨38948222598934891533288211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207723853860986088177537125 38948222598934891533288211)
      ·
        refine ⟨58422333898402337299932317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38948222598934891533288211 58422333898402337299932317)
        ·
          refine ⟨21908375211900876487474619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58422333898402337299932317 21908375211900876487474619)
          ·
            refine ⟨32862562817851314731211929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21908375211900876487474619 32862562817851314731211929)
            ·
              refine ⟨24646922113388486048408947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32862562817851314731211929 24646922113388486048408947)
              ·
                refine ⟨36970383170082729072613421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24646922113388486048408947 36970383170082729072613421)
                ·
                  refine ⟨13863893688781023402230033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36970383170082729072613421 13863893688781023402230033)
                  ·
                    refine ⟨10397920266585767551672525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13863893688781023402230033 10397920266585767551672525)
                    ·
                      refine ⟨3899220099969662831877197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10397920266585767551672525 3899220099969662831877197)
                      ·
                        rfl

theorem cell23_7593704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_7593704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593704 prefixEnd_7593704 := by exact prefixLift 7593704
  have htrace : WordTrace (prefixWord ++ tailWord_7593704) baseStart_7593704 baseEnd_7593704 := by
    simpa [prefixWord, tailWord_7593704, baseEnd_7593704] using wordTrace_append hprefix tailTrace_7593704
  have hstable : (prefixWord ++ tailWord_7593704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593704).length < 2 ^ (prefixWord ++ tailWord_7593704).sum := by decide
  have hdescent : baseEnd_7593704 < baseStart_7593704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593718 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_7593718 : Nat := 118140960795 + 7593718 * 2 ^ 59
def prefixEnd_7593718 : Nat := 4983230072969 + 3 ^ 40 * 7593718 * 2
def baseEnd_7593718 : Nat := 3899227288698825777102133

theorem tailTrace_7593718 : CollatzResearch.WordTrace tailWord_7593718 prefixEnd_7593718 3899227288698825777102133 := by
  unfold tailWord_7593718
  simp only [CollatzResearch.WordTrace]
  refine ⟨17310353068954004039232863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184643766068842709751817205 17310353068954004039232863)
  ·
    refine ⟨25965529603431006058849295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17310353068954004039232863 25965529603431006058849295)
    ·
      refine ⟨38948294405146509088273943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25965529603431006058849295 38948294405146509088273943)
      ·
        refine ⟨58422441607719763632410915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38948294405146509088273943 58422441607719763632410915)
        ·
          refine ⟨87633662411579645448616373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58422441607719763632410915 87633662411579645448616373)
          ·
            refine ⟨8215655851085591760807785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87633662411579645448616373 8215655851085591760807785)
            ·
              refine ⟨6161741888314193820605839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8215655851085591760807785 6161741888314193820605839)
              ·
                refine ⟨9242612832471290730908759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6161741888314193820605839 9242612832471290730908759)
                ·
                  refine ⟨13863919248706936096363139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9242612832471290730908759 13863919248706936096363139)
                  ·
                    refine ⟨20795878873060404144544709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13863919248706936096363139 20795878873060404144544709)
                    ·
                      refine ⟨3899227288698825777102133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20795878873060404144544709 3899227288698825777102133)
                      ·
                        rfl

theorem cell23_7593718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_7593718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593718 prefixEnd_7593718 := by exact prefixLift 7593718
  have htrace : WordTrace (prefixWord ++ tailWord_7593718) baseStart_7593718 baseEnd_7593718 := by
    simpa [prefixWord, tailWord_7593718, baseEnd_7593718] using wordTrace_append hprefix tailTrace_7593718
  have hstable : (prefixWord ++ tailWord_7593718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593718).length < 2 ^ (prefixWord ++ tailWord_7593718).sum := by decide
  have hdescent : baseEnd_7593718 < baseStart_7593718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593720 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 1, 9]
def baseStart_7593720 : Nat := 118140960795 + 7593720 * 2 ^ 59
def prefixEnd_7593720 : Nat := 4983230072969 + 3 ^ 40 * 7593720 * 2
def baseEnd_7593720 : Nat := 1299742771886711589759041

theorem tailTrace_7593720 : CollatzResearch.WordTrace tailWord_7593720 prefixEnd_7593720 1299742771886711589759041 := by
  unfold tailWord_7593720
  simp only [CollatzResearch.WordTrace]
  refine ⟨138482861024628409484649307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184643814699504545979532409 138482861024628409484649307)
  ·
    refine ⟨207724291536942614226973961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138482861024628409484649307 207724291536942614226973961)
    ·
      refine ⟨155793218652706960670230471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207724291536942614226973961 155793218652706960670230471)
      ·
        refine ⟨233689827979060441005345707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155793218652706960670230471 233689827979060441005345707)
        ·
          refine ⟨350534741968590661508018561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233689827979060441005345707 350534741968590661508018561)
          ·
            refine ⟨262901056476442996131013921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350534741968590661508018561 262901056476442996131013921)
            ·
              refine ⟨197175792357332247098260441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262901056476442996131013921 197175792357332247098260441)
              ·
                refine ⟨147881844267999185323695331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197175792357332247098260441 147881844267999185323695331)
                ·
                  refine ⟨221822766401998777985542997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147881844267999185323695331 221822766401998777985542997)
                  ·
                    refine ⟨1299742771886711589759041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 221822766401998777985542997 1299742771886711589759041)
                    ·
                      rfl

theorem cell23_7593720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_7593720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593720 prefixEnd_7593720 := by exact prefixLift 7593720
  have htrace : WordTrace (prefixWord ++ tailWord_7593720) baseStart_7593720 baseEnd_7593720 := by
    simpa [prefixWord, tailWord_7593720, baseEnd_7593720] using wordTrace_append hprefix tailTrace_7593720
  have hstable : (prefixWord ++ tailWord_7593720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593720).length < 2 ^ (prefixWord ++ tailWord_7593720).sum := by decide
  have hdescent : baseEnd_7593720 < baseStart_7593720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593748 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7593748 : Nat := 118140960795 + 7593748 * 2 ^ 59
def prefixEnd_7593748 : Nat := 4983230072969 + 3 ^ 40 * 7593748 * 2
def baseEnd_7593748 : Nat := 3899242693118460659726995

theorem tailTrace_7593748 : CollatzResearch.WordTrace tailWord_7593748 prefixEnd_7593748 3899242693118460659726995 := by
  unfold tailWord_7593748
  simp only [CollatzResearch.WordTrace]
  refine ⟨138483371646577689875658949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184644495528770253167545265 138483371646577689875658949)
  ·
    refine ⟨25965632183733316851686053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138483371646577689875658949 25965632183733316851686053)
    ·
      refine ⟨4868556034449996909691135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25965632183733316851686053 4868556034449996909691135)
      ·
        refine ⟨7302834051674995364536703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4868556034449996909691135 7302834051674995364536703)
        ·
          refine ⟨10954251077512493046805055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7302834051674995364536703 10954251077512493046805055)
          ·
            refine ⟨16431376616268739570207583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10954251077512493046805055 16431376616268739570207583)
            ·
              refine ⟨24647064924403109355311375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16431376616268739570207583 24647064924403109355311375)
              ·
                refine ⟨36970597386604664032967063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24647064924403109355311375 36970597386604664032967063)
                ·
                  refine ⟨55455896079906996049450595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36970597386604664032967063 55455896079906996049450595)
                  ·
                    refine ⟨83183844119860494074175893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55455896079906996049450595 83183844119860494074175893)
                    ·
                      refine ⟨3899242693118460659726995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83183844119860494074175893 3899242693118460659726995)
                      ·
                        rfl

theorem cell23_7593748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7593748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593748 prefixEnd_7593748 := by exact prefixLift 7593748
  have htrace : WordTrace (prefixWord ++ tailWord_7593748) baseStart_7593748 baseEnd_7593748 := by
    simpa [prefixWord, tailWord_7593748, baseEnd_7593748] using wordTrace_append hprefix tailTrace_7593748
  have hstable : (prefixWord ++ tailWord_7593748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593748).length < 2 ^ (prefixWord ++ tailWord_7593748).sum := by decide
  have hdescent : baseEnd_7593748 < baseStart_7593748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593751 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 1, 3, 3]
def baseStart_7593751 : Nat := 118140960795 + 7593751 * 2 ^ 59
def prefixEnd_7593751 : Nat := 4983230072969 + 3 ^ 40 * 7593751 * 2
def baseEnd_7593751 : Nat := 3899244233560424147989481

theorem tailTrace_7593751 : CollatzResearch.WordTrace tailWord_7593751 prefixEnd_7593751 3899244233560424147989481 := by
  unfold tailWord_7593751
  simp only [CollatzResearch.WordTrace]
  refine ⟨276966852712144511263677107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184644568474763007509118071 276966852712144511263677107)
  ·
    refine ⟨415450279068216766895515661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276966852712144511263677107 415450279068216766895515661)
    ·
      refine ⟨155793854650581287585818373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415450279068216766895515661 155793854650581287585818373)
      ·
        refine ⟨29211347746983991422340945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155793854650581287585818373 29211347746983991422340945)
        ·
          refine ⟨21908510810237993566755709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29211347746983991422340945 21908510810237993566755709)
          ·
            refine ⟨8215691553839247587533391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21908510810237993566755709 8215691553839247587533391)
            ·
              refine ⟨12323537330758871381300087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8215691553839247587533391 12323537330758871381300087)
              ·
                refine ⟨18485305996138307071950131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12323537330758871381300087 18485305996138307071950131)
                ·
                  refine ⟨27727958994207460607925197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18485305996138307071950131 27727958994207460607925197)
                  ·
                    refine ⟨10397984622827797727971949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27727958994207460607925197 10397984622827797727971949)
                    ·
                      refine ⟨3899244233560424147989481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10397984622827797727971949 3899244233560424147989481)
                      ·
                        rfl

theorem cell23_7593751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_7593751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593751 prefixEnd_7593751 := by exact prefixLift 7593751
  have htrace : WordTrace (prefixWord ++ tailWord_7593751) baseStart_7593751 baseEnd_7593751 := by
    simpa [prefixWord, tailWord_7593751, baseEnd_7593751] using wordTrace_append hprefix tailTrace_7593751
  have hstable : (prefixWord ++ tailWord_7593751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593751).length < 2 ^ (prefixWord ++ tailWord_7593751).sum := by decide
  have hdescent : baseEnd_7593751 < baseStart_7593751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593761 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 1, 3, 2]
def baseStart_7593761 : Nat := 118140960795 + 7593761 * 2 ^ 59
def prefixEnd_7593761 : Nat := 4983230072969 + 3 ^ 40 * 7593761 * 2
def baseEnd_7593761 : Nat := 3899249368366969108864435

theorem tailTrace_7593761 : CollatzResearch.WordTrace tailWord_7593761 prefixEnd_7593761 3899249368366969108864435 := by
  unfold tailWord_7593761
  simp only [CollatzResearch.WordTrace]
  refine ⟨276967217442108282971541137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184644811628072188647694091 276967217442108282971541137)
  ·
    refine ⟨207725413081581212228655853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276967217442108282971541137 207725413081581212228655853)
    ·
      refine ⟨77897029905592954585745945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207725413081581212228655853 77897029905592954585745945)
      ·
        refine ⟨58422772429194715939309459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77897029905592954585745945 58422772429194715939309459)
        ·
          refine ⟨87634158643792073908964189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58422772429194715939309459 87634158643792073908964189)
          ·
            refine ⟨32862809491422027715861571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87634158643792073908964189 32862809491422027715861571)
            ·
              refine ⟨49294214237133041573792357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32862809491422027715861571 49294214237133041573792357)
              ·
                refine ⟨9242665169462445295086067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49294214237133041573792357 9242665169462445295086067)
                ·
                  refine ⟨13863997754193667942629101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9242665169462445295086067 13863997754193667942629101)
                  ·
                    refine ⟨5198999157822625478485913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13863997754193667942629101 5198999157822625478485913)
                    ·
                      refine ⟨3899249368366969108864435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5198999157822625478485913 3899249368366969108864435)
                      ·
                        rfl

theorem cell23_7593761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_7593761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593761 prefixEnd_7593761 := by exact prefixLift 7593761
  have htrace : WordTrace (prefixWord ++ tailWord_7593761) baseStart_7593761 baseEnd_7593761 := by
    simpa [prefixWord, tailWord_7593761, baseEnd_7593761] using wordTrace_append hprefix tailTrace_7593761
  have hstable : (prefixWord ++ tailWord_7593761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593761).length < 2 ^ (prefixWord ++ tailWord_7593761).sum := by decide
  have hdescent : baseEnd_7593761 < baseStart_7593761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593777 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_7593777 : Nat := 118140960795 + 7593777 * 2 ^ 59
def prefixEnd_7593777 : Nat := 4983230072969 + 3 ^ 40 * 7593777 * 2
def baseEnd_7593777 : Nat := 3899257584057441046264361

theorem tailTrace_7593777 : CollatzResearch.WordTrace tailWord_7593777 prefixEnd_7593777 3899257584057441046264361 := by
  unfold tailWord_7593777
  simp only [CollatzResearch.WordTrace]
  refine ⟨276967801010050317704123585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184645200673366878469415723 276967801010050317704123585)
  ·
    refine ⟨207725850757537738278092689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276967801010050317704123585 207725850757537738278092689)
    ·
      refine ⟨155794388068153303708569517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207725850757537738278092689 155794388068153303708569517)
      ·
        refine ⟨58422895525557488890713569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155794388068153303708569517 58422895525557488890713569)
        ·
          refine ⟨43817171644168116668035177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58422895525557488890713569 43817171644168116668035177)
          ·
            refine ⟨32862878733126087501026383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43817171644168116668035177 32862878733126087501026383)
            ·
              refine ⟨49294318099689131251539575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32862878733126087501026383 49294318099689131251539575)
              ·
                refine ⟨73941477149533696877309363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49294318099689131251539575 73941477149533696877309363)
                ·
                  refine ⟨110912215724300545315964045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73941477149533696877309363 110912215724300545315964045)
                  ·
                    refine ⟨41592080896612704493486517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110912215724300545315964045 41592080896612704493486517)
                    ·
                      refine ⟨3899257584057441046264361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41592080896612704493486517 3899257584057441046264361)
                      ·
                        rfl

theorem cell23_7593777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_7593777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593777 prefixEnd_7593777 := by exact prefixLift 7593777
  have htrace : WordTrace (prefixWord ++ tailWord_7593777) baseStart_7593777 baseEnd_7593777 := by
    simpa [prefixWord, tailWord_7593777, baseEnd_7593777] using wordTrace_append hprefix tailTrace_7593777
  have hstable : (prefixWord ++ tailWord_7593777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593777).length < 2 ^ (prefixWord ++ tailWord_7593777).sum := by decide
  have hdescent : baseEnd_7593777 < baseStart_7593777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593847 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_7593847 : Nat := 118140960795 + 7593847 * 2 ^ 59
def prefixEnd_7593847 : Nat := 4983230072969 + 3 ^ 40 * 7593847 * 2
def baseEnd_7593847 : Nat := 3899293527703255772389039

theorem tailTrace_7593847 : CollatzResearch.WordTrace tailWord_7593847 prefixEnd_7593847 3899293527703255772389039 := by
  unfold tailWord_7593847
  simp only [CollatzResearch.WordTrace]
  refine ⟨276970354119796719659171795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184646902746531146439447863 276970354119796719659171795)
  ·
    refine ⟨415455531179695079488757693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276970354119796719659171795 415455531179695079488757693)
    ·
      refine ⟨155795824192385654808284135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415455531179695079488757693 155795824192385654808284135)
      ·
        refine ⟨233693736288578482212426203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155795824192385654808284135 233693736288578482212426203)
        ·
          refine ⟨350540604432867723318639305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233693736288578482212426203 350540604432867723318639305)
          ·
            refine ⟨262905453324650792488979479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350540604432867723318639305 262905453324650792488979479)
            ·
              refine ⟨394358179986976188733469219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262905453324650792488979479 394358179986976188733469219)
              ·
                refine ⟨591537269980464283100203829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394358179986976188733469219 591537269980464283100203829)
                ·
                  refine ⟨55456619060668526540644109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 591537269980464283100203829 55456619060668526540644109)
                  ·
                    refine ⟨20796232147750697452741541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55456619060668526540644109 20796232147750697452741541)
                    ·
                      refine ⟨3899293527703255772389039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20796232147750697452741541 3899293527703255772389039)
                      ·
                        rfl

theorem cell23_7593847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_7593847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593847 prefixEnd_7593847 := by exact prefixLift 7593847
  have htrace : WordTrace (prefixWord ++ tailWord_7593847) baseStart_7593847 baseEnd_7593847 := by
    simpa [prefixWord, tailWord_7593847, baseEnd_7593847] using wordTrace_append hprefix tailTrace_7593847
  have hstable : (prefixWord ++ tailWord_7593847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593847).length < 2 ^ (prefixWord ++ tailWord_7593847).sum := by decide
  have hdescent : baseEnd_7593847 < baseStart_7593847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593907 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 8]
def baseStart_7593907 : Nat := 118140960795 + 7593907 * 2 ^ 59
def prefixEnd_7593907 : Nat := 4983230072969 + 3 ^ 40 * 7593907 * 2
def baseEnd_7593907 : Nat := 3899324336542525537638763

theorem tailTrace_7593907 : CollatzResearch.WordTrace tailWord_7593907 prefixEnd_7593907 3899324336542525537638763 := by
  unfold tailWord_7593907
  simp only [CollatzResearch.WordTrace]
  refine ⟨276972542499579349906355975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184648361666386233270903983 276972542499579349906355975)
  ·
    refine ⟨415458813749369024859533963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276972542499579349906355975 415458813749369024859533963)
    ·
      refine ⟨623188220624053537289300945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415458813749369024859533963 623188220624053537289300945)
      ·
        refine ⟨467391165468040152966975709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623188220624053537289300945 467391165468040152966975709)
        ·
          refine ⟨175271687050515057362615891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467391165468040152966975709 175271687050515057362615891)
          ·
            refine ⟨262907530575772586043923837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175271687050515057362615891 262907530575772586043923837)
            ·
              refine ⟨98590323965914719766471439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262907530575772586043923837 98590323965914719766471439)
              ·
                refine ⟨147885485948872079649707159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98590323965914719766471439 147885485948872079649707159)
                ·
                  refine ⟨221828228923308119474560739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147885485948872079649707159 221828228923308119474560739)
                  ·
                    refine ⟨332742343384962179211841109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221828228923308119474560739 332742343384962179211841109)
                    ·
                      refine ⟨3899324336542525537638763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 332742343384962179211841109 3899324336542525537638763)
                      ·
                        rfl

theorem cell23_7593907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_7593907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593907 prefixEnd_7593907 := by exact prefixLift 7593907
  have htrace : WordTrace (prefixWord ++ tailWord_7593907) baseStart_7593907 baseEnd_7593907 := by
    simpa [prefixWord, tailWord_7593907, baseEnd_7593907] using wordTrace_append hprefix tailTrace_7593907
  have hstable : (prefixWord ++ tailWord_7593907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593907).length < 2 ^ (prefixWord ++ tailWord_7593907).sum := by decide
  have hdescent : baseEnd_7593907 < baseStart_7593907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593931 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 3, 1, 3]
def baseStart_7593931 : Nat := 118140960795 + 7593931 * 2 ^ 59
def prefixEnd_7593931 : Nat := 4983230072969 + 3 ^ 40 * 7593931 * 2
def baseEnd_7593931 : Nat := 3899336660078233443738653

theorem tailTrace_7593931 : CollatzResearch.WordTrace tailWord_7593931 prefixEnd_7593931 3899336660078233443738653 := by
  unfold tailWord_7593931
  simp only [CollatzResearch.WordTrace]
  refine ⟨276973417851492402005229647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184648945234328268003486431 276973417851492402005229647)
  ·
    refine ⟨415460126777238603007844471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276973417851492402005229647 415460126777238603007844471)
    ·
      refine ⟨623190190165857904511766707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415460126777238603007844471 623190190165857904511766707)
      ·
        refine ⟨934785285248786856767650061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623190190165857904511766707 934785285248786856767650061)
        ·
          refine ⟨350544481968295071287868773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 934785285248786856767650061 350544481968295071287868773)
          ·
            refine ⟨65727090369055325866475395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350544481968295071287868773 65727090369055325866475395)
            ·
              refine ⟨98590635553582988799713093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65727090369055325866475395 98590635553582988799713093)
              ·
                refine ⟨18485744166296810399946205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98590635553582988799713093 18485744166296810399946205)
                ·
                  refine ⟨6932154062361303899979827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18485744166296810399946205 6932154062361303899979827)
                  ·
                    refine ⟨10398231093541955849969741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6932154062361303899979827 10398231093541955849969741)
                    ·
                      refine ⟨3899336660078233443738653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10398231093541955849969741 3899336660078233443738653)
                      ·
                        rfl

theorem cell23_7593931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 1, 3].length) (baseStart_7593931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593931 prefixEnd_7593931 := by exact prefixLift 7593931
  have htrace : WordTrace (prefixWord ++ tailWord_7593931) baseStart_7593931 baseEnd_7593931 := by
    simpa [prefixWord, tailWord_7593931, baseEnd_7593931] using wordTrace_append hprefix tailTrace_7593931
  have hstable : (prefixWord ++ tailWord_7593931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593931).length < 2 ^ (prefixWord ++ tailWord_7593931).sum := by decide
  have hdescent : baseEnd_7593931 < baseStart_7593931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7593951 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 1, 5]
def baseStart_7593951 : Nat := 118140960795 + 7593951 * 2 ^ 59
def prefixEnd_7593951 : Nat := 4983230072969 + 3 ^ 40 * 7593951 * 2
def baseEnd_7593951 : Nat := 1299782309897107788496187

theorem tailTrace_7593951 : CollatzResearch.WordTrace tailWord_7593951 prefixEnd_7593951 1299782309897107788496187 := by
  unfold tailWord_7593951
  simp only [CollatzResearch.WordTrace]
  refine ⟨276974147311419945420957707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184649431540946630280638471 276974147311419945420957707)
  ·
    refine ⟨415461220967129918131436561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276974147311419945420957707 415461220967129918131436561)
    ·
      refine ⟨311595915725347438598577421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415461220967129918131436561 311595915725347438598577421)
      ·
        refine ⟨116848468397005289474466533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311595915725347438598577421 116848468397005289474466533)
        ·
          refine ⟨21909087824438491776462475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116848468397005289474466533 21909087824438491776462475)
          ·
            refine ⟨32863631736657737664693713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21909087824438491776462475 32863631736657737664693713)
            ·
              refine ⟨24647723802493303248520285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32863631736657737664693713 24647723802493303248520285)
              ·
                refine ⟨9242896425934988718195107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24647723802493303248520285 9242896425934988718195107)
                ·
                  refine ⟨13864344638902483077292661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9242896425934988718195107 13864344638902483077292661)
                  ·
                    refine ⟨1299782309897107788496187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13864344638902483077292661 1299782309897107788496187)
                    ·
                      rfl

theorem cell23_7593951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 5].length) (baseStart_7593951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7593951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7593951 prefixEnd_7593951 := by exact prefixLift 7593951
  have htrace : WordTrace (prefixWord ++ tailWord_7593951) baseStart_7593951 baseEnd_7593951 := by
    simpa [prefixWord, tailWord_7593951, baseEnd_7593951] using wordTrace_append hprefix tailTrace_7593951
  have hstable : (prefixWord ++ tailWord_7593951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7593951).length < 2 ^ (prefixWord ++ tailWord_7593951).sum := by decide
  have hdescent : baseEnd_7593951 < baseStart_7593951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7593951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594005 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 1, 1, 4]
def baseStart_7594005 : Nat := 118140960795 + 7594005 * 2 ^ 59
def prefixEnd_7594005 : Nat := 4983230072969 + 3 ^ 40 * 7594005 * 2
def baseEnd_7594005 : Nat := 3899374657646666154213313

theorem tailTrace_7594005 : CollatzResearch.WordTrace tailWord_7594005 prefixEnd_7594005 3899374657646666154213313 := by
  unfold tailWord_7594005
  simp only [CollatzResearch.WordTrace]
  refine ⟨276976116853224312643423469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184650744568816208428948979 276976116853224312643423469)
  ·
    refine ⟨103866043819959117241283801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276976116853224312643423469 103866043819959117241283801)
    ·
      refine ⟨77899532864969337930962851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103866043819959117241283801 77899532864969337930962851)
      ·
        refine ⟨116849299297454006896444277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77899532864969337930962851 116849299297454006896444277)
        ·
          refine ⟨10954621809136313146541651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116849299297454006896444277 10954621809136313146541651)
          ·
            refine ⟨16431932713704469719812477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10954621809136313146541651 16431932713704469719812477)
            ·
              refine ⟨6161974767639176144929679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16431932713704469719812477 6161974767639176144929679)
              ·
                refine ⟨9242962151458764217394519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6161974767639176144929679 9242962151458764217394519)
                ·
                  refine ⟨13864443227188146326091779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9242962151458764217394519 13864443227188146326091779)
                  ·
                    refine ⟨20796664840782219489137669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13864443227188146326091779 20796664840782219489137669)
                    ·
                      refine ⟨3899374657646666154213313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20796664840782219489137669 3899374657646666154213313)
                      ·
                        rfl

theorem cell23_7594005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_7594005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594005 prefixEnd_7594005 := by exact prefixLift 7594005
  have htrace : WordTrace (prefixWord ++ tailWord_7594005) baseStart_7594005 baseEnd_7594005 := by
    simpa [prefixWord, tailWord_7594005, baseEnd_7594005] using wordTrace_append hprefix tailTrace_7594005
  have hstable : (prefixWord ++ tailWord_7594005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594005).length < 2 ^ (prefixWord ++ tailWord_7594005).sum := by decide
  have hdescent : baseEnd_7594005 < baseStart_7594005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594048 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 3, 3, 2]
def baseStart_7594048 : Nat := 118140960795 + 7594048 * 2 ^ 59
def prefixEnd_7594048 : Nat := 4983230072969 + 3 ^ 40 * 7594048 * 2
def baseEnd_7594048 : Nat := 3899396737314809485975615

theorem tailTrace_7594048 : CollatzResearch.WordTrace tailWord_7594048 prefixEnd_7594048 3899396737314809485975615 := by
  unfold tailWord_7594048
  simp only [CollatzResearch.WordTrace]
  refine ⟨138488842596034265493619399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184651790128045687324825865 138488842596034265493619399)
  ·
    refine ⟨207733263894051398240429099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138488842596034265493619399 207733263894051398240429099)
    ·
      refine ⟨311599895841077097360643649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207733263894051398240429099 311599895841077097360643649)
      ·
        refine ⟨233699921880807823020482737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311599895841077097360643649 233699921880807823020482737)
        ·
          refine ⟨175274941410605867265362053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233699921880807823020482737 175274941410605867265362053)
          ·
            refine ⟨32864051514488600112255385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175274941410605867265362053 32864051514488600112255385)
            ·
              refine ⟨24648038635866450084191539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32864051514488600112255385 24648038635866450084191539)
              ·
                refine ⟨36972057953799675126287309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24648038635866450084191539 36972057953799675126287309)
                ·
                  refine ⟨13864521732674878172357741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36972057953799675126287309 13864521732674878172357741)
                  ·
                    refine ⟨5199195649753079314634153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13864521732674878172357741 5199195649753079314634153)
                    ·
                      refine ⟨3899396737314809485975615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5199195649753079314634153 3899396737314809485975615)
                      ·
                        rfl

theorem cell23_7594048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 3, 2].length) (baseStart_7594048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594048 prefixEnd_7594048 := by exact prefixLift 7594048
  have htrace : WordTrace (prefixWord ++ tailWord_7594048) baseStart_7594048 baseEnd_7594048 := by
    simpa [prefixWord, tailWord_7594048, baseEnd_7594048] using wordTrace_append hprefix tailTrace_7594048
  have hstable : (prefixWord ++ tailWord_7594048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594048).length < 2 ^ (prefixWord ++ tailWord_7594048).sum := by decide
  have hdescent : baseEnd_7594048 < baseStart_7594048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594095 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 1, 4, 2]
def baseStart_7594095 : Nat := 118140960795 + 7594095 * 2 ^ 59
def prefixEnd_7594095 : Nat := 4983230072969 + 3 ^ 40 * 7594095 * 2
def baseEnd_7594095 : Nat := 3899420870905570802087899

theorem tailTrace_7594095 : CollatzResearch.WordTrace tailWord_7594095 prefixEnd_7594095 3899420870905570802087899 := by
  unfold tailWord_7594095
  simp only [CollatzResearch.WordTrace]
  refine ⟨276979399422898258014199739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184652932948598838676133159 276979399422898258014199739)
  ·
    refine ⟨415469099134347387021299609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276979399422898258014199739 415469099134347387021299609)
    ·
      refine ⟨311601824350760540265974707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415469099134347387021299609 311601824350760540265974707)
      ·
        refine ⟨467402736526140810398962061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311601824350760540265974707 467402736526140810398962061)
        ·
          refine ⟨175276026197302803899610773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467402736526140810398962061 175276026197302803899610773)
          ·
            refine ⟨8216063727998568932794255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 175276026197302803899610773 8216063727998568932794255)
            ·
              refine ⟨12324095591997853399191383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8216063727998568932794255 12324095591997853399191383)
              ·
                refine ⟨18486143387996780098787075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12324095591997853399191383 18486143387996780098787075)
                ·
                  refine ⟨27729215081995170148180613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18486143387996780098787075 27729215081995170148180613)
                  ·
                    refine ⟨5199227827874094402783865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27729215081995170148180613 5199227827874094402783865)
                    ·
                      refine ⟨3899420870905570802087899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5199227827874094402783865 3899420870905570802087899)
                      ·
                        rfl

theorem cell23_7594095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 4, 2].length) (baseStart_7594095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594095 prefixEnd_7594095 := by exact prefixLift 7594095
  have htrace : WordTrace (prefixWord ++ tailWord_7594095) baseStart_7594095 baseEnd_7594095 := by
    simpa [prefixWord, tailWord_7594095, baseEnd_7594095] using wordTrace_append hprefix tailTrace_7594095
  have hstable : (prefixWord ++ tailWord_7594095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594095).length < 2 ^ (prefixWord ++ tailWord_7594095).sum := by decide
  have hdescent : baseEnd_7594095 < baseStart_7594095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594135 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 7]
def baseStart_7594135 : Nat := 118140960795 + 7594135 * 2 ^ 59
def prefixEnd_7594135 : Nat := 4983230072969 + 3 ^ 40 * 7594135 * 2
def baseEnd_7594135 : Nat := 433271267792416738398635

theorem tailTrace_7594135 : CollatzResearch.WordTrace tailWord_7594135 prefixEnd_7594135 433271267792416738398635 := by
  unfold tailWord_7594135
  simp only [CollatzResearch.WordTrace]
  refine ⟨276980858342753344845655859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184653905561835563230437239 276980858342753344845655859)
  ·
    refine ⟨415471287514130017268483789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276980858342753344845655859 415471287514130017268483789)
    ·
      refine ⟨155801732817798756475681421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415471287514130017268483789 155801732817798756475681421)
      ·
        refine ⟨58425649806674533678380533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155801732817798756475681421 58425649806674533678380533)
        ·
          refine ⟨5477404669375737532348175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58425649806674533678380533 5477404669375737532348175)
          ·
            refine ⟨8216107004063606298522263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5477404669375737532348175 8216107004063606298522263)
            ·
              refine ⟨12324160506095409447783395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8216107004063606298522263 12324160506095409447783395)
              ·
                refine ⟨18486240759143114171675093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12324160506095409447783395 18486240759143114171675093)
                ·
                  refine ⟨433271267792416738398635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18486240759143114171675093 433271267792416738398635)
                  ·
                    rfl

theorem cell23_7594135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 7].length) (baseStart_7594135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594135 prefixEnd_7594135 := by exact prefixLift 7594135
  have htrace : WordTrace (prefixWord ++ tailWord_7594135) baseStart_7594135 baseEnd_7594135 := by
    simpa [prefixWord, tailWord_7594135, baseEnd_7594135] using wordTrace_append hprefix tailTrace_7594135
  have hstable : (prefixWord ++ tailWord_7594135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594135).length < 2 ^ (prefixWord ++ tailWord_7594135).sum := by decide
  have hdescent : baseEnd_7594135 < baseStart_7594135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594141 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_7594141 : Nat := 118140960795 + 7594141 * 2 ^ 59
def prefixEnd_7594141 : Nat := 4983230072969 + 3 ^ 40 * 7594141 * 2
def baseEnd_7594141 : Nat := 3899444491015677622112687

theorem tailTrace_7594141 : CollatzResearch.WordTrace tailWord_7594141 prefixEnd_7594141 3899444491015677622112687 := by
  unfold tailWord_7594141
  simp only [CollatzResearch.WordTrace]
  refine ⟨276981077180731607870374277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184654051453821071913582851 276981077180731607870374277)
  ·
    refine ⟨51933951971387176475695177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276981077180731607870374277 51933951971387176475695177)
    ·
      refine ⟨38950463978540382356771383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51933951971387176475695177 38950463978540382356771383)
      ·
        refine ⟨58425695967810573535157075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38950463978540382356771383 58425695967810573535157075)
        ·
          refine ⟨87638543951715860302735613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58425695967810573535157075 87638543951715860302735613)
          ·
            refine ⟨32864453981893447613525855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87638543951715860302735613 32864453981893447613525855)
            ·
              refine ⟨49296680972840171420288783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32864453981893447613525855 49296680972840171420288783)
              ·
                refine ⟨73945021459260257130433175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49296680972840171420288783 73945021459260257130433175)
                ·
                  refine ⟨110917532188890385695649763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73945021459260257130433175 110917532188890385695649763)
                  ·
                    refine ⟨166376298283335578543474645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110917532188890385695649763 166376298283335578543474645)
                    ·
                      refine ⟨3899444491015677622112687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166376298283335578543474645 3899444491015677622112687)
                      ·
                        rfl

theorem cell23_7594141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_7594141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594141 prefixEnd_7594141 := by exact prefixLift 7594141
  have htrace : WordTrace (prefixWord ++ tailWord_7594141) baseStart_7594141 baseEnd_7594141 := by
    simpa [prefixWord, tailWord_7594141, baseEnd_7594141] using wordTrace_append hprefix tailTrace_7594141
  have hstable : (prefixWord ++ tailWord_7594141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594141).length < 2 ^ (prefixWord ++ tailWord_7594141).sum := by decide
  have hdescent : baseEnd_7594141 < baseStart_7594141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594146 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_7594146 : Nat := 118140960795 + 7594146 * 2 ^ 59
def prefixEnd_7594146 : Nat := 4983230072969 + 3 ^ 40 * 7594146 * 2
def baseEnd_7594146 : Nat := 3899447058418950102550165

theorem tailTrace_7594146 : CollatzResearch.WordTrace tailWord_7594146 prefixEnd_7594146 3899447058418950102550165 := by
  unfold tailWord_7594146
  simp only [CollatzResearch.WordTrace]
  refine ⟨69245314886428373431076573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184654173030475662482870861 69245314886428373431076573)
  ·
    refine ⟨25966993082410640036653715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69245314886428373431076573 25966993082410640036653715)
    ·
      refine ⟨38950489623615960054980573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25966993082410640036653715 38950489623615960054980573)
      ·
        refine ⟨14606433608855985020617715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38950489623615960054980573 14606433608855985020617715)
        ·
          refine ⟨21909650413283977530926573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14606433608855985020617715 21909650413283977530926573)
          ·
            refine ⟨8216118904981491574097465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21909650413283977530926573 8216118904981491574097465)
            ·
              refine ⟨6162089178736118680573099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8216118904981491574097465 6162089178736118680573099)
              ·
                refine ⟨9243133768104178020859649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6162089178736118680573099 9243133768104178020859649)
                ·
                  refine ⟨6932350326078133515644737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9243133768104178020859649 6932350326078133515644737)
                  ·
                    refine ⟨5199262744558600136733553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6932350326078133515644737 5199262744558600136733553)
                    ·
                      refine ⟨3899447058418950102550165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5199262744558600136733553 3899447058418950102550165)
                      ·
                        rfl

theorem cell23_7594146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_7594146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594146 prefixEnd_7594146 := by exact prefixLift 7594146
  have htrace : WordTrace (prefixWord ++ tailWord_7594146) baseStart_7594146 baseEnd_7594146 := by
    simpa [prefixWord, tailWord_7594146, baseEnd_7594146] using wordTrace_append hprefix tailTrace_7594146
  have hstable : (prefixWord ++ tailWord_7594146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594146).length < 2 ^ (prefixWord ++ tailWord_7594146).sum := by decide
  have hdescent : baseEnd_7594146 < baseStart_7594146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594168 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 2, 1, 4]
def baseStart_7594168 : Nat := 118140960795 + 7594168 * 2 ^ 59
def prefixEnd_7594168 : Nat := 4983230072969 + 3 ^ 40 * 7594168 * 2
def baseEnd_7594168 : Nat := 3899458354993349016475063

theorem tailTrace_7594168 : CollatzResearch.WordTrace tailWord_7594168 prefixEnd_7594168 3899458354993349016475063 := by
  unfold tailWord_7594168
  simp only [CollatzResearch.WordTrace]
  refine ⟨138491030975816895740803579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184654707967755860987738105 138491030975816895740803579)
  ·
    refine ⟨207736546463725343611205369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138491030975816895740803579 207736546463725343611205369)
    ·
      refine ⟨155802409847794007708404027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207736546463725343611205369 155802409847794007708404027)
      ·
        refine ⟨233703614771691011562606041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155802409847794007708404027 233703614771691011562606041)
        ·
          refine ⟨175277711078768258671954531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233703614771691011562606041 175277711078768258671954531)
          ·
            refine ⟨262916566618152388007931797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175277711078768258671954531 262916566618152388007931797)
            ·
              refine ⟨12324214060225893187871803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 262916566618152388007931797 12324214060225893187871803)
              ·
                refine ⟨18486321090338839781807705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12324214060225893187871803 18486321090338839781807705)
                ·
                  refine ⟨13864740817754129836355779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18486321090338839781807705 13864740817754129836355779)
                  ·
                    refine ⟨20797111226631194754533669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13864740817754129836355779 20797111226631194754533669)
                    ·
                      refine ⟨3899458354993349016475063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20797111226631194754533669 3899458354993349016475063)
                      ·
                        rfl

theorem cell23_7594168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_7594168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594168 prefixEnd_7594168 := by exact prefixLift 7594168
  have htrace : WordTrace (prefixWord ++ tailWord_7594168) baseStart_7594168 baseEnd_7594168 := by
    simpa [prefixWord, tailWord_7594168, baseEnd_7594168] using wordTrace_append hprefix tailTrace_7594168
  have hstable : (prefixWord ++ tailWord_7594168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594168).length < 2 ^ (prefixWord ++ tailWord_7594168).sum := by decide
  have hdescent : baseEnd_7594168 < baseStart_7594168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594242 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 6]
def baseStart_7594242 : Nat := 118140960795 + 7594242 * 2 ^ 59
def prefixEnd_7594242 : Nat := 4983230072969 + 3 ^ 40 * 7594242 * 2
def baseEnd_7594242 : Nat := 433277372506864636327747

theorem tailTrace_7594242 : CollatzResearch.WordTrace tailWord_7594242 prefixEnd_7594242 433277372506864636327747 := by
  unfold tailWord_7594242
  simp only [CollatzResearch.WordTrace]
  refine ⟨69246190238341425529950245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184656507302243801413200653 69246190238341425529950245)
  ·
    refine ⟨12983660669689017286865671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69246190238341425529950245 12983660669689017286865671)
    ·
      refine ⟨19475491004533525930298507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12983660669689017286865671 19475491004533525930298507)
      ·
        refine ⟨29213236506800288895447761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19475491004533525930298507 29213236506800288895447761)
        ·
          refine ⟨21909927380100216671585821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29213236506800288895447761 21909927380100216671585821)
          ·
            refine ⟨8216222767537581251844683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21909927380100216671585821 8216222767537581251844683)
            ·
              refine ⟨12324334151306371877767025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8216222767537581251844683 12324334151306371877767025)
              ·
                refine ⟨9243250613479778908325269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12324334151306371877767025 9243250613479778908325269)
                ·
                  refine ⟨433277372506864636327747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9243250613479778908325269 433277372506864636327747)
                  ·
                    rfl

theorem cell23_7594242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_7594242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594242 prefixEnd_7594242 := by exact prefixLift 7594242
  have htrace : WordTrace (prefixWord ++ tailWord_7594242) baseStart_7594242 baseEnd_7594242 := by
    simpa [prefixWord, tailWord_7594242, baseEnd_7594242] using wordTrace_append hprefix tailTrace_7594242
  have hstable : (prefixWord ++ tailWord_7594242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594242).length < 2 ^ (prefixWord ++ tailWord_7594242).sum := by decide
  have hdescent : baseEnd_7594242 < baseStart_7594242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594252 : List Nat := [2, 2, 1, 2, 2, 2, 1, 6, 1, 1, 3]
def baseStart_7594252 : Nat := 118140960795 + 7594252 * 2 ^ 59
def prefixEnd_7594252 : Nat := 4983230072969 + 3 ^ 40 * 7594252 * 2
def baseEnd_7594252 : Nat := 3899501487368326687824677

theorem tailTrace_7594252 : CollatzResearch.WordTrace tailWord_7594252 prefixEnd_7594252 3899501487368326687824677 := by
  unfold tailWord_7594252
  simp only [CollatzResearch.WordTrace]
  refine ⟨138492562841664736913832505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184656750455552982551776673 138492562841664736913832505)
  ·
    refine ⟨103869422131248552685374379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138492562841664736913832505 103869422131248552685374379)
    ·
      refine ⟨155804133196872829028061569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103869422131248552685374379 155804133196872829028061569)
      ·
        refine ⟨116853099897654621771046177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155804133196872829028061569 116853099897654621771046177)
        ·
          refine ⟨87639824923240966328284633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116853099897654621771046177 87639824923240966328284633)
          ·
            refine ⟨65729868692430724746213475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87639824923240966328284633 65729868692430724746213475)
            ·
              refine ⟨98594803038646087119320213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65729868692430724746213475 98594803038646087119320213)
              ·
                refine ⟨4621631392436535333718135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98594803038646087119320213 4621631392436535333718135)
                ·
                  refine ⟨6932447088654803000577203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621631392436535333718135 6932447088654803000577203)
                  ·
                    refine ⟨10398670632982204500865805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6932447088654803000577203 10398670632982204500865805)
                    ·
                      refine ⟨3899501487368326687824677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10398670632982204500865805 3899501487368326687824677)
                      ·
                        rfl

theorem cell23_7594252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_7594252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594252 prefixEnd_7594252 := by exact prefixLift 7594252
  have htrace : WordTrace (prefixWord ++ tailWord_7594252) baseStart_7594252 baseEnd_7594252 := by
    simpa [prefixWord, tailWord_7594252, baseEnd_7594252] using wordTrace_append hprefix tailTrace_7594252
  have hstable : (prefixWord ++ tailWord_7594252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594252).length < 2 ^ (prefixWord ++ tailWord_7594252).sum := by decide
  have hdescent : baseEnd_7594252 < baseStart_7594252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594275 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 4]
def baseStart_7594275 : Nat := 118140960795 + 7594275 * 2 ^ 59
def prefixEnd_7594275 : Nat := 4983230072969 + 3 ^ 40 * 7594275 * 2
def baseEnd_7594275 : Nat := 3899513297423380097837071

theorem tailTrace_7594275 : CollatzResearch.WordTrace tailWord_7594275 prefixEnd_7594275 3899513297423380097837071 := by
  unfold tailWord_7594275
  simp only [CollatzResearch.WordTrace]
  refine ⟨276985964562246148755752279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184657309708164099170501519 276985964562246148755752279)
  ·
    refine ⟨415478946843369223133628419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276985964562246148755752279 415478946843369223133628419)
    ·
      refine ⟨623218420265053834700442629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415478946843369223133628419 623218420265053834700442629)
      ·
        refine ⟨116853453799697594006332993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 623218420265053834700442629 116853453799697594006332993)
        ·
          refine ⟨87640090349773195504749745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116853453799697594006332993 87640090349773195504749745)
          ·
            refine ⟨65730067762329896628562309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87640090349773195504749745 65730067762329896628562309)
            ·
              refine ⟨12324387705436855617855433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65730067762329896628562309 12324387705436855617855433)
              ·
                refine ⟨9243290779077641713391575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12324387705436855617855433 9243290779077641713391575)
                ·
                  refine ⟨13864936168616462570087363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9243290779077641713391575 13864936168616462570087363)
                  ·
                    refine ⟨20797404252924693855131045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13864936168616462570087363 20797404252924693855131045)
                    ·
                      refine ⟨3899513297423380097837071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20797404252924693855131045 3899513297423380097837071)
                      ·
                        rfl

theorem cell23_7594275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_7594275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594275 prefixEnd_7594275 := by exact prefixLift 7594275
  have htrace : WordTrace (prefixWord ++ tailWord_7594275) baseStart_7594275 baseEnd_7594275 := by
    simpa [prefixWord, tailWord_7594275, baseEnd_7594275] using wordTrace_append hprefix tailTrace_7594275
  have hstable : (prefixWord ++ tailWord_7594275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594275).length < 2 ^ (prefixWord ++ tailWord_7594275).sum := by decide
  have hdescent : baseEnd_7594275 < baseStart_7594275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594292 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_7594292 : Nat := 118140960795 + 7594292 * 2 ^ 59
def prefixEnd_7594292 : Nat := 4983230072969 + 3 ^ 40 * 7594292 * 2
def baseEnd_7594292 : Nat := 3899522026594506531324493

theorem tailTrace_7594292 : CollatzResearch.WordTrace tailWord_7594292 prefixEnd_7594292 3899522026594506531324493 := by
  unfold tailWord_7594292
  simp only [CollatzResearch.WordTrace]
  refine ⟨138493292301592280329560565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184657723068789707106080753 138493292301592280329560565)
  ·
    refine ⟨12983746153274276280896303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138493292301592280329560565 12983746153274276280896303)
    ·
      refine ⟨19475619229911414421344455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12983746153274276280896303 19475619229911414421344455)
      ·
        refine ⟨29213428844867121632016683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19475619229911414421344455 29213428844867121632016683)
        ·
          refine ⟨43820143267300682448025025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29213428844867121632016683 43820143267300682448025025)
          ·
            refine ⟨32865107450475511836018769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43820143267300682448025025 32865107450475511836018769)
            ·
              refine ⟨24648830587856633877014077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32865107450475511836018769 24648830587856633877014077)
              ·
                refine ⟨9243311470446237703880279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24648830587856633877014077 9243311470446237703880279)
                ·
                  refine ⟨13864967205669356555820419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9243311470446237703880279 13864967205669356555820419)
                  ·
                    refine ⟨20797450808504034833730629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13864967205669356555820419 20797450808504034833730629)
                    ·
                      refine ⟨3899522026594506531324493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20797450808504034833730629 3899522026594506531324493)
                      ·
                        rfl

theorem cell23_7594292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_7594292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594292 prefixEnd_7594292 := by exact prefixLift 7594292
  have htrace : WordTrace (prefixWord ++ tailWord_7594292) baseStart_7594292 baseEnd_7594292 := by
    simpa [prefixWord, tailWord_7594292, baseEnd_7594292] using wordTrace_append hprefix tailTrace_7594292
  have hstable : (prefixWord ++ tailWord_7594292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594292).length < 2 ^ (prefixWord ++ tailWord_7594292).sum := by decide
  have hdescent : baseEnd_7594292 < baseStart_7594292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594298 : List Nat := [3, 1, 1, 1, 4, 4, 9]
def baseStart_7594298 : Nat := 118140960795 + 7594298 * 2 ^ 59
def prefixEnd_7594298 : Nat := 4983230072969 + 3 ^ 40 * 7594298 * 2
def baseEnd_7594298 : Nat := 48142285277511524788265

theorem tailTrace_7594298 : CollatzResearch.WordTrace tailWord_7594298 prefixEnd_7594298 48142285277511524788265 := by
  unfold tailWord_7594298
  simp only [CollatzResearch.WordTrace]
  refine ⟨69246700860290705920959887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184657868960775215789226365 69246700860290705920959887)
  ·
    refine ⟨103870051290436058881439831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69246700860290705920959887 103870051290436058881439831)
    ·
      refine ⟨155805076935654088322159747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103870051290436058881439831 155805076935654088322159747)
      ·
        refine ⟨233707615403481132483239621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155805076935654088322159747 233707615403481132483239621)
        ·
          refine ⟨43820177888152712340607429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233707615403481132483239621 43820177888152712340607429)
          ·
            refine ⟨8216283354028633563863893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43820177888152712340607429 8216283354028633563863893)
            ·
              refine ⟨48142285277511524788265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8216283354028633563863893 48142285277511524788265)
              ·
                rfl

theorem cell23_7594298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 9].length) (baseStart_7594298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594298 prefixEnd_7594298 := by exact prefixLift 7594298
  have htrace : WordTrace (prefixWord ++ tailWord_7594298) baseStart_7594298 baseEnd_7594298 := by
    simpa [prefixWord, tailWord_7594298, baseEnd_7594298] using wordTrace_append hprefix tailTrace_7594298
  have hstable : (prefixWord ++ tailWord_7594298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594298).length < 2 ^ (prefixWord ++ tailWord_7594298).sum := by decide
  have hdescent : baseEnd_7594298 < baseStart_7594298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594410 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7594410 : Nat := 118140960795 + 7594410 * 2 ^ 59
def prefixEnd_7594410 : Nat := 4983230072969 + 3 ^ 40 * 7594410 * 2
def baseEnd_7594410 : Nat := 3899582617311737069648951

theorem tailTrace_7594410 : CollatzResearch.WordTrace tailWord_7594410 prefixEnd_7594410 3899582617311737069648951 := by
  unfold tailWord_7594410
  simp only [CollatzResearch.WordTrace]
  refine ⟨69247722104189266702979171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184660592277838044541277789 69247722104189266702979171)
  ·
    refine ⟨103871583156283900054468757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69247722104189266702979171 103871583156283900054468757)
    ·
      refine ⟨4868980460450807815053223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103871583156283900054468757 4868980460450807815053223)
      ·
        refine ⟨7303470690676211722579835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4868980460450807815053223 7303470690676211722579835)
        ·
          refine ⟨10955206036014317583869753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7303470690676211722579835 10955206036014317583869753)
          ·
            refine ⟨8216404527010738187902315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10955206036014317583869753 8216404527010738187902315)
            ·
              refine ⟨12324606790516107281853473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8216404527010738187902315 12324606790516107281853473)
              ·
                refine ⟨9243455092887080461390105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12324606790516107281853473 9243455092887080461390105)
                ·
                  refine ⟨6932591319665310346042579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9243455092887080461390105 6932591319665310346042579)
                  ·
                    refine ⟨10398886979497965519063869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6932591319665310346042579 10398886979497965519063869)
                    ·
                      refine ⟨3899582617311737069648951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10398886979497965519063869 3899582617311737069648951)
                      ·
                        rfl

theorem cell23_7594410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7594410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594410 prefixEnd_7594410 := by exact prefixLift 7594410
  have htrace : WordTrace (prefixWord ++ tailWord_7594410) baseStart_7594410 baseEnd_7594410 := by
    simpa [prefixWord, tailWord_7594410, baseEnd_7594410] using wordTrace_append hprefix tailTrace_7594410
  have hstable : (prefixWord ++ tailWord_7594410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594410).length < 2 ^ (prefixWord ++ tailWord_7594410).sum := by decide
  have hdescent : baseEnd_7594410 < baseStart_7594410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594472 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_7594472 : Nat := 118140960795 + 7594472 * 2 ^ 59
def prefixEnd_7594472 : Nat := 4983230072969 + 3 ^ 40 * 7594472 * 2
def baseEnd_7594472 : Nat := 3899614453112315827073665

theorem tailTrace_7594472 : CollatzResearch.WordTrace tailWord_7594472 prefixEnd_7594472 3899614453112315827073665 := by
  unfold tailWord_7594472
  simp only [CollatzResearch.WordTrace]
  refine ⟨138496574871266225700336835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184662099828354967600449113 138496574871266225700336835)
  ·
    refine ⟨207744862306899338550505253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138496574871266225700336835 207744862306899338550505253)
    ·
      refine ⟨38952161682543625978219735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207744862306899338550505253 38952161682543625978219735)
      ·
        refine ⟨58428242523815438967329603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38952161682543625978219735 58428242523815438967329603)
        ·
          refine ⟨87642363785723158450994405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58428242523815438967329603 87642363785723158450994405)
          ·
            refine ⟨16432943209823092209561451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87642363785723158450994405 16432943209823092209561451)
            ·
              refine ⟨24649414814734638314342177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16432943209823092209561451 24649414814734638314342177)
              ·
                refine ⟨18487061111050978735756633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24649414814734638314342177 18487061111050978735756633)
                ·
                  refine ⟨13865295833288234051817475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18487061111050978735756633 13865295833288234051817475)
                  ·
                    refine ⟨20797943749932351077726213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13865295833288234051817475 20797943749932351077726213)
                    ·
                      refine ⟨3899614453112315827073665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20797943749932351077726213 3899614453112315827073665)
                      ·
                        rfl

theorem cell23_7594472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_7594472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594472 prefixEnd_7594472 := by exact prefixLift 7594472
  have htrace : WordTrace (prefixWord ++ tailWord_7594472) baseStart_7594472 baseEnd_7594472 := by
    simpa [prefixWord, tailWord_7594472, baseEnd_7594472] using wordTrace_append hprefix tailTrace_7594472
  have hstable : (prefixWord ++ tailWord_7594472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594472).length < 2 ^ (prefixWord ++ tailWord_7594472).sum := by decide
  have hdescent : baseEnd_7594472 < baseStart_7594472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594495 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 6]
def baseStart_7594495 : Nat := 118140960795 + 7594495 * 2 ^ 59
def prefixEnd_7594495 : Nat := 4983230072969 + 3 ^ 40 * 7594495 * 2
def baseEnd_7594495 : Nat := 433291807018596581898451

theorem tailTrace_7594495 : CollatzResearch.WordTrace tailWord_7594495 prefixEnd_7594495 433291807018596581898451 := by
  unfold tailWord_7594495
  simp only [CollatzResearch.WordTrace]
  refine ⟨276993988621449126328760939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184662659080966084219173959 276993988621449126328760939)
  ·
    refine ⟨415490982932173689493141409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276993988621449126328760939 415490982932173689493141409)
    ·
      refine ⟨311618237199130267119856057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415490982932173689493141409 311618237199130267119856057)
      ·
        refine ⟨233713677899347700339892043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311618237199130267119856057 233713677899347700339892043)
        ·
          refine ⟨350570516849021550509838065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233713677899347700339892043 350570516849021550509838065)
          ·
            refine ⟨262927887636766162882378549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350570516849021550509838065 262927887636766162882378549)
            ·
              refine ⟨24649489465946827770222989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262927887636766162882378549 24649489465946827770222989)
              ·
                refine ⟨9243558549730060413833621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24649489465946827770222989 9243558549730060413833621)
                ·
                  refine ⟨433291807018596581898451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9243558549730060413833621 433291807018596581898451)
                  ·
                    rfl

theorem cell23_7594495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 6].length) (baseStart_7594495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594495 prefixEnd_7594495 := by exact prefixLift 7594495
  have htrace : WordTrace (prefixWord ++ tailWord_7594495) baseStart_7594495 baseEnd_7594495 := by
    simpa [prefixWord, tailWord_7594495, baseEnd_7594495] using wordTrace_append hprefix tailTrace_7594495
  have hstable : (prefixWord ++ tailWord_7594495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594495).length < 2 ^ (prefixWord ++ tailWord_7594495).sum := by decide
  have hdescent : baseEnd_7594495 < baseStart_7594495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594572 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 4, 4]
def baseStart_7594572 : Nat := 118140960795 + 7594572 * 2 ^ 59
def prefixEnd_7594572 : Nat := 4983230072969 + 3 ^ 40 * 7594572 * 2
def baseEnd_7594572 : Nat := 1299888600392588478607735

theorem tailTrace_7594572 : CollatzResearch.WordTrace tailWord_7594572 prefixEnd_7594572 1299888600392588478607735 := by
  unfold tailWord_7594572
  simp only [CollatzResearch.WordTrace]
  refine ⟨138498398521085084239656985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184664531361446778986209313 138498398521085084239656985)
  ·
    refine ⟨103873798890813813179742739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138498398521085084239656985 103873798890813813179742739)
    ·
      refine ⟨155810698336220719769614109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103873798890813813179742739 155810698336220719769614109)
      ·
        refine ⟨58429011876082769913605291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155810698336220719769614109 58429011876082769913605291)
        ·
          refine ⟨87643517814124154870407937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58429011876082769913605291 87643517814124154870407937)
          ·
            refine ⟨65732638360593116152805953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87643517814124154870407937 65732638360593116152805953)
            ·
              refine ⟨49299478770444837114604465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65732638360593116152805953 49299478770444837114604465)
              ·
                refine ⟨36974609077833627835953349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49299478770444837114604465 36974609077833627835953349)
                ·
                  refine ⟨6932739202093805219241253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36974609077833627835953349 6932739202093805219241253)
                  ·
                    refine ⟨1299888600392588478607735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6932739202093805219241253 1299888600392588478607735)
                    ·
                      rfl

theorem cell23_7594572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_7594572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594572 prefixEnd_7594572 := by exact prefixLift 7594572
  have htrace : WordTrace (prefixWord ++ tailWord_7594572) baseStart_7594572 baseEnd_7594572 := by
    simpa [prefixWord, tailWord_7594572, baseEnd_7594572] using wordTrace_append hprefix tailTrace_7594572
  have hstable : (prefixWord ++ tailWord_7594572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594572).length < 2 ^ (prefixWord ++ tailWord_7594572).sum := by decide
  have hdescent : baseEnd_7594572 < baseStart_7594572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594573 : List Nat := [1, 6, 1, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_7594573 : Nat := 118140960795 + 7594573 * 2 ^ 59
def prefixEnd_7594573 : Nat := 4983230072969 + 3 ^ 40 * 7594573 * 2
def baseEnd_7594573 : Nat := 3899666314658419931910701

theorem tailTrace_7594573 : CollatzResearch.WordTrace tailWord_7594573 prefixEnd_7594573 3899666314658419931910701 := by
  unfold tailWord_7594573
  simp only [CollatzResearch.WordTrace]
  refine ⟨276996833515166545650100373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184664555676777697100066915 276996833515166545650100373)
  ·
    refine ⟨12984226571023431827348455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 276996833515166545650100373 12984226571023431827348455)
    ·
      refine ⟨19476339856535147741022683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12984226571023431827348455 19476339856535147741022683)
      ·
        refine ⟨29214509784802721611534025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19476339856535147741022683 29214509784802721611534025)
        ·
          refine ⟨21910882338602041208650519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29214509784802721611534025 21910882338602041208650519)
          ·
            refine ⟨32866323507903061812975779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21910882338602041208650519 32866323507903061812975779)
            ·
              refine ⟨49299485261854592719463669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32866323507903061812975779 49299485261854592719463669)
              ·
                refine ⟨4621826743298868067449719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49299485261854592719463669 4621826743298868067449719)
                ·
                  refine ⟨6932740114948302101174579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621826743298868067449719 6932740114948302101174579)
                  ·
                    refine ⟨10399110172422453151761869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6932740114948302101174579 10399110172422453151761869)
                    ·
                      refine ⟨3899666314658419931910701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10399110172422453151761869 3899666314658419931910701)
                      ·
                        rfl

theorem cell23_7594573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_7594573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594573 prefixEnd_7594573 := by exact prefixLift 7594573
  have htrace : WordTrace (prefixWord ++ tailWord_7594573) baseStart_7594573 baseEnd_7594573 := by
    simpa [prefixWord, tailWord_7594573, baseEnd_7594573] using wordTrace_append hprefix tailTrace_7594573
  have hstable : (prefixWord ++ tailWord_7594573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594573).length < 2 ^ (prefixWord ++ tailWord_7594573).sum := by decide
  have hdescent : baseEnd_7594573 < baseStart_7594573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594596 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 3, 2, 2]
def baseStart_7594596 : Nat := 118140960795 + 7594596 * 2 ^ 59
def prefixEnd_7594596 : Nat := 4983230072969 + 3 ^ 40 * 7594596 * 2
def baseEnd_7594596 : Nat := 3899678124713473341923095

theorem tailTrace_7594596 : CollatzResearch.WordTrace tailWord_7594596 prefixEnd_7594596 3899678124713473341923095 := by
  unfold tailWord_7594596
  simp only [CollatzResearch.WordTrace]
  refine ⟨138498836197041610289093821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184665114929388813718791761 138498836197041610289093821)
  ·
    refine ⟨51937063573890603858410183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138498836197041610289093821 51937063573890603858410183)
    ·
      refine ⟨77905595360835905787615275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51937063573890603858410183 77905595360835905787615275)
      ·
        refine ⟨116858393041253858681422913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77905595360835905787615275 116858393041253858681422913)
        ·
          refine ⟨87643794780940394011067185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116858393041253858681422913 87643794780940394011067185)
          ·
            refine ⟨65732846085705295508300389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87643794780940394011067185 65732846085705295508300389)
            ·
              refine ⟨12324908641069742907806323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65732846085705295508300389 12324908641069742907806323)
              ·
                refine ⟨18487362961604614361709485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12324908641069742907806323 18487362961604614361709485)
                ·
                  refine ⟨6932761110601730385641057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18487362961604614361709485 6932761110601730385641057)
                  ·
                    refine ⟨5199570832951297789230793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6932761110601730385641057 5199570832951297789230793)
                    ·
                      refine ⟨3899678124713473341923095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5199570832951297789230793 3899678124713473341923095)
                      ·
                        rfl

theorem cell23_7594596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_7594596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594596 prefixEnd_7594596 := by exact prefixLift 7594596
  have htrace : WordTrace (prefixWord ++ tailWord_7594596) baseStart_7594596 baseEnd_7594596 := by
    simpa [prefixWord, tailWord_7594596, baseEnd_7594596] using wordTrace_append hprefix tailTrace_7594596
  have hstable : (prefixWord ++ tailWord_7594596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594596).length < 2 ^ (prefixWord ++ tailWord_7594596).sum := by decide
  have hdescent : baseEnd_7594596 < baseStart_7594596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594615 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 2, 7]
def baseStart_7594615 : Nat := 118140960795 + 7594615 * 2 ^ 59
def prefixEnd_7594615 : Nat := 4983230072969 + 3 ^ 40 * 7594615 * 2
def baseEnd_7594615 : Nat := 1299895960281969589195169

theorem tailTrace_7594615 : CollatzResearch.WordTrace tailWord_7594615 prefixEnd_7594615 1299895960281969589195169 := by
  unfold tailWord_7594615
  simp only [CollatzResearch.WordTrace]
  refine ⟨276998365381014386823129299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184665576920676257882086199 276998365381014386823129299)
  ·
    refine ⟨415497548071521580234693949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276998365381014386823129299 415497548071521580234693949)
    ·
      refine ⟨155811580526820592588010231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415497548071521580234693949 155811580526820592588010231)
      ·
        refine ⟨233717370790230888882015347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155811580526820592588010231 233717370790230888882015347)
        ·
          refine ⟨350576056185346333323023021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233717370790230888882015347 350576056185346333323023021)
          ·
            refine ⟨131466021069504874996133633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350576056185346333323023021 131466021069504874996133633)
            ·
              refine ⟨98599515802128656247100225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131466021069504874996133633 98599515802128656247100225)
              ·
                refine ⟨73949636851596492185325169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98599515802128656247100225 73949636851596492185325169)
                ·
                  refine ⟨55462227638697369138993877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73949636851596492185325169 55462227638697369138993877)
                  ·
                    refine ⟨1299895960281969589195169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55462227638697369138993877 1299895960281969589195169)
                    ·
                      rfl

theorem cell23_7594615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_7594615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594615 prefixEnd_7594615 := by exact prefixLift 7594615
  have htrace : WordTrace (prefixWord ++ tailWord_7594615) baseStart_7594615 baseEnd_7594615 := by
    simpa [prefixWord, tailWord_7594615, baseEnd_7594615] using wordTrace_append hprefix tailTrace_7594615
  have hstable : (prefixWord ++ tailWord_7594615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594615).length < 2 ^ (prefixWord ++ tailWord_7594615).sum := by decide
  have hdescent : baseEnd_7594615 < baseStart_7594615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594629 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 4, 1, 3]
def baseStart_7594629 : Nat := 118140960795 + 7594629 * 2 ^ 59
def prefixEnd_7594629 : Nat := 4983230072969 + 3 ^ 40 * 7594629 * 2
def baseEnd_7594629 : Nat := 3899695069575071712810443

theorem tailTrace_7594629 : CollatzResearch.WordTrace tailWord_7594629 prefixEnd_7594629 3899695069575071712810443 := by
  unfold tailWord_7594629
  simp only [CollatzResearch.WordTrace]
  refine ⟨276998876002963667214138941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184665917335309111476092627 276998876002963667214138941)
  ·
    refine ⟨103874578501111375205302103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276998876002963667214138941 103874578501111375205302103)
    ·
      refine ⟨155811867751667062807953155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103874578501111375205302103 155811867751667062807953155)
      ·
        refine ⟨233717801627500594211929733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155811867751667062807953155 233717801627500594211929733)
        ·
          refine ⟨43822087805156361414736825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233717801627500594211929733 43822087805156361414736825)
          ·
            refine ⟨32866565853867271061052619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43822087805156361414736825 32866565853867271061052619)
            ·
              refine ⟨49299848780800906591578929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32866565853867271061052619 49299848780800906591578929)
              ·
                refine ⟨36974886585600679943684197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49299848780800906591578929 36974886585600679943684197)
                ·
                  refine ⟨6932791234800127489440787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36974886585600679943684197 6932791234800127489440787)
                  ·
                    refine ⟨10399186852200191234161181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6932791234800127489440787 10399186852200191234161181)
                    ·
                      refine ⟨3899695069575071712810443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10399186852200191234161181 3899695069575071712810443)
                      ·
                        rfl

theorem cell23_7594629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_7594629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594629 prefixEnd_7594629 := by exact prefixLift 7594629
  have htrace : WordTrace (prefixWord ++ tailWord_7594629) baseStart_7594629 baseEnd_7594629 := by
    simpa [prefixWord, tailWord_7594629, baseEnd_7594629] using wordTrace_append hprefix tailTrace_7594629
  have hstable : (prefixWord ++ tailWord_7594629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594629).length < 2 ^ (prefixWord ++ tailWord_7594629).sum := by decide
  have hdescent : baseEnd_7594629 < baseStart_7594629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594673 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 3, 3, 2]
def baseStart_7594673 : Nat := 118140960795 + 7594673 * 2 ^ 59
def prefixEnd_7594673 : Nat := 4983230072969 + 3 ^ 40 * 7594673 * 2
def baseEnd_7594673 : Nat := 3899717662723869540660241

theorem tailTrace_7594673 : CollatzResearch.WordTrace tailWord_7594673 prefixEnd_7594673 3899717662723869540660241 := by
  unfold tailWord_7594673
  simp only [CollatzResearch.WordTrace]
  refine ⟨277000480814804262728740673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184666987209869508485827115 277000480814804262728740673)
  ·
    refine ⟨207750360611103197046555505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277000480814804262728740673 207750360611103197046555505)
    ·
      refine ⟨155812770458327397784916629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207750360611103197046555505 155812770458327397784916629)
      ·
        refine ⟨7303723615234096771167967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155812770458327397784916629 7303723615234096771167967)
        ·
          refine ⟨10955585422851145156751951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7303723615234096771167967 10955585422851145156751951)
          ·
            refine ⟨16433378134276717735127927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10955585422851145156751951 16433378134276717735127927)
            ·
              refine ⟨24650067201415076602691891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16433378134276717735127927 24650067201415076602691891)
              ·
                refine ⟨36975100802122614904037837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24650067201415076602691891 36975100802122614904037837)
                ·
                  refine ⟨13865662800795980589014189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36975100802122614904037837 13865662800795980589014189)
                  ·
                    refine ⟨5199623550298492720880321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13865662800795980589014189 5199623550298492720880321)
                    ·
                      refine ⟨3899717662723869540660241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5199623550298492720880321 3899717662723869540660241)
                      ·
                        rfl

theorem cell23_7594673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_7594673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594673 prefixEnd_7594673 := by exact prefixLift 7594673
  have htrace : WordTrace (prefixWord ++ tailWord_7594673) baseStart_7594673 baseEnd_7594673 := by
    simpa [prefixWord, tailWord_7594673, baseEnd_7594673] using wordTrace_append hprefix tailTrace_7594673
  have hstable : (prefixWord ++ tailWord_7594673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594673).length < 2 ^ (prefixWord ++ tailWord_7594673).sum := by decide
  have hdescent : baseEnd_7594673 < baseStart_7594673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594686 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_7594686 : Nat := 118140960795 + 7594686 * 2 ^ 59
def prefixEnd_7594686 : Nat := 4983230072969 + 3 ^ 40 * 7594686 * 2
def baseEnd_7594686 : Nat := 3899724337972377989797681

theorem tailTrace_7594686 : CollatzResearch.WordTrace tailWord_7594686 prefixEnd_7594686 3899724337972377989797681 := by
  unfold tailWord_7594686
  simp only [CollatzResearch.WordTrace]
  refine ⟨34625119370469645743620489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184667303309171443965975941 34625119370469645743620489)
  ·
    refine ⟨25968839527852234307715367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34625119370469645743620489 25968839527852234307715367)
    ·
      refine ⟨38953259291778351461573051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25968839527852234307715367 38953259291778351461573051)
      ·
        refine ⟨58429888937667527192359577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38953259291778351461573051 58429888937667527192359577)
        ·
          refine ⟨43822416703250645394269683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58429888937667527192359577 43822416703250645394269683)
          ·
            refine ⟨65733625054875968091404525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43822416703250645394269683 65733625054875968091404525)
            ·
              refine ⟨24650109395578488034276697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65733625054875968091404525 24650109395578488034276697)
              ·
                refine ⟨18487582046683866025707523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24650109395578488034276697 18487582046683866025707523)
                ·
                  refine ⟨27731373070025799038561285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18487582046683866025707523 27731373070025799038561285)
                  ·
                    refine ⟨5199632450629837319730241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27731373070025799038561285 5199632450629837319730241)
                    ·
                      refine ⟨3899724337972377989797681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5199632450629837319730241 3899724337972377989797681)
                      ·
                        rfl

theorem cell23_7594686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_7594686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594686 prefixEnd_7594686 := by exact prefixLift 7594686
  have htrace : WordTrace (prefixWord ++ tailWord_7594686) baseStart_7594686 baseEnd_7594686 := by
    simpa [prefixWord, tailWord_7594686, baseEnd_7594686] using wordTrace_append hprefix tailTrace_7594686
  have hstable : (prefixWord ++ tailWord_7594686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594686).length < 2 ^ (prefixWord ++ tailWord_7594686).sum := by decide
  have hdescent : baseEnd_7594686 < baseStart_7594686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594716 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7594716 : Nat := 118140960795 + 7594716 * 2 ^ 59
def prefixEnd_7594716 : Nat := 4983230072969 + 3 ^ 40 * 7594716 * 2
def baseEnd_7594716 : Nat := 3899739742392012872422543

theorem tailTrace_7594716 : CollatzResearch.WordTrace tailWord_7594716 prefixEnd_7594716 3899739742392012872422543 := by
  unfold tailWord_7594716
  simp only [CollatzResearch.WordTrace]
  refine ⟨138501024576824240536278001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184668032769098987381704001 138501024576824240536278001)
  ·
    refine ⟨103875768432618180402208501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138501024576824240536278001 103875768432618180402208501)
    ·
      refine ⟨9738353290557954412707047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103875768432618180402208501 9738353290557954412707047)
      ·
        refine ⟨14607529935836931619060571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9738353290557954412707047 14607529935836931619060571)
        ·
          refine ⟨21911294903755397428590857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14607529935836931619060571 21911294903755397428590857)
          ·
            refine ⟨16433471177816548071443143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21911294903755397428590857 16433471177816548071443143)
            ·
              refine ⟨24650206766724822107164715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16433471177816548071443143 24650206766724822107164715)
              ·
                refine ⟨36975310150087233160747073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24650206766724822107164715 36975310150087233160747073)
                ·
                  refine ⟨27731482612565424870560305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36975310150087233160747073 27731482612565424870560305)
                  ·
                    refine ⟨20798611959424068652920229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27731482612565424870560305 20798611959424068652920229)
                    ·
                      refine ⟨3899739742392012872422543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20798611959424068652920229 3899739742392012872422543)
                      ·
                        rfl

theorem cell23_7594716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7594716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594716 prefixEnd_7594716 := by exact prefixLift 7594716
  have htrace : WordTrace (prefixWord ++ tailWord_7594716) baseStart_7594716 baseEnd_7594716 := by
    simpa [prefixWord, tailWord_7594716, baseEnd_7594716] using wordTrace_append hprefix tailTrace_7594716
  have hstable : (prefixWord ++ tailWord_7594716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594716).length < 2 ^ (prefixWord ++ tailWord_7594716).sum := by decide
  have hdescent : baseEnd_7594716 < baseStart_7594716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594719 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 3]
def baseStart_7594719 : Nat := 118140960795 + 7594719 * 2 ^ 59
def prefixEnd_7594719 : Nat := 4983230072969 + 3 ^ 40 * 7594719 * 2
def baseEnd_7594719 : Nat := 3899741282833976360685029

theorem tailTrace_7594719 : CollatzResearch.WordTrace tailWord_7594719 prefixEnd_7594719 3899741282833976360685029 := by
  unfold tailWord_7594719
  simp only [CollatzResearch.WordTrace]
  refine ⟨277002158572637612584915211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184668105715091741723276807 277002158572637612584915211)
  ·
    refine ⟨415503237858956418877372817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277002158572637612584915211 415503237858956418877372817)
    ·
      refine ⟨311627428394217314158029613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415503237858956418877372817 311627428394217314158029613)
      ·
        refine ⟨116860285647831492809261105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311627428394217314158029613 116860285647831492809261105)
        ·
          refine ⟨87645214235873619606945829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116860285647831492809261105 87645214235873619606945829)
          ·
            refine ⟨16433477669226303676302343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87645214235873619606945829 16433477669226303676302343)
            ·
              refine ⟨24650216503839455514453515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16433477669226303676302343 24650216503839455514453515)
              ·
                refine ⟨36975324755759183271680273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24650216503839455514453515 36975324755759183271680273)
                ·
                  refine ⟨27731493566819387453760205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36975324755759183271680273 27731493566819387453760205)
                  ·
                    refine ⟨10399310087557270295160077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27731493566819387453760205 10399310087557270295160077)
                    ·
                      refine ⟨3899741282833976360685029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10399310087557270295160077 3899741282833976360685029)
                      ·
                        rfl

theorem cell23_7594719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_7594719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594719 prefixEnd_7594719 := by exact prefixLift 7594719
  have htrace : WordTrace (prefixWord ++ tailWord_7594719) baseStart_7594719 baseEnd_7594719 := by
    simpa [prefixWord, tailWord_7594719, baseEnd_7594719] using wordTrace_append hprefix tailTrace_7594719
  have hstable : (prefixWord ++ tailWord_7594719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594719).length < 2 ^ (prefixWord ++ tailWord_7594719).sum := by decide
  have hdescent : baseEnd_7594719 < baseStart_7594719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594741 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7594741 : Nat := 118140960795 + 7594741 * 2 ^ 59
def prefixEnd_7594741 : Nat := 4983230072969 + 3 ^ 40 * 7594741 * 2
def baseEnd_7594741 : Nat := 3899752579408375274609929

theorem tailTrace_7594741 : CollatzResearch.WordTrace tailWord_7594741 prefixEnd_7594741 3899752579408375274609929 := by
  unfold tailWord_7594741
  simp only [CollatzResearch.WordTrace]
  refine ⟨277002960978557910342216077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184668640652371940228144051 277002960978557910342216077)
  ·
    refine ⟨103876110366959216378331029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277002960978557910342216077 103876110366959216378331029)
    ·
      refine ⟨4869192673451213267734267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103876110366959216378331029 4869192673451213267734267)
      ·
        refine ⟨7303789010176819901601401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4869192673451213267734267 7303789010176819901601401)
        ·
          refine ⟨5477841757632614926201051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7303789010176819901601401 5477841757632614926201051)
          ·
            refine ⟨8216762636448922389301577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5477841757632614926201051 8216762636448922389301577)
            ·
              refine ⟨6162571977336691791976183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8216762636448922389301577 6162571977336691791976183)
              ·
                refine ⟨9243857966005037687964275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6162571977336691791976183 9243857966005037687964275)
                ·
                  refine ⟨13865786949007556531946413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9243857966005037687964275 13865786949007556531946413)
                  ·
                    refine ⟨5199670105877833699479905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13865786949007556531946413 5199670105877833699479905)
                    ·
                      refine ⟨3899752579408375274609929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5199670105877833699479905 3899752579408375274609929)
                      ·
                        rfl

theorem cell23_7594741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7594741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594741 prefixEnd_7594741 := by exact prefixLift 7594741
  have htrace : WordTrace (prefixWord ++ tailWord_7594741) baseStart_7594741 baseEnd_7594741 := by
    simpa [prefixWord, tailWord_7594741, baseEnd_7594741] using wordTrace_append hprefix tailTrace_7594741
  have hstable : (prefixWord ++ tailWord_7594741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594741).length < 2 ^ (prefixWord ++ tailWord_7594741).sum := by decide
  have hdescent : baseEnd_7594741 < baseStart_7594741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594769 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 3, 4]
def baseStart_7594769 : Nat := 118140960795 + 7594769 * 2 ^ 59
def prefixEnd_7594769 : Nat := 4983230072969 + 3 ^ 40 * 7594769 * 2
def baseEnd_7594769 : Nat := 1299922318955567055019933

theorem tailTrace_7594769 : CollatzResearch.WordTrace tailWord_7594769 prefixEnd_7594769 1299922318955567055019933 := by
  unfold tailWord_7594769
  simp only [CollatzResearch.WordTrace]
  refine ⟨277003982222456471124235361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184669321481637647416156907 277003982222456471124235361)
  ·
    refine ⟨207752986666842353343176521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277003982222456471124235361 207752986666842353343176521)
    ·
      refine ⟨155814740000131765007382391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207752986666842353343176521 155814740000131765007382391)
      ·
        refine ⟨233722110000197647511073587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155814740000131765007382391 233722110000197647511073587)
        ·
          refine ⟨350583165000296471266610381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233722110000197647511073587 350583165000296471266610381)
          ·
            refine ⟨131468686875111176724978893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350583165000296471266610381 131468686875111176724978893)
            ·
              refine ⟨49300757578166691271867085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131468686875111176724978893 49300757578166691271867085)
              ·
                refine ⟨18487784091812509226950157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49300757578166691271867085 18487784091812509226950157)
                ·
                  refine ⟨6932919034429690960106309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18487784091812509226950157 6932919034429690960106309)
                  ·
                    refine ⟨1299922318955567055019933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6932919034429690960106309 1299922318955567055019933)
                    ·
                      rfl

theorem cell23_7594769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_7594769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594769 prefixEnd_7594769 := by exact prefixLift 7594769
  have htrace : WordTrace (prefixWord ++ tailWord_7594769) baseStart_7594769 baseEnd_7594769 := by
    simpa [prefixWord, tailWord_7594769, baseEnd_7594769] using wordTrace_append hprefix tailTrace_7594769
  have hstable : (prefixWord ++ tailWord_7594769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594769).length < 2 ^ (prefixWord ++ tailWord_7594769).sum := by decide
  have hdescent : baseEnd_7594769 < baseStart_7594769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594786 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_7594786 : Nat := 118140960795 + 7594786 * 2 ^ 59
def prefixEnd_7594786 : Nat := 4983230072969 + 3 ^ 40 * 7594786 * 2
def baseEnd_7594786 : Nat := 1299925228679275866182407

theorem tailTrace_7594786 : CollatzResearch.WordTrace tailWord_7594786 prefixEnd_7594786 1299925228679275866182407 := by
  unfold tailWord_7594786
  simp only [CollatzResearch.WordTrace]
  refine ⟨69251150565848720756901053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184669734842263255351736141 69251150565848720756901053)
  ·
    refine ⟨25969181462193270283837895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69251150565848720756901053 25969181462193270283837895)
    ·
      refine ⟨38953772193289905425756843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25969181462193270283837895 38953772193289905425756843)
      ·
        refine ⟨58430658289934858138635265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38953772193289905425756843 58430658289934858138635265)
        ·
          refine ⟨43822993717451143603976449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58430658289934858138635265 43822993717451143603976449)
          ·
            refine ⟨32867245288088357702982337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43822993717451143603976449 32867245288088357702982337)
            ·
              refine ⟨24650433966066268277236753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32867245288088357702982337 24650433966066268277236753)
              ·
                refine ⟨18487825474549701207927565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24650433966066268277236753 18487825474549701207927565)
                ·
                  refine ⟨6932934552956137952972837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18487825474549701207927565 6932934552956137952972837)
                  ·
                    refine ⟨1299925228679275866182407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6932934552956137952972837 1299925228679275866182407)
                    ·
                      rfl

theorem cell23_7594786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_7594786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594786 prefixEnd_7594786 := by exact prefixLift 7594786
  have htrace : WordTrace (prefixWord ++ tailWord_7594786) baseStart_7594786 baseEnd_7594786 := by
    simpa [prefixWord, tailWord_7594786, baseEnd_7594786] using wordTrace_append hprefix tailTrace_7594786
  have hstable : (prefixWord ++ tailWord_7594786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594786).length < 2 ^ (prefixWord ++ tailWord_7594786).sum := by decide
  have hdescent : baseEnd_7594786 < baseStart_7594786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594803 : List Nat := [1, 1, 1, 2, 6, 1, 3, 3, 1, 4]
def baseStart_7594803 : Nat := 118140960795 + 7594803 * 2 ^ 59
def prefixEnd_7594803 : Nat := 4983230072969 + 3 ^ 40 * 7594803 * 2
def baseEnd_7594803 : Nat := 1299928138402984677344881

theorem tailTrace_7594803 : CollatzResearch.WordTrace tailWord_7594803 prefixEnd_7594803 1299928138402984677344881 := by
  unfold tailWord_7594803
  simp only [CollatzResearch.WordTrace]
  refine ⟨277005222304333294930973063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184670148202888863287315375 277005222304333294930973063)
  ·
    refine ⟨415507833456499942396459595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277005222304333294930973063 415507833456499942396459595)
    ·
      refine ⟨623261750184749913594689393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415507833456499942396459595 623261750184749913594689393)
      ·
        refine ⟨467446312638562435196017045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623261750184749913594689393 467446312638562435196017045)
        ·
          refine ⟨21911545904932614149813299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 467446312638562435196017045 21911545904932614149813299)
          ·
            refine ⟨32867318857398921224719949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21911545904932614149813299 32867318857398921224719949)
            ·
              refine ⟨12325244571524595459269981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32867318857398921224719949 12325244571524595459269981)
              ·
                refine ⟨4621966714321723297226243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12325244571524595459269981 4621966714321723297226243)
                ·
                  refine ⟨6932950071482584945839365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621966714321723297226243 6932950071482584945839365)
                  ·
                    refine ⟨1299928138402984677344881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6932950071482584945839365 1299928138402984677344881)
                    ·
                      rfl

theorem cell23_7594803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 1, 4].length) (baseStart_7594803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594803 prefixEnd_7594803 := by exact prefixLift 7594803
  have htrace : WordTrace (prefixWord ++ tailWord_7594803) baseStart_7594803 baseEnd_7594803 := by
    simpa [prefixWord, tailWord_7594803, baseEnd_7594803] using wordTrace_append hprefix tailTrace_7594803
  have hstable : (prefixWord ++ tailWord_7594803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594803).length < 2 ^ (prefixWord ++ tailWord_7594803).sum := by decide
  have hdescent : baseEnd_7594803 < baseStart_7594803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594813 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_7594813 : Nat := 118140960795 + 7594813 * 2 ^ 59
def prefixEnd_7594813 : Nat := 4983230072969 + 3 ^ 40 * 7594813 * 2
def baseEnd_7594813 : Nat := 3899789550015498992909597

theorem tailTrace_7594813 : CollatzResearch.WordTrace tailWord_7594813 prefixEnd_7594813 3899789550015498992909597 := by
  unfold tailWord_7594813
  simp only [CollatzResearch.WordTrace]
  refine ⟨277005587034297066638837093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184670391356198044425891395 277005587034297066638837093)
  ·
    refine ⟨51938547568930699994781955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277005587034297066638837093 51938547568930699994781955)
    ·
      refine ⟨77907821353396049992172933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51938547568930699994781955 77907821353396049992172933)
      ·
        refine ⟨14607716503761759373532425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77907821353396049992172933 14607716503761759373532425)
        ·
          refine ⟨10955787377821319530149319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14607716503761759373532425 10955787377821319530149319)
          ·
            refine ⟨16433681066731979295223979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10955787377821319530149319 16433681066731979295223979)
            ·
              refine ⟨24650521600097968942835969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16433681066731979295223979 24650521600097968942835969)
              ·
                refine ⟨18487891200073476707126977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24650521600097968942835969 18487891200073476707126977)
                ·
                  refine ⟨13865918400055107530345233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18487891200073476707126977 13865918400055107530345233)
                  ·
                    refine ⟨10399438800041330647758925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13865918400055107530345233 10399438800041330647758925)
                    ·
                      refine ⟨3899789550015498992909597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10399438800041330647758925 3899789550015498992909597)
                      ·
                        rfl

theorem cell23_7594813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_7594813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594813 prefixEnd_7594813 := by exact prefixLift 7594813
  have htrace : WordTrace (prefixWord ++ tailWord_7594813) baseStart_7594813 baseEnd_7594813 := by
    simpa [prefixWord, tailWord_7594813, baseEnd_7594813] using wordTrace_append hprefix tailTrace_7594813
  have hstable : (prefixWord ++ tailWord_7594813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594813).length < 2 ^ (prefixWord ++ tailWord_7594813).sum := by decide
  have hdescent : baseEnd_7594813 < baseStart_7594813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594826 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_7594826 : Nat := 118140960795 + 7594826 * 2 ^ 59
def prefixEnd_7594826 : Nat := 4983230072969 + 3 ^ 40 * 7594826 * 2
def baseEnd_7594826 : Nat := 3899796225264007442047037

theorem tailTrace_7594826 : CollatzResearch.WordTrace tailWord_7594826 prefixEnd_7594826 3899796225264007442047037 := by
  unfold tailWord_7594826
  simp only [CollatzResearch.WordTrace]
  refine ⟨69251515295812492464765083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184670707455499979906040221 69251515295812492464765083)
  ·
    refine ⟨103877272943718738697147625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69251515295812492464765083 103877272943718738697147625)
    ·
      refine ⟨77907954707789054022860719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103877272943718738697147625 77907954707789054022860719)
      ·
        refine ⟨116861932061683581034291079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77907954707789054022860719 116861932061683581034291079)
        ·
          refine ⟨175292898092525371551436619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116861932061683581034291079 175292898092525371551436619)
          ·
            refine ⟨262939347138788057327154929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175292898092525371551436619 262939347138788057327154929)
            ·
              refine ⟨197204510354091042995366197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262939347138788057327154929 197204510354091042995366197)
              ·
                refine ⟨18487922845696035280815581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197204510354091042995366197 18487922845696035280815581)
                ·
                  refine ⟨6932971067136013230305843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18487922845696035280815581 6932971067136013230305843)
                  ·
                    refine ⟨10399456600704019845458765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6932971067136013230305843 10399456600704019845458765)
                    ·
                      refine ⟨3899796225264007442047037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10399456600704019845458765 3899796225264007442047037)
                      ·
                        rfl

theorem cell23_7594826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_7594826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594826 prefixEnd_7594826 := by exact prefixLift 7594826
  have htrace : WordTrace (prefixWord ++ tailWord_7594826) baseStart_7594826 baseEnd_7594826 := by
    simpa [prefixWord, tailWord_7594826, baseEnd_7594826] using wordTrace_append hprefix tailTrace_7594826
  have hstable : (prefixWord ++ tailWord_7594826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594826).length < 2 ^ (prefixWord ++ tailWord_7594826).sum := by decide
  have hdescent : baseEnd_7594826 < baseStart_7594826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594833 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 6]
def baseStart_7594833 : Nat := 118140960795 + 7594833 * 2 ^ 59
def prefixEnd_7594833 : Nat := 4983230072969 + 3 ^ 40 * 7594833 * 2
def baseEnd_7594833 : Nat := 433311091069843212739945

theorem tailTrace_7594833 : CollatzResearch.WordTrace tailWord_7594833 prefixEnd_7594833 433311091069843212739945 := by
  unfold tailWord_7594833
  simp only [CollatzResearch.WordTrace]
  refine ⟨277006316494224610054565153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184670877662816406703043435 277006316494224610054565153)
  ·
    refine ⟨207754737370668457540923865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277006316494224610054565153 207754737370668457540923865)
    ·
      refine ⟨155816053028001343155692899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207754737370668457540923865 155816053028001343155692899)
      ·
        refine ⟨233724079542002014733539349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155816053028001343155692899 233724079542002014733539349)
        ·
          refine ⟨10955816228531344440634657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 233724079542002014733539349 10955816228531344440634657)
          ·
            refine ⟨8216862171398508330475993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10955816228531344440634657 8216862171398508330475993)
            ·
              refine ⟨6162646628548881247856995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8216862171398508330475993 6162646628548881247856995)
              ·
                refine ⟨9243969942823321871785493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6162646628548881247856995 9243969942823321871785493)
                ·
                  refine ⟨433311091069843212739945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9243969942823321871785493 433311091069843212739945)
                  ·
                    rfl

theorem cell23_7594833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 6].length) (baseStart_7594833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594833 prefixEnd_7594833 := by exact prefixLift 7594833
  have htrace : WordTrace (prefixWord ++ tailWord_7594833) baseStart_7594833 baseEnd_7594833 := by
    simpa [prefixWord, tailWord_7594833, baseEnd_7594833] using wordTrace_append hprefix tailTrace_7594833
  have hstable : (prefixWord ++ tailWord_7594833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594833).length < 2 ^ (prefixWord ++ tailWord_7594833).sum := by decide
  have hdescent : baseEnd_7594833 < baseStart_7594833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594859 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 6, 4]
def baseStart_7594859 : Nat := 118140960795 + 7594859 * 2 ^ 59
def prefixEnd_7594859 : Nat := 4983230072969 + 3 ^ 40 * 7594859 * 2
def baseEnd_7594859 : Nat := 1299937723375201937644795

theorem tailTrace_7594859 : CollatzResearch.WordTrace tailWord_7594859 prefixEnd_7594859 1299937723375201937644795 := by
  unfold tailWord_7594859
  simp only [CollatzResearch.WordTrace]
  refine ⟨277007264792130416495011631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184671509861420277663341087 277007264792130416495011631)
  ·
    refine ⟨415510897188195624742517447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277007264792130416495011631 415510897188195624742517447)
    ·
      refine ⟨623266345782293437113776171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415510897188195624742517447 623266345782293437113776171)
      ·
        refine ⟨934899518673440155670664257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623266345782293437113776171 934899518673440155670664257)
        ·
          refine ⟨701174639005080116752998193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934899518673440155670664257 701174639005080116752998193)
          ·
            refine ⟨525880979253810087564748645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701174639005080116752998193 525880979253810087564748645)
            ·
              refine ⟨98602683610089391418390371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 525880979253810087564748645 98602683610089391418390371)
              ·
                refine ⟨147904025415134087127585557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98602683610089391418390371 147904025415134087127585557)
                ·
                  refine ⟨6933001191334410334105573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147904025415134087127585557 6933001191334410334105573)
                  ·
                    refine ⟨1299937723375201937644795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6933001191334410334105573 1299937723375201937644795)
                    ·
                      rfl

theorem cell23_7594859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 4].length) (baseStart_7594859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594859 prefixEnd_7594859 := by exact prefixLift 7594859
  have htrace : WordTrace (prefixWord ++ tailWord_7594859) baseStart_7594859 baseEnd_7594859 := by
    simpa [prefixWord, tailWord_7594859, baseEnd_7594859] using wordTrace_append hprefix tailTrace_7594859
  have hstable : (prefixWord ++ tailWord_7594859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594859).length < 2 ^ (prefixWord ++ tailWord_7594859).sum := by decide
  have hdescent : baseEnd_7594859 < baseStart_7594859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594866 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_7594866 : Nat := 118140960795 + 7594866 * 2 ^ 59
def prefixEnd_7594866 : Nat := 4983230072969 + 3 ^ 40 * 7594866 * 2
def baseEnd_7594866 : Nat := 3899816764490187285546853

theorem tailTrace_7594866 : CollatzResearch.WordTrace tailWord_7594866 prefixEnd_7594866 3899816764490187285546853 := by
  unfold tailWord_7594866
  simp only [CollatzResearch.WordTrace]
  refine ⟨69251880025776264172629113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184671680068736704460344301 69251880025776264172629113)
  ·
    refine ⟨51938910019332198129471835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69251880025776264172629113 51938910019332198129471835)
    ·
      refine ⟨77908365028998297194207753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51938910019332198129471835 77908365028998297194207753)
      ·
        refine ⟨58431273771748722895655815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77908365028998297194207753 58431273771748722895655815)
        ·
          refine ⟨87646910657623084343483723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58431273771748722895655815 87646910657623084343483723)
          ·
            refine ⟨131470365986434626515225585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87646910657623084343483723 131470365986434626515225585)
            ·
              refine ⟨98602774489825969886419189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131470365986434626515225585 98602774489825969886419189)
              ·
                refine ⟨9244010108421184676851799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98602774489825969886419189 9244010108421184676851799)
                ·
                  refine ⟨13866015162631777015277699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9244010108421184676851799 13866015162631777015277699)
                  ·
                    refine ⟨20799022743947665522916549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13866015162631777015277699 20799022743947665522916549)
                    ·
                      refine ⟨3899816764490187285546853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20799022743947665522916549 3899816764490187285546853)
                      ·
                        rfl

theorem cell23_7594866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_7594866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594866 prefixEnd_7594866 := by exact prefixLift 7594866
  have htrace : WordTrace (prefixWord ++ tailWord_7594866) baseStart_7594866 baseEnd_7594866 := by
    simpa [prefixWord, tailWord_7594866, baseEnd_7594866] using wordTrace_append hprefix tailTrace_7594866
  have hstable : (prefixWord ++ tailWord_7594866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594866).length < 2 ^ (prefixWord ++ tailWord_7594866).sum := by decide
  have hdescent : baseEnd_7594866 < baseStart_7594866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594870 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7594870 : Nat := 118140960795 + 7594870 * 2 ^ 59
def prefixEnd_7594870 : Nat := 4983230072969 + 3 ^ 40 * 7594870 * 2
def baseEnd_7594870 : Nat := 3899818818412805269896835

theorem tailTrace_7594870 : CollatzResearch.WordTrace tailWord_7594870 prefixEnd_7594870 3899818818412805269896835 := by
  unfold tailWord_7594870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17312979124693160335853879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184671777330060376915774709 17312979124693160335853879)
  ·
    refine ⟨25969468687039740503780819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17312979124693160335853879 25969468687039740503780819)
    ·
      refine ⟨38954203030559610755671229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25969468687039740503780819 38954203030559610755671229)
      ·
        refine ⟨14607826136459854033376711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38954203030559610755671229 14607826136459854033376711)
        ·
          refine ⟨21911739204689781050065067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14607826136459854033376711 21911739204689781050065067)
          ·
            refine ⟨32867608807034671575097601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21911739204689781050065067 32867608807034671575097601)
            ·
              refine ⟨24650706605276003681323201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32867608807034671575097601 24650706605276003681323201)
              ·
                refine ⟨18488029953957002760992401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24650706605276003681323201 18488029953957002760992401)
                ·
                  refine ⟨13866022465467752070744301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18488029953957002760992401 13866022465467752070744301)
                  ·
                    refine ⟨5199758424550407026529113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13866022465467752070744301 5199758424550407026529113)
                    ·
                      refine ⟨3899818818412805269896835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5199758424550407026529113 3899818818412805269896835)
                      ·
                        rfl

theorem cell23_7594870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7594870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594870 prefixEnd_7594870 := by exact prefixLift 7594870
  have htrace : WordTrace (prefixWord ++ tailWord_7594870) baseStart_7594870 baseEnd_7594870 := by
    simpa [prefixWord, tailWord_7594870, baseEnd_7594870] using wordTrace_append hprefix tailTrace_7594870
  have hstable : (prefixWord ++ tailWord_7594870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594870).length < 2 ^ (prefixWord ++ tailWord_7594870).sum := by decide
  have hdescent : baseEnd_7594870 < baseStart_7594870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594883 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 3, 2, 2]
def baseStart_7594883 : Nat := 118140960795 + 7594883 * 2 ^ 59
def prefixEnd_7594883 : Nat := 4983230072969 + 3 ^ 40 * 7594883 * 2
def baseEnd_7594883 : Nat := 3899825493661313719034275

theorem tailTrace_7594883 : CollatzResearch.WordTrace tailWord_7594883 prefixEnd_7594883 3899825493661313719034275 := by
  unfold tailWord_7594883
  simp only [CollatzResearch.WordTrace]
  refine ⟨277008140144043468593885303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184672093429362312395923535 277008140144043468593885303)
  ·
    refine ⟨415512210216065202890827955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277008140144043468593885303 415512210216065202890827955)
    ·
      refine ⟨623268315324097804336241933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415512210216065202890827955 623268315324097804336241933)
      ·
        refine ⟨233725618246536676626090725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 623268315324097804336241933 233725618246536676626090725)
        ·
          refine ⟨43823553421225626867392011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233725618246536676626090725 43823553421225626867392011)
          ·
            refine ⟨65735330131838440301088017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43823553421225626867392011 65735330131838440301088017)
            ·
              refine ⟨49301497598878830225816013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65735330131838440301088017 49301497598878830225816013)
              ·
                refine ⟨18488061599579561334681005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49301497598878830225816013 18488061599579561334681005)
                ·
                  refine ⟨6933023099842335500505377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18488061599579561334681005 6933023099842335500505377)
                  ·
                    refine ⟨5199767324881751625379033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6933023099842335500505377 5199767324881751625379033)
                    ·
                      refine ⟨3899825493661313719034275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5199767324881751625379033 3899825493661313719034275)
                      ·
                        rfl

theorem cell23_7594883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 2, 2].length) (baseStart_7594883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594883 prefixEnd_7594883 := by exact prefixLift 7594883
  have htrace : WordTrace (prefixWord ++ tailWord_7594883) baseStart_7594883 baseEnd_7594883 := by
    simpa [prefixWord, tailWord_7594883, baseEnd_7594883] using wordTrace_append hprefix tailTrace_7594883
  have hstable : (prefixWord ++ tailWord_7594883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594883).length < 2 ^ (prefixWord ++ tailWord_7594883).sum := by decide
  have hdescent : baseEnd_7594883 < baseStart_7594883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594889 : List Nat := [1, 2, 1, 1, 5, 2, 3, 8]
def baseStart_7594889 : Nat := 118140960795 + 7594889 * 2 ^ 59
def prefixEnd_7594889 : Nat := 4983230072969 + 3 ^ 40 * 7594889 * 2
def baseEnd_7594889 : Nat := 144438095353527433168861

theorem tailTrace_7594889 : CollatzResearch.WordTrace tailWord_7594889 prefixEnd_7594889 144438095353527433168861 := by
  unfold tailWord_7594889
  simp only [CollatzResearch.WordTrace]
  refine ⟨277008358982021731618603721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184672239321347821079069147 277008358982021731618603721)
  ·
    refine ⟨207756269236516298713952791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277008358982021731618603721 207756269236516298713952791)
    ·
      refine ⟨311634403854774448070929187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207756269236516298713952791 311634403854774448070929187)
      ·
        refine ⟨467451605782161672106393781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311634403854774448070929187 467451605782161672106393781)
        ·
          refine ⟨43823588042077656759974417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 467451605782161672106393781 43823588042077656759974417)
          ·
            refine ⟨32867691031558242569980813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43823588042077656759974417 32867691031558242569980813)
            ·
              refine ⟨12325384136834340963742805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32867691031558242569980813 12325384136834340963742805)
              ·
                refine ⟨144438095353527433168861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12325384136834340963742805 144438095353527433168861)
                ·
                  rfl

theorem cell23_7594889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 8].length) (baseStart_7594889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594889 prefixEnd_7594889 := by exact prefixLift 7594889
  have htrace : WordTrace (prefixWord ++ tailWord_7594889) baseStart_7594889 baseEnd_7594889 := by
    simpa [prefixWord, tailWord_7594889, baseEnd_7594889] using wordTrace_append hprefix tailTrace_7594889
  have hstable : (prefixWord ++ tailWord_7594889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594889).length < 2 ^ (prefixWord ++ tailWord_7594889).sum := by decide
  have hdescent : baseEnd_7594889 < baseStart_7594889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
