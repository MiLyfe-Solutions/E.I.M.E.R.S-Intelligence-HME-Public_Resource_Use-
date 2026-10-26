import V185TrunkScan23Chunk0493

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2922834 : List Nat := [3, 2, 2, 1, 1, 1, 6, 7]
def baseStart_2922834 : Nat := 118140960795 + 2922834 * 2 ^ 59
def prefixEnd_2922834 : Nat := 4983230072969 + 3 ^ 40 * 2922834 * 2
def baseEnd_2922834 : Nat := 55585878344574912304931

theorem tailTrace_2922834 : CollatzResearch.WordTrace tailWord_2922834 prefixEnd_2922834 55585878344574912304931 := by
  unfold tailWord_2922834
  simp only [CollatzResearch.WordTrace]
  refine ⟨26651128473269768287633889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71069675928719382100357037 26651128473269768287633889)
  ·
    refine ⟨19988346354952326215725417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26651128473269768287633889 19988346354952326215725417)
    ·
      refine ⟨14991259766214244661794063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19988346354952326215725417 14991259766214244661794063)
      ·
        refine ⟨22486889649321366992691095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14991259766214244661794063 22486889649321366992691095)
        ·
          refine ⟨33730334473982050489036643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22486889649321366992691095 33730334473982050489036643)
          ·
            refine ⟨50595501710973075733554965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33730334473982050489036643 50595501710973075733554965)
            ·
              refine ⟨2371664142701862925010389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50595501710973075733554965 2371664142701862925010389)
              ·
                refine ⟨55585878344574912304931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2371664142701862925010389 55585878344574912304931)
                ·
                  rfl

theorem cell23_2922834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 7].length) (baseStart_2922834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922834 prefixEnd_2922834 := by exact prefixLift 2922834
  have htrace : WordTrace (prefixWord ++ tailWord_2922834) baseStart_2922834 baseEnd_2922834 := by
    simpa [prefixWord, tailWord_2922834, baseEnd_2922834] using wordTrace_append hprefix tailTrace_2922834
  have hstable : (prefixWord ++ tailWord_2922834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922834).length < 2 ^ (prefixWord ++ tailWord_2922834).sum := by decide
  have hdescent : baseEnd_2922834 < baseStart_2922834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922857 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_2922857 : Nat := 118140960795 + 2922857 * 2 ^ 59
def prefixEnd_2922857 : Nat := 4983230072969 + 3 ^ 40 * 2922857 * 2
def baseEnd_2922857 : Nat := 1500830525358576042245531

theorem tailTrace_2922857 : CollatzResearch.WordTrace tailWord_2922857 prefixEnd_2922857 1500830525358576042245531 := by
  unfold tailWord_2922857
  simp only [CollatzResearch.WordTrace]
  refine ⟨106605352771995748078622825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71070235181330498719081883 106605352771995748078622825)
  ·
    refine ⟨79954014578996811058967119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106605352771995748078622825 79954014578996811058967119)
    ·
      refine ⟨119931021868495216588450679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79954014578996811058967119 119931021868495216588450679)
      ·
        refine ⟨179896532802742824882676019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119931021868495216588450679 179896532802742824882676019)
        ·
          refine ⟨269844799204114237324014029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179896532802742824882676019 269844799204114237324014029)
          ·
            refine ⟨101191799701542838996505261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269844799204114237324014029 101191799701542838996505261)
            ·
              refine ⟨37946924888078564623689473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101191799701542838996505261 37946924888078564623689473)
              ·
                refine ⟨28460193666058923467767105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37946924888078564623689473 28460193666058923467767105)
                ·
                  refine ⟨21345145249544192600825329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28460193666058923467767105 21345145249544192600825329)
                  ·
                    refine ⟨16008858937158144450618997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21345145249544192600825329 16008858937158144450618997)
                    ·
                      refine ⟨1500830525358576042245531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16008858937158144450618997 1500830525358576042245531)
                      ·
                        rfl

theorem cell23_2922857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_2922857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922857 prefixEnd_2922857 := by exact prefixLift 2922857
  have htrace : WordTrace (prefixWord ++ tailWord_2922857) baseStart_2922857 baseEnd_2922857 := by
    simpa [prefixWord, tailWord_2922857, baseEnd_2922857] using wordTrace_append hprefix tailTrace_2922857
  have hstable : (prefixWord ++ tailWord_2922857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922857).length < 2 ^ (prefixWord ++ tailWord_2922857).sum := by decide
  have hdescent : baseEnd_2922857 < baseStart_2922857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922861 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_2922861 : Nat := 118140960795 + 2922861 * 2 ^ 59
def prefixEnd_2922861 : Nat := 4983230072969 + 3 ^ 40 * 2922861 * 2
def baseEnd_2922861 : Nat := 1500832579281194026595513

theorem tailTrace_2922861 : CollatzResearch.WordTrace tailWord_2922861 prefixEnd_2922861 1500832579281194026595513 := by
  unfold tailWord_2922861
  simp only [CollatzResearch.WordTrace]
  refine ⟨106605498663981256761768437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71070332442654171174512291 106605498663981256761768437)
  ·
    refine ⟨9994265499748242821415791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106605498663981256761768437 9994265499748242821415791)
    ·
      refine ⟨14991398249622364232123687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9994265499748242821415791 14991398249622364232123687)
      ·
        refine ⟨22487097374433546348185531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14991398249622364232123687 22487097374433546348185531)
        ·
          refine ⟨33730646061650319522278297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22487097374433546348185531 33730646061650319522278297)
          ·
            refine ⟨25297984546237739641708723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33730646061650319522278297 25297984546237739641708723)
            ·
              refine ⟨37946976819356609462563085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25297984546237739641708723 37946976819356609462563085)
              ·
                refine ⟨14230116307258728548461157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37946976819356609462563085 14230116307258728548461157)
                ·
                  refine ⟨2668146807611011602836467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14230116307258728548461157 2668146807611011602836467)
                  ·
                    refine ⟨4002220211416517404254701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2668146807611011602836467 4002220211416517404254701)
                    ·
                      refine ⟨1500832579281194026595513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4002220211416517404254701 1500832579281194026595513)
                      ·
                        rfl

theorem cell23_2922861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_2922861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922861 prefixEnd_2922861 := by exact prefixLift 2922861
  have htrace : WordTrace (prefixWord ++ tailWord_2922861) baseStart_2922861 baseEnd_2922861 := by
    simpa [prefixWord, tailWord_2922861, baseEnd_2922861] using wordTrace_append hprefix tailTrace_2922861
  have hstable : (prefixWord ++ tailWord_2922861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922861).length < 2 ^ (prefixWord ++ tailWord_2922861).sum := by decide
  have hdescent : baseEnd_2922861 < baseStart_2922861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922867 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 4]
def baseStart_2922867 : Nat := 118140960795 + 2922867 * 2 ^ 59
def prefixEnd_2922867 : Nat := 4983230072969 + 3 ^ 40 * 2922867 * 2
def baseEnd_2922867 : Nat := 1500835660165121003120485

theorem tailTrace_2922867 : CollatzResearch.WordTrace tailWord_2922867 prefixEnd_2922867 1500835660165121003120485 := by
  unfold tailWord_2922867
  simp only [CollatzResearch.WordTrace]
  refine ⟨106605717501959519786486855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71070478334639679857657903 106605717501959519786486855)
  ·
    refine ⟨159908576252939279679730283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106605717501959519786486855 159908576252939279679730283)
    ·
      refine ⟨239862864379408919519595425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159908576252939279679730283 239862864379408919519595425)
      ·
        refine ⟨179897148284556689639696569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239862864379408919519595425 179897148284556689639696569)
        ·
          refine ⟨134922861213417517229772427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179897148284556689639696569 134922861213417517229772427)
          ·
            refine ⟨202384291820126275844658641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134922861213417517229772427 202384291820126275844658641)
            ·
              refine ⟨151788218865094706883493981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202384291820126275844658641 151788218865094706883493981)
              ·
                refine ⟨56920582074410515081310243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151788218865094706883493981 56920582074410515081310243)
                ·
                  refine ⟨85380873111615772621965365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56920582074410515081310243 85380873111615772621965365)
                  ·
                    refine ⟨8004456854213978683309253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85380873111615772621965365 8004456854213978683309253)
                    ·
                      refine ⟨1500835660165121003120485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8004456854213978683309253 1500835660165121003120485)
                      ·
                        rfl

theorem cell23_2922867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_2922867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922867 prefixEnd_2922867 := by exact prefixLift 2922867
  have htrace : WordTrace (prefixWord ++ tailWord_2922867) baseStart_2922867 baseEnd_2922867 := by
    simpa [prefixWord, tailWord_2922867, baseEnd_2922867] using wordTrace_append hprefix tailTrace_2922867
  have hstable : (prefixWord ++ tailWord_2922867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922867).length < 2 ^ (prefixWord ++ tailWord_2922867).sum := by decide
  have hdescent : baseEnd_2922867 < baseStart_2922867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922882 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2922882 : Nat := 118140960795 + 2922882 * 2 ^ 59
def prefixEnd_2922882 : Nat := 4983230072969 + 3 ^ 40 * 2922882 * 2
def baseEnd_2922882 : Nat := 1500843362374938444432917

theorem tailTrace_2922882 : CollatzResearch.WordTrace tailWord_2922882 prefixEnd_2922882 1500843362374938444432917 := by
  unfold tailWord_2922882
  simp only [CollatzResearch.WordTrace]
  refine ⟨26651566149226294337070725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71070843064603451565521933 26651566149226294337070725)
  ·
    refine ⟨4997168652979930188200761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26651566149226294337070725 4997168652979930188200761)
    ·
      refine ⟨3747876489734947641150571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4997168652979930188200761 3747876489734947641150571)
      ·
        refine ⟨5621814734602421461725857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3747876489734947641150571 5621814734602421461725857)
        ·
          refine ⟨4216361050951816096294393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5621814734602421461725857 4216361050951816096294393)
          ·
            refine ⟨3162270788213862072220795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4216361050951816096294393 3162270788213862072220795)
            ·
              refine ⟨4743406182320793108331193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162270788213862072220795 4743406182320793108331193)
              ·
                refine ⟨3557554636740594831248395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4743406182320793108331193 3557554636740594831248395)
                ·
                  refine ⟨5336331955110892246872593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3557554636740594831248395 5336331955110892246872593)
                  ·
                    refine ⟨4002248966333169185154445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5336331955110892246872593 4002248966333169185154445)
                    ·
                      refine ⟨1500843362374938444432917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4002248966333169185154445 1500843362374938444432917)
                      ·
                        rfl

theorem cell23_2922882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2922882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922882 prefixEnd_2922882 := by exact prefixLift 2922882
  have htrace : WordTrace (prefixWord ++ tailWord_2922882) baseStart_2922882 baseEnd_2922882 := by
    simpa [prefixWord, tailWord_2922882, baseEnd_2922882] using wordTrace_append hprefix tailTrace_2922882
  have hstable : (prefixWord ++ tailWord_2922882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922882).length < 2 ^ (prefixWord ++ tailWord_2922882).sum := by decide
  have hdescent : baseEnd_2922882 < baseStart_2922882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922927 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_2922927 : Nat := 118140960795 + 2922927 * 2 ^ 59
def prefixEnd_2922927 : Nat := 4983230072969 + 3 ^ 40 * 2922927 * 2
def baseEnd_2922927 : Nat := 1500866469004390768370209

theorem tailTrace_2922927 : CollatzResearch.WordTrace tailWord_2922927 prefixEnd_2922927 1500866469004390768370209 := by
  unfold tailWord_2922927
  simp only [CollatzResearch.WordTrace]
  refine ⟨106607905881742150033671035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71071937254494766689114023 106607905881742150033671035)
  ·
    refine ⟨159911858822613225050506553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106607905881742150033671035 159911858822613225050506553)
    ·
      refine ⟨119933894116959918787879915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159911858822613225050506553 119933894116959918787879915)
      ·
        refine ⟨179900841175439878181819873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119933894116959918787879915 179900841175439878181819873)
        ·
          refine ⟨134925630881579908636364905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179900841175439878181819873 134925630881579908636364905)
          ·
            refine ⟨101194223161184931477273679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134925630881579908636364905 101194223161184931477273679)
            ·
              refine ⟨151791334741777397215910519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101194223161184931477273679 151791334741777397215910519)
              ·
                refine ⟨227687002112666095823865779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151791334741777397215910519 227687002112666095823865779)
                ·
                  refine ⟨341530503168999143735798669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227687002112666095823865779 341530503168999143735798669)
                  ·
                    refine ⟨128073938688374678900924501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341530503168999143735798669 128073938688374678900924501)
                    ·
                      refine ⟨1500866469004390768370209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 128073938688374678900924501 1500866469004390768370209)
                      ·
                        rfl

theorem cell23_2922927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_2922927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922927 prefixEnd_2922927 := by exact prefixLift 2922927
  have htrace : WordTrace (prefixWord ++ tailWord_2922927) baseStart_2922927 baseEnd_2922927 := by
    simpa [prefixWord, tailWord_2922927, baseEnd_2922927] using wordTrace_append hprefix tailTrace_2922927
  have hstable : (prefixWord ++ tailWord_2922927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922927).length < 2 ^ (prefixWord ++ tailWord_2922927).sum := by decide
  have hdescent : baseEnd_2922927 < baseStart_2922927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922954 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_2922954 : Nat := 118140960795 + 2922954 * 2 ^ 59
def prefixEnd_2922954 : Nat := 4983230072969 + 3 ^ 40 * 2922954 * 2
def baseEnd_2922954 : Nat := 500293444327354054244195

theorem tailTrace_2922954 : CollatzResearch.WordTrace tailWord_2922954 prefixEnd_2922954 500293444327354054244195 := by
  unfold tailWord_2922954
  simp only [CollatzResearch.WordTrace]
  refine ⟨26652222663161083411225979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71072593768429555763269277 26652222663161083411225979)
  ·
    refine ⟨39978333994741625116838969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26652222663161083411225979 39978333994741625116838969)
    ·
      refine ⟨29983750496056218837629227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39978333994741625116838969 29983750496056218837629227)
      ·
        refine ⟨44975625744084328256443841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29983750496056218837629227 44975625744084328256443841)
        ·
          refine ⟨33731719308063246192332881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44975625744084328256443841 33731719308063246192332881)
          ·
            refine ⟨25298789481047434644249661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33731719308063246192332881 25298789481047434644249661)
            ·
              refine ⟨9487046055392787991593623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25298789481047434644249661 9487046055392787991593623)
              ·
                refine ⟨14230569083089181987390435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9487046055392787991593623 14230569083089181987390435)
                ·
                  refine ⟨21345853624633772981085653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14230569083089181987390435 21345853624633772981085653)
                  ·
                    refine ⟨500293444327354054244195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21345853624633772981085653 500293444327354054244195)
                    ·
                      rfl

theorem cell23_2922954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_2922954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922954 prefixEnd_2922954 := by exact prefixLift 2922954
  have htrace : WordTrace (prefixWord ++ tailWord_2922954) baseStart_2922954 baseEnd_2922954 := by
    simpa [prefixWord, tailWord_2922954, baseEnd_2922954] using wordTrace_append hprefix tailTrace_2922954
  have hstable : (prefixWord ++ tailWord_2922954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922954).length < 2 ^ (prefixWord ++ tailWord_2922954).sum := by decide
  have hdescent : baseEnd_2922954 < baseStart_2922954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923001 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 3, 4]
def baseStart_2923001 : Nat := 118140960795 + 2923001 * 2 ^ 59
def prefixEnd_2923001 : Nat := 4983230072969 + 3 ^ 40 * 2923001 * 2
def baseEnd_2923001 : Nat := 500301488857607826281623

theorem tailTrace_2923001 : CollatzResearch.WordTrace tailWord_2923001 prefixEnd_2923001 500301488857607826281623 := by
  unfold tailWord_2923001
  simp only [CollatzResearch.WordTrace]
  refine ⟨106610604883474060671864857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71073736588982707114576571 106610604883474060671864857)
  ·
    refine ⟨79957953662605545503898643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106610604883474060671864857 79957953662605545503898643)
    ·
      refine ⟨119936930493908318255847965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79957953662605545503898643 119936930493908318255847965)
      ·
        refine ⟨44976348935215619345942987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119936930493908318255847965 44976348935215619345942987)
        ·
          refine ⟨67464523402823429018914481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44976348935215619345942987 67464523402823429018914481)
          ·
            refine ⟨50598392552117571764185861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67464523402823429018914481 50598392552117571764185861)
            ·
              refine ⟨9487198603522044705784849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50598392552117571764185861 9487198603522044705784849)
              ·
                refine ⟨7115398952641533529338637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9487198603522044705784849 7115398952641533529338637)
                ·
                  refine ⟨2668274607240575073501989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7115398952641533529338637 2668274607240575073501989)
                  ·
                    refine ⟨500301488857607826281623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668274607240575073501989 500301488857607826281623)
                    ·
                      rfl

theorem cell23_2923001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 4].length) (baseStart_2923001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923001 prefixEnd_2923001 := by exact prefixLift 2923001
  have htrace : WordTrace (prefixWord ++ tailWord_2923001) baseStart_2923001 baseEnd_2923001 := by
    simpa [prefixWord, tailWord_2923001, baseEnd_2923001] using wordTrace_append hprefix tailTrace_2923001
  have hstable : (prefixWord ++ tailWord_2923001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923001).length < 2 ^ (prefixWord ++ tailWord_2923001).sum := by decide
  have hdescent : baseEnd_2923001 < baseStart_2923001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923004 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2923004 : Nat := 118140960795 + 2923004 * 2 ^ 59
def prefixEnd_2923004 : Nat := 4983230072969 + 3 ^ 40 * 2923004 * 2
def baseEnd_2923004 : Nat := 1500906007014786967107355

theorem tailTrace_2923004 : CollatzResearch.WordTrace tailWord_2923004 prefixEnd_2923004 1500906007014786967107355 := by
  unfold tailWord_2923004
  simp only [CollatzResearch.WordTrace]
  refine ⟨53305357151231596092112033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71073809534975461456149377 53305357151231596092112033)
  ·
    refine ⟨39979017863423697069084025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53305357151231596092112033 39979017863423697069084025)
    ·
      refine ⟨29984263397567772801813019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39979017863423697069084025 29984263397567772801813019)
      ·
        refine ⟨44976395096351659202719529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29984263397567772801813019 44976395096351659202719529)
        ·
          refine ⟨33732296322263744402039647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44976395096351659202719529 33732296322263744402039647)
          ·
            refine ⟨50598444483395616603059471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33732296322263744402039647 50598444483395616603059471)
            ·
              refine ⟨75897666725093424904589207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50598444483395616603059471 75897666725093424904589207)
              ·
                refine ⟨113846500087640137356883811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75897666725093424904589207 113846500087640137356883811)
                ·
                  refine ⟨170769750131460206035325717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113846500087640137356883811 170769750131460206035325717)
                  ·
                    refine ⟨8004832037412197157905893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 170769750131460206035325717 8004832037412197157905893)
                    ·
                      refine ⟨1500906007014786967107355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8004832037412197157905893 1500906007014786967107355)
                      ·
                        rfl

theorem cell23_2923004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2923004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923004 prefixEnd_2923004 := by exact prefixLift 2923004
  have htrace : WordTrace (prefixWord ++ tailWord_2923004) baseStart_2923004 baseEnd_2923004 := by
    simpa [prefixWord, tailWord_2923004, baseEnd_2923004] using wordTrace_append hprefix tailTrace_2923004
  have hstable : (prefixWord ++ tailWord_2923004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923004).length < 2 ^ (prefixWord ++ tailWord_2923004).sum := by decide
  have hdescent : baseEnd_2923004 < baseStart_2923004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923011 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 3]
def baseStart_2923011 : Nat := 118140960795 + 2923011 * 2 ^ 59
def prefixEnd_2923011 : Nat := 4983230072969 + 3 ^ 40 * 2923011 * 2
def baseEnd_2923011 : Nat := 1500909601379368439719823

theorem tailTrace_2923011 : CollatzResearch.WordTrace tailWord_2923011 prefixEnd_2923011 1500909601379368439719823 := by
  unfold tailWord_2923011
  simp only [CollatzResearch.WordTrace]
  refine ⟨106610969613437832379728887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71073979742291888253152591 106610969613437832379728887)
  ·
    refine ⟨159916454420156748569593331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106610969613437832379728887 159916454420156748569593331)
    ·
      refine ⟨239874681630235122854389997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159916454420156748569593331 239874681630235122854389997)
      ·
        refine ⟨89953005611338171070396249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239874681630235122854389997 89953005611338171070396249)
        ·
          refine ⟨67464754208503628302797187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89953005611338171070396249 67464754208503628302797187)
          ·
            refine ⟨101197131312755442454195781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67464754208503628302797187 101197131312755442454195781)
            ·
              refine ⟨18974462121141645460161709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101197131312755442454195781 18974462121141645460161709)
              ·
                refine ⟨7115423295428117047560641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18974462121141645460161709 7115423295428117047560641)
                ·
                  refine ⟨5336567471571087785670481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7115423295428117047560641 5336567471571087785670481)
                  ·
                    refine ⟨4002425603678315839252861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5336567471571087785670481 4002425603678315839252861)
                    ·
                      refine ⟨1500909601379368439719823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4002425603678315839252861 1500909601379368439719823)
                      ·
                        rfl

theorem cell23_2923011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_2923011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923011 prefixEnd_2923011 := by exact prefixLift 2923011
  have htrace : WordTrace (prefixWord ++ tailWord_2923011) baseStart_2923011 baseEnd_2923011 := by
    simpa [prefixWord, tailWord_2923011, baseEnd_2923011] using wordTrace_append hprefix tailTrace_2923011
  have hstable : (prefixWord ++ tailWord_2923011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923011).length < 2 ^ (prefixWord ++ tailWord_2923011).sum := by decide
  have hdescent : baseEnd_2923011 < baseStart_2923011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923034 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_2923034 : Nat := 118140960795 + 2923034 * 2 ^ 59
def prefixEnd_2923034 : Nat := 4983230072969 + 3 ^ 40 * 2923034 * 2
def baseEnd_2923034 : Nat := 1500921411434421849732217

theorem tailTrace_2923034 : CollatzResearch.WordTrace tailWord_2923034 prefixEnd_2923034 1500921411434421849732217 := by
  unfold tailWord_2923034
  simp only [CollatzResearch.WordTrace]
  refine ⟨26652952123088626826954039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71074538994903004871877437 26652952123088626826954039)
  ·
    refine ⟨39979428184632940240431059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26652952123088626826954039 39979428184632940240431059)
    ·
      refine ⟨59969142276949410360646589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39979428184632940240431059 59969142276949410360646589)
      ·
        refine ⟨22488428353856028885242471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59969142276949410360646589 22488428353856028885242471)
        ·
          refine ⟨33732642530784043327863707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22488428353856028885242471 33732642530784043327863707)
          ·
            refine ⟨50598963796176064991795561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33732642530784043327863707 50598963796176064991795561)
            ·
              refine ⟨37949222847132048743846671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50598963796176064991795561 37949222847132048743846671)
              ·
                refine ⟨56923834270698073115770007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37949222847132048743846671 56923834270698073115770007)
                ·
                  refine ⟨85385751406047109673655011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56923834270698073115770007 85385751406047109673655011)
                  ·
                    refine ⟨128078627109070664510482517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85385751406047109673655011 128078627109070664510482517)
                    ·
                      refine ⟨1500921411434421849732217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 128078627109070664510482517 1500921411434421849732217)
                      ·
                        rfl

theorem cell23_2923034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_2923034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923034 prefixEnd_2923034 := by exact prefixLift 2923034
  have htrace : WordTrace (prefixWord ++ tailWord_2923034) baseStart_2923034 baseEnd_2923034 := by
    simpa [prefixWord, tailWord_2923034, baseEnd_2923034] using wordTrace_append hprefix tailTrace_2923034
  have hstable : (prefixWord ++ tailWord_2923034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923034).length < 2 ^ (prefixWord ++ tailWord_2923034).sum := by decide
  have hdescent : baseEnd_2923034 < baseStart_2923034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923048 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 6]
def baseStart_2923048 : Nat := 118140960795 + 2923048 * 2 ^ 59
def prefixEnd_2923048 : Nat := 4983230072969 + 3 ^ 40 * 2923048 * 2
def baseEnd_2923048 : Nat := 166769844462620532773017

theorem tailTrace_2923048 : CollatzResearch.WordTrace tailWord_2923048 prefixEnd_2923048 166769844462620532773017 := by
  unfold tailWord_2923048
  simp only [CollatzResearch.WordTrace]
  refine ⟨53306159557151893849412899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71074879409535858465883865 53306159557151893849412899)
  ·
    refine ⟨79959239335727840774119349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53306159557151893849412899 79959239335727840774119349)
    ·
      refine ⟨7496178687724485072573689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79959239335727840774119349 7496178687724485072573689)
      ·
        refine ⟨5622134015793363804430267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7496178687724485072573689 5622134015793363804430267)
        ·
          refine ⟨8433201023690045706645401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622134015793363804430267 8433201023690045706645401)
          ·
            refine ⟨6324900767767534279984051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8433201023690045706645401 6324900767767534279984051)
            ·
              refine ⟨9487351151651301419976077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6324900767767534279984051 9487351151651301419976077)
              ·
                refine ⟨3557756681869238032491029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9487351151651301419976077 3557756681869238032491029)
                ·
                  refine ⟨166769844462620532773017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3557756681869238032491029 166769844462620532773017)
                  ·
                    rfl

theorem cell23_2923048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 6].length) (baseStart_2923048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923048 prefixEnd_2923048 := by exact prefixLift 2923048
  have htrace : WordTrace (prefixWord ++ tailWord_2923048) baseStart_2923048 baseEnd_2923048 := by
    simpa [prefixWord, tailWord_2923048, baseEnd_2923048] using wordTrace_append hprefix tailTrace_2923048
  have hstable : (prefixWord ++ tailWord_2923048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923048).length < 2 ^ (prefixWord ++ tailWord_2923048).sum := by decide
  have hdescent : baseEnd_2923048 < baseStart_2923048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923051 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 3, 5, 2]
def baseStart_2923051 : Nat := 118140960795 + 2923051 * 2 ^ 59
def prefixEnd_2923051 : Nat := 4983230072969 + 3 ^ 40 * 2923051 * 2
def baseEnd_2923051 : Nat := 1500930140605548283219639

theorem tailTrace_2923051 : CollatzResearch.WordTrace tailWord_2923051 prefixEnd_2923051 1500930140605548283219639 := by
  unfold tailWord_2923051
  simp only [CollatzResearch.WordTrace]
  refine ⟨106612428533292919211185007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71074952355528612807456671 106612428533292919211185007)
  ·
    refine ⟨159918642799939378816777511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106612428533292919211185007 159918642799939378816777511)
    ·
      refine ⟨239877964199909068225166267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159918642799939378816777511 239877964199909068225166267)
      ·
        refine ⟨359816946299863602337749401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239877964199909068225166267 359816946299863602337749401)
        ·
          refine ⟨269862709724897701753312051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359816946299863602337749401 269862709724897701753312051)
          ·
            refine ⟨404794064587346552629968077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269862709724897701753312051 404794064587346552629968077)
            ·
              refine ⟨151797774220254957236238029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404794064587346552629968077 151797774220254957236238029)
              ·
                refine ⟨56924165332595608963589261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151797774220254957236238029 56924165332595608963589261)
                ·
                  refine ⟨21346561999723353361345973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56924165332595608963589261 21346561999723353361345973)
                  ·
                    refine ⟨2001240187474064377626185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21346561999723353361345973 2001240187474064377626185)
                    ·
                      refine ⟨1500930140605548283219639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2001240187474064377626185 1500930140605548283219639)
                      ·
                        rfl

theorem cell23_2923051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 5, 2].length) (baseStart_2923051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923051 prefixEnd_2923051 := by exact prefixLift 2923051
  have htrace : WordTrace (prefixWord ++ tailWord_2923051) baseStart_2923051 baseEnd_2923051 := by
    simpa [prefixWord, tailWord_2923051, baseEnd_2923051] using wordTrace_append hprefix tailTrace_2923051
  have hstable : (prefixWord ++ tailWord_2923051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923051).length < 2 ^ (prefixWord ++ tailWord_2923051).sum := by decide
  have hdescent : baseEnd_2923051 < baseStart_2923051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923058 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_2923058 : Nat := 118140960795 + 2923058 * 2 ^ 59
def prefixEnd_2923058 : Nat := 4983230072969 + 3 ^ 40 * 2923058 * 2
def baseEnd_2923058 : Nat := 1500933734970129755832107

theorem tailTrace_2923058 : CollatzResearch.WordTrace tailWord_2923058 prefixEnd_2923058 1500933734970129755832107 := by
  unfold tailWord_2923058
  simp only [CollatzResearch.WordTrace]
  refine ⟨26653170961066889851672457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71075122562845039604459885 26653170961066889851672457)
  ·
    refine ⟨19989878220800167388754343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26653170961066889851672457 19989878220800167388754343)
    ·
      refine ⟨29984817331200251083131515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19989878220800167388754343 29984817331200251083131515)
      ·
        refine ⟨44977225996800376624697273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29984817331200251083131515 44977225996800376624697273)
        ·
          refine ⟨33732919497600282468522955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44977225996800376624697273 33732919497600282468522955)
          ·
            refine ⟨50599379246400423702784433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33732919497600282468522955 50599379246400423702784433)
            ·
              refine ⟨37949534434800317777088325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50599379246400423702784433 37949534434800317777088325)
              ·
                refine ⟨7115537706525059583204061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37949534434800317777088325 7115537706525059583204061)
                ·
                  refine ⟨2668326639946897343701523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7115537706525059583204061 2668326639946897343701523)
                  ·
                    refine ⟨4002489959920346015552285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2668326639946897343701523 4002489959920346015552285)
                    ·
                      refine ⟨1500933734970129755832107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4002489959920346015552285 1500933734970129755832107)
                      ·
                        rfl

theorem cell23_2923058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_2923058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923058 prefixEnd_2923058 := by exact prefixLift 2923058
  have htrace : WordTrace (prefixWord ++ tailWord_2923058) baseStart_2923058 baseEnd_2923058 := by
    simpa [prefixWord, tailWord_2923058, baseEnd_2923058] using wordTrace_append hprefix tailTrace_2923058
  have hstable : (prefixWord ++ tailWord_2923058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923058).length < 2 ^ (prefixWord ++ tailWord_2923058).sum := by decide
  have hdescent : baseEnd_2923058 < baseStart_2923058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923061 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2923061 : Nat := 118140960795 + 2923061 * 2 ^ 59
def prefixEnd_2923061 : Nat := 4983230072969 + 3 ^ 40 * 2923061 * 2
def baseEnd_2923061 : Nat := 500311758470697748031531

theorem tailTrace_2923061 : CollatzResearch.WordTrace tailWord_2923061 prefixEnd_2923061 500311758470697748031531 := by
  unfold tailWord_2923061
  simp only [CollatzResearch.WordTrace]
  refine ⟨106612793263256690919049037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71075195508837793946032691 106612793263256690919049037)
  ·
    refine ⟨39979797473721259094643389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106612793263256690919049037 39979797473721259094643389)
    ·
      refine ⟨14992424052645472160491271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39979797473721259094643389 14992424052645472160491271)
      ·
        refine ⟨22488636078968208240736907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14992424052645472160491271 22488636078968208240736907)
        ·
          refine ⟨33732954118452312361105361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22488636078968208240736907 33732954118452312361105361)
          ·
            refine ⟨25299715588839234270829021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33732954118452312361105361 25299715588839234270829021)
            ·
              refine ⟨9487393345814712851560883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25299715588839234270829021 9487393345814712851560883)
              ·
                refine ⟨14231090018722069277341325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9487393345814712851560883 14231090018722069277341325)
                ·
                  refine ⟨5336658757020775979002997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14231090018722069277341325 5336658757020775979002997)
                  ·
                    refine ⟨500311758470697748031531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5336658757020775979002997 500311758470697748031531)
                    ·
                      rfl

theorem cell23_2923061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2923061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923061 prefixEnd_2923061 := by exact prefixLift 2923061
  have htrace : WordTrace (prefixWord ++ tailWord_2923061) baseStart_2923061 baseEnd_2923061 := by
    simpa [prefixWord, tailWord_2923061, baseEnd_2923061] using wordTrace_append hprefix tailTrace_2923061
  have hstable : (prefixWord ++ tailWord_2923061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923061).length < 2 ^ (prefixWord ++ tailWord_2923061).sum := by decide
  have hdescent : baseEnd_2923061 < baseStart_2923061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923092 : List Nat := [2, 4, 1, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_2923092 : Nat := 118140960795 + 2923092 * 2 ^ 59
def prefixEnd_2923092 : Nat := 4983230072969 + 3 ^ 40 * 2923092 * 2
def baseEnd_2923092 : Nat := 1500951193312382622806951

theorem tailTrace_2923092 : CollatzResearch.WordTrace tailWord_2923092 prefixEnd_2923092 1500951193312382622806951 := by
  unfold tailWord_2923092
  simp only [CollatzResearch.WordTrace]
  refine ⟨53306961963072191606713765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71075949284096255475618353 53306961963072191606713765)
  ·
    refine ⟨9995055368076035926258831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53306961963072191606713765 9995055368076035926258831)
    ·
      refine ⟨14992583052114053889388247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9995055368076035926258831 14992583052114053889388247)
      ·
        refine ⟨22488874578171080834082371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14992583052114053889388247 22488874578171080834082371)
        ·
          refine ⟨33733311867256621251123557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22488874578171080834082371 33733311867256621251123557)
          ·
            refine ⟨6324995975110616484585667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33733311867256621251123557 6324995975110616484585667)
            ·
              refine ⟨9487493962665924726878501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6324995975110616484585667 9487493962665924726878501)
              ·
                refine ⟨1778905117999860886289719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9487493962665924726878501 1778905117999860886289719)
                ·
                  refine ⟨2668357676999791329434579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778905117999860886289719 2668357676999791329434579)
                  ·
                    refine ⟨4002536515499686994151869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2668357676999791329434579 4002536515499686994151869)
                    ·
                      refine ⟨1500951193312382622806951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4002536515499686994151869 1500951193312382622806951)
                      ·
                        rfl

theorem cell23_2923092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_2923092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923092 prefixEnd_2923092 := by exact prefixLift 2923092
  have htrace : WordTrace (prefixWord ++ tailWord_2923092) baseStart_2923092 baseEnd_2923092 := by
    simpa [prefixWord, tailWord_2923092, baseEnd_2923092] using wordTrace_append hprefix tailTrace_2923092
  have hstable : (prefixWord ++ tailWord_2923092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923092).length < 2 ^ (prefixWord ++ tailWord_2923092).sum := by decide
  have hdescent : baseEnd_2923092 < baseStart_2923092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923108 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_2923108 : Nat := 118140960795 + 2923108 * 2 ^ 59
def prefixEnd_2923108 : Nat := 4983230072969 + 3 ^ 40 * 2923108 * 2
def baseEnd_2923108 : Nat := 500319803000951520068959

theorem tailTrace_2923108 : CollatzResearch.WordTrace tailWord_2923108 prefixEnd_2923108 500319803000951520068959 := by
  unfold tailWord_2923108
  simp only [CollatzResearch.WordTrace]
  refine ⟨53307253747043208973004989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71076338329390945297339985 53307253747043208973004989)
  ·
    refine ⟨19990220155141203364876871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53307253747043208973004989 19990220155141203364876871)
    ·
      refine ⟨29985330232711805047315307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19990220155141203364876871 29985330232711805047315307)
      ·
        refine ⟨44977995349067707570972961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29985330232711805047315307 44977995349067707570972961)
        ·
          refine ⟨33733496511800780678229721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44977995349067707570972961 33733496511800780678229721)
          ·
            refine ⟨25300122383850585508672291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33733496511800780678229721 25300122383850585508672291)
            ·
              refine ⟨37950183575775878263008437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25300122383850585508672291 37950183575775878263008437)
              ·
                refine ⟨3557829710228988587157041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37950183575775878263008437 3557829710228988587157041)
                ·
                  refine ⟨2668372282671741440367781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3557829710228988587157041 2668372282671741440367781)
                  ·
                    refine ⟨500319803000951520068959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668372282671741440367781 500319803000951520068959)
                    ·
                      rfl

theorem cell23_2923108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_2923108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923108 prefixEnd_2923108 := by exact prefixLift 2923108
  have htrace : WordTrace (prefixWord ++ tailWord_2923108) baseStart_2923108 baseEnd_2923108 := by
    simpa [prefixWord, tailWord_2923108, baseEnd_2923108] using wordTrace_append hprefix tailTrace_2923108
  have hstable : (prefixWord ++ tailWord_2923108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923108).length < 2 ^ (prefixWord ++ tailWord_2923108).sum := by decide
  have hdescent : baseEnd_2923108 < baseStart_2923108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923131 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 3]
def baseStart_2923131 : Nat := 118140960795 + 2923131 * 2 ^ 59
def prefixEnd_2923131 : Nat := 4983230072969 + 3 ^ 40 * 2923131 * 2
def baseEnd_2923131 : Nat := 1500971219057907970219271

theorem tailTrace_2923131 : CollatzResearch.WordTrace tailWord_2923131 prefixEnd_2923131 1500971219057907970219271 := by
  unfold tailWord_2923131
  simp only [CollatzResearch.WordTrace]
  refine ⟨106615346373003092874097247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71076897582002061916064831 106615346373003092874097247)
  ·
    refine ⟨159923019559504639311145871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106615346373003092874097247 159923019559504639311145871)
    ·
      refine ⟨239884529339256958966718807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159923019559504639311145871 239884529339256958966718807)
      ·
        refine ⟨359826794008885438450078211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239884529339256958966718807 359826794008885438450078211)
        ·
          refine ⟨539740191013328157675117317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359826794008885438450078211 539740191013328157675117317)
          ·
            refine ⟨101201285814999029564084497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 539740191013328157675117317 101201285814999029564084497)
            ·
              refine ⟨75900964361249272173063373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101201285814999029564084497 75900964361249272173063373)
              ·
                refine ⟨28462861635468477064898765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75900964361249272173063373 28462861635468477064898765)
                ·
                  refine ⟨10673573113300678899337037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28462861635468477064898765 10673573113300678899337037)
                  ·
                    refine ⟨4002589917487754587251389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10673573113300678899337037 4002589917487754587251389)
                    ·
                      refine ⟨1500971219057907970219271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4002589917487754587251389 1500971219057907970219271)
                      ·
                        rfl

theorem cell23_2923131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 3].length) (baseStart_2923131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923131 prefixEnd_2923131 := by exact prefixLift 2923131
  have htrace : WordTrace (prefixWord ++ tailWord_2923131) baseStart_2923131 baseEnd_2923131 := by
    simpa [prefixWord, tailWord_2923131, baseEnd_2923131] using wordTrace_append hprefix tailTrace_2923131
  have hstable : (prefixWord ++ tailWord_2923131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923131).length < 2 ^ (prefixWord ++ tailWord_2923131).sum := by decide
  have hdescent : baseEnd_2923131 < baseStart_2923131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923132 : List Nat := [2, 2, 2, 1, 1, 2, 3, 5, 1, 2, 2]
def baseStart_2923132 : Nat := 118140960795 + 2923132 * 2 ^ 59
def prefixEnd_2923132 : Nat := 4983230072969 + 3 ^ 40 * 2923132 * 2
def baseEnd_2923132 : Nat := 1500971732538562466306767

theorem tailTrace_2923132 : CollatzResearch.WordTrace tailWord_2923132 prefixEnd_2923132 1500971732538562466306767 := by
  unfold tailWord_2923132
  simp only [CollatzResearch.WordTrace]
  refine ⟨53307691422999735022441825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71076921897332980029922433 53307691422999735022441825)
  ·
    refine ⟨39980768567249801266831369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53307691422999735022441825 39980768567249801266831369)
    ·
      refine ⟨29985576425437350950123527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39980768567249801266831369 29985576425437350950123527)
      ·
        refine ⟨44978364638156026425185291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29985576425437350950123527 44978364638156026425185291)
        ·
          refine ⟨67467546957234039637777937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44978364638156026425185291 67467546957234039637777937)
          ·
            refine ⟨50600660217925529728333453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67467546957234039637777937 50600660217925529728333453)
            ·
              refine ⟨18975247581722073648125045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50600660217925529728333453 18975247581722073648125045)
              ·
                refine ⟨1778929460786444404511723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18975247581722073648125045 1778929460786444404511723)
                ·
                  refine ⟨2668394191179666606767585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778929460786444404511723 2668394191179666606767585)
                  ·
                    refine ⟨2001295643384749955075689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2668394191179666606767585 2001295643384749955075689)
                    ·
                      refine ⟨1500971732538562466306767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2001295643384749955075689 1500971732538562466306767)
                      ·
                        rfl

theorem cell23_2923132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_2923132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923132 prefixEnd_2923132 := by exact prefixLift 2923132
  have htrace : WordTrace (prefixWord ++ tailWord_2923132) baseStart_2923132 baseEnd_2923132 := by
    simpa [prefixWord, tailWord_2923132, baseEnd_2923132] using wordTrace_append hprefix tailTrace_2923132
  have hstable : (prefixWord ++ tailWord_2923132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923132).length < 2 ^ (prefixWord ++ tailWord_2923132).sum := by decide
  have hdescent : baseEnd_2923132 < baseStart_2923132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923162 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2923162 : Nat := 118140960795 + 2923162 * 2 ^ 59
def prefixEnd_2923162 : Nat := 4983230072969 + 3 ^ 40 * 2923162 * 2
def baseEnd_2923162 : Nat := 1500987136958197348931629

theorem tailTrace_2923162 : CollatzResearch.WordTrace tailWord_2923162 prefixEnd_2923162 1500987136958197348931629 := by
  unfold tailWord_2923162
  simp only [CollatzResearch.WordTrace]
  refine ⟨26654119258972696292118935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71077651357260523445650493 26654119258972696292118935)
  ·
    refine ⟨39981178888459044438178403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26654119258972696292118935 39981178888459044438178403)
    ·
      refine ⟨59971768332688566657267605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39981178888459044438178403 59971768332688566657267605)
      ·
        refine ⟨2811176640594776562059419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59971768332688566657267605 2811176640594776562059419)
        ·
          refine ⟨4216764960892164843089129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2811176640594776562059419 4216764960892164843089129)
          ·
            refine ⟨3162573720669123632316847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4216764960892164843089129 3162573720669123632316847)
            ·
              refine ⟨4743860581003685448475271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162573720669123632316847 4743860581003685448475271)
              ·
                refine ⟨7115790871505528172712907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743860581003685448475271 7115790871505528172712907)
                ·
                  refine ⟨10673686307258292259069361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7115790871505528172712907 10673686307258292259069361)
                  ·
                    refine ⟨8005264730443719194302021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10673686307258292259069361 8005264730443719194302021)
                    ·
                      refine ⟨1500987136958197348931629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8005264730443719194302021 1500987136958197348931629)
                      ·
                        rfl

theorem cell23_2923162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2923162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923162 prefixEnd_2923162 := by exact prefixLift 2923162
  have htrace : WordTrace (prefixWord ++ tailWord_2923162) baseStart_2923162 baseEnd_2923162 := by
    simpa [prefixWord, tailWord_2923162, baseEnd_2923162] using wordTrace_append hprefix tailTrace_2923162
  have hstable : (prefixWord ++ tailWord_2923162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923162).length < 2 ^ (prefixWord ++ tailWord_2923162).sum := by decide
  have hdescent : baseEnd_2923162 < baseStart_2923162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923165 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_2923165 : Nat := 118140960795 + 2923165 * 2 ^ 59
def prefixEnd_2923165 : Nat := 4983230072969 + 3 ^ 40 * 2923165 * 2
def baseEnd_2923165 : Nat := 1500988677400160837194115

theorem tailTrace_2923165 : CollatzResearch.WordTrace tailWord_2923165 prefixEnd_2923165 1500988677400160837194115 := by
  unfold tailWord_2923165
  simp only [CollatzResearch.WordTrace]
  refine ⟨106616586454879916680834949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71077724303253277787223299 106616586454879916680834949)
  ·
    refine ⟨19990609960289984377656553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106616586454879916680834949 19990609960289984377656553)
    ·
      refine ⟨14992957470217488283242415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19990609960289984377656553 14992957470217488283242415)
      ·
        refine ⟨22489436205326232424863623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14992957470217488283242415 22489436205326232424863623)
        ·
          refine ⟨33734154307989348637295435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22489436205326232424863623 33734154307989348637295435)
          ·
            refine ⟨50601231461984022955943153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33734154307989348637295435 50601231461984022955943153)
            ·
              refine ⟨37950923596488017216957365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50601231461984022955943153 37950923596488017216957365)
              ·
                refine ⟨3557899087170751614089753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37950923596488017216957365 3557899087170751614089753)
                ·
                  refine ⟨2668424315378063710567315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3557899087170751614089753 2668424315378063710567315)
                  ·
                    refine ⟨4002636473067095565850973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2668424315378063710567315 4002636473067095565850973)
                    ·
                      refine ⟨1500988677400160837194115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4002636473067095565850973 1500988677400160837194115)
                      ·
                        rfl

theorem cell23_2923165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_2923165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923165 prefixEnd_2923165 := by exact prefixLift 2923165
  have htrace : WordTrace (prefixWord ++ tailWord_2923165) baseStart_2923165 baseEnd_2923165 := by
    simpa [prefixWord, tailWord_2923165, baseEnd_2923165] using wordTrace_append hprefix tailTrace_2923165
  have hstable : (prefixWord ++ tailWord_2923165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923165).length < 2 ^ (prefixWord ++ tailWord_2923165).sum := by decide
  have hdescent : baseEnd_2923165 < baseStart_2923165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923182 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2923182 : Nat := 118140960795 + 2923182 * 2 ^ 59
def prefixEnd_2923182 : Nat := 4983230072969 + 3 ^ 40 * 2923182 * 2
def baseEnd_2923182 : Nat := 1500997406571287270681537

theorem tailTrace_2923182 : CollatzResearch.WordTrace tailWord_2923182 prefixEnd_2923182 1500997406571287270681537 := by
  unfold tailWord_2923182
  simp only [CollatzResearch.WordTrace]
  refine ⟨13327150811977291073025475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71078137663878885722802533 13327150811977291073025475)
  ·
    refine ⟨19990726217965936609538213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13327150811977291073025475 19990726217965936609538213)
    ·
      refine ⟨3748261165868613114288415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19990726217965936609538213 3748261165868613114288415)
      ·
        refine ⟨5622391748802919671432623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3748261165868613114288415 5622391748802919671432623)
        ·
          refine ⟨8433587623204379507148935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622391748802919671432623 8433587623204379507148935)
          ·
            refine ⟨12650381434806569260723403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8433587623204379507148935 12650381434806569260723403)
            ·
              refine ⟨18975572152209853891085105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12650381434806569260723403 18975572152209853891085105)
              ·
                refine ⟨14231679114157390418313829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18975572152209853891085105 14231679114157390418313829)
                ·
                  refine ⟨2668439833904510703433843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14231679114157390418313829 2668439833904510703433843)
                  ·
                    refine ⟨4002659750856766055150765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2668439833904510703433843 4002659750856766055150765)
                    ·
                      refine ⟨1500997406571287270681537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4002659750856766055150765 1500997406571287270681537)
                      ·
                        rfl

theorem cell23_2923182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2923182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923182 prefixEnd_2923182 := by exact prefixLift 2923182
  have htrace : WordTrace (prefixWord ++ tailWord_2923182) baseStart_2923182 baseEnd_2923182 := by
    simpa [prefixWord, tailWord_2923182, baseEnd_2923182] using wordTrace_append hprefix tailTrace_2923182
  have hstable : (prefixWord ++ tailWord_2923182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923182).length < 2 ^ (prefixWord ++ tailWord_2923182).sum := by decide
  have hdescent : baseEnd_2923182 < baseStart_2923182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923241 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 1, 7]
def baseStart_2923241 : Nat := 118140960795 + 2923241 * 2 ^ 59
def prefixEnd_2923241 : Nat := 4983230072969 + 3 ^ 40 * 2923241 * 2
def baseEnd_2923241 : Nat := 500342567309967513281255

theorem tailTrace_2923241 : CollatzResearch.WordTrace tailWord_2923241 prefixEnd_2923241 500342567309967513281255 := by
  unfold tailWord_2923241
  simp only [CollatzResearch.WordTrace]
  refine ⟨106619358402604581660601577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71079572268403054440401051 106619358402604581660601577)
  ·
    refine ⟨79964518801953436245451183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106619358402604581660601577 79964518801953436245451183)
    ·
      refine ⟨119946778202930154368176775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79964518801953436245451183 119946778202930154368176775)
      ·
        refine ⟨179920167304395231552265163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119946778202930154368176775 179920167304395231552265163)
        ·
          refine ⟨269880250956592847328397745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179920167304395231552265163 269880250956592847328397745)
          ·
            refine ⟨202410188217444635496298309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269880250956592847328397745 202410188217444635496298309)
            ·
              refine ⟨37951910290770869155555933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202410188217444635496298309 37951910290770869155555933)
              ·
                refine ⟨14231966359039075933333475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37951910290770869155555933 14231966359039075933333475)
                ·
                  refine ⟨21347949538558613900000213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14231966359039075933333475 21347949538558613900000213)
                  ·
                    refine ⟨500342567309967513281255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21347949538558613900000213 500342567309967513281255)
                    ·
                      rfl

theorem cell23_2923241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_2923241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923241 prefixEnd_2923241 := by exact prefixLift 2923241
  have htrace : WordTrace (prefixWord ++ tailWord_2923241) baseStart_2923241 baseEnd_2923241 := by
    simpa [prefixWord, tailWord_2923241, baseEnd_2923241] using wordTrace_append hprefix tailTrace_2923241
  have hstable : (prefixWord ++ tailWord_2923241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923241).length < 2 ^ (prefixWord ++ tailWord_2923241).sum := by decide
  have hdescent : baseEnd_2923241 < baseStart_2923241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923245 : List Nat := [1, 5, 1, 2, 1, 1, 2, 5, 5]
def baseStart_2923245 : Nat := 118140960795 + 2923245 * 2 ^ 59
def prefixEnd_2923245 : Nat := 4983230072969 + 3 ^ 40 * 2923245 * 2
def baseEnd_2923245 : Nat := 166781083983613391577083

theorem tailTrace_2923245 : CollatzResearch.WordTrace tailWord_2923245 prefixEnd_2923245 166781083983613391577083 := by
  unfold tailWord_2923245
  simp only [CollatzResearch.WordTrace]
  refine ⟨106619504294590090343747189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71079669529726726895831459 106619504294590090343747189)
  ·
    refine ⟨9995578527617820969726299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106619504294590090343747189 9995578527617820969726299)
    ·
      refine ⟨14993367791426731454589449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9995578527617820969726299 14993367791426731454589449)
      ·
        refine ⟨11245025843570048590942087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14993367791426731454589449 11245025843570048590942087)
        ·
          refine ⟨16867538765355072886413131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11245025843570048590942087 16867538765355072886413131)
          ·
            refine ⟨25301308148032609329619697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16867538765355072886413131 25301308148032609329619697)
            ·
              refine ⟨18975981111024456997214773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25301308148032609329619697 18975981111024456997214773)
              ·
                refine ⟨1778998229158542843488885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18975981111024456997214773 1778998229158542843488885)
                ·
                  refine ⟨166781083983613391577083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1778998229158542843488885 166781083983613391577083)
                  ·
                    rfl

theorem cell23_2923245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_2923245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923245 prefixEnd_2923245 := by exact prefixLift 2923245
  have htrace : WordTrace (prefixWord ++ tailWord_2923245) baseStart_2923245 baseEnd_2923245 := by
    simpa [prefixWord, tailWord_2923245, baseEnd_2923245] using wordTrace_append hprefix tailTrace_2923245
  have hstable : (prefixWord ++ tailWord_2923245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923245).length < 2 ^ (prefixWord ++ tailWord_2923245).sum := by decide
  have hdescent : baseEnd_2923245 < baseStart_2923245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923258 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_2923258 : Nat := 118140960795 + 2923258 * 2 ^ 59
def prefixEnd_2923258 : Nat := 4983230072969 + 3 ^ 40 * 2923258 * 2
def baseEnd_2923258 : Nat := 500345477033676324443729

theorem tailTrace_2923258 : CollatzResearch.WordTrace tailWord_2923258 prefixEnd_2923258 500345477033676324443729 := by
  unfold tailWord_2923258
  simp only [CollatzResearch.WordTrace]
  refine ⟨26654994610885748390992607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71079985629028662375980285 26654994610885748390992607)
  ·
    refine ⟨39982491916328622586488911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26654994610885748390992607 39982491916328622586488911)
    ·
      refine ⟨59973737874492933879733367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39982491916328622586488911 59973737874492933879733367)
      ·
        refine ⟨89960606811739400819600051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59973737874492933879733367 89960606811739400819600051)
        ·
          refine ⟨134940910217609101229400077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89960606811739400819600051 134940910217609101229400077)
          ·
            refine ⟨50602841331603412961025029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134940910217609101229400077 50602841331603412961025029)
            ·
              refine ⟨9488032749675639930192193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50602841331603412961025029 9488032749675639930192193)
              ·
                refine ⟨7116024562256729947644145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9488032749675639930192193 7116024562256729947644145)
                ·
                  refine ⟨5337018421692547460733109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7116024562256729947644145 5337018421692547460733109)
                  ·
                    refine ⟨500345477033676324443729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5337018421692547460733109 500345477033676324443729)
                    ·
                      rfl

theorem cell23_2923258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_2923258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923258 prefixEnd_2923258 := by exact prefixLift 2923258
  have htrace : WordTrace (prefixWord ++ tailWord_2923258) baseStart_2923258 baseEnd_2923258 := by
    simpa [prefixWord, tailWord_2923258, baseEnd_2923258] using wordTrace_append hprefix tailTrace_2923258
  have hstable : (prefixWord ++ tailWord_2923258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923258).length < 2 ^ (prefixWord ++ tailWord_2923258).sum := by decide
  have hdescent : baseEnd_2923258 < baseStart_2923258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923262 : List Nat := [4, 2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_2923262 : Nat := 118140960795 + 2923262 * 2 ^ 59
def prefixEnd_2923262 : Nat := 4983230072969 + 3 ^ 40 * 2923262 * 2
def baseEnd_2923262 : Nat := 166782053891516328631241

theorem tailTrace_2923262 : CollatzResearch.WordTrace tailWord_2923262 prefixEnd_2923262 166782053891516328631241 := by
  unfold tailWord_2923262
  simp only [CollatzResearch.WordTrace]
  refine ⟨13327515541941062780889505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71080082890352334831410693 13327515541941062780889505)
  ·
    refine ⟨9995636656455797085667129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13327515541941062780889505 9995636656455797085667129)
    ·
      refine ⟨7496727492341847814250347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9995636656455797085667129 7496727492341847814250347)
      ·
        refine ⟨11245091238512771721375521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7496727492341847814250347 11245091238512771721375521)
        ·
          refine ⟨8433818428884578791031641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11245091238512771721375521 8433818428884578791031641)
          ·
            refine ⟨6325363821663434093273731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8433818428884578791031641 6325363821663434093273731)
            ·
              refine ⟨9488045732495151139910597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6325363821663434093273731 9488045732495151139910597)
              ·
                refine ⟨1779008574842840838733237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9488045732495151139910597 1779008574842840838733237)
                ·
                  refine ⟨166782053891516328631241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1779008574842840838733237 166782053891516328631241)
                  ·
                    rfl

theorem cell23_2923262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_2923262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923262 prefixEnd_2923262 := by exact prefixLift 2923262
  have htrace : WordTrace (prefixWord ++ tailWord_2923262) baseStart_2923262 baseEnd_2923262 := by
    simpa [prefixWord, tailWord_2923262, baseEnd_2923262] using wordTrace_append hprefix tailTrace_2923262
  have hstable : (prefixWord ++ tailWord_2923262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923262).length < 2 ^ (prefixWord ++ tailWord_2923262).sum := by decide
  have hdescent : baseEnd_2923262 < baseStart_2923262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923268 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2923268 : Nat := 118140960795 + 2923268 * 2 ^ 59
def prefixEnd_2923268 : Nat := 4983230072969 + 3 ^ 40 * 2923268 * 2
def baseEnd_2923268 : Nat := 1501041565907573934206141

theorem tailTrace_2923268 : CollatzResearch.WordTrace tailWord_2923268 prefixEnd_2923268 1501041565907573934206141 := by
  unfold tailWord_2923268
  simp only [CollatzResearch.WordTrace]
  refine ⟨53310171586753382635917229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71080228782337843514556305 53310171586753382635917229)
  ·
    refine ⟨19991314345032518488468961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53310171586753382635917229 19991314345032518488468961)
    ·
      refine ⟨14993485758774388866351721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19991314345032518488468961 14993485758774388866351721)
      ·
        refine ⟨11245114319080791649763791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14993485758774388866351721 11245114319080791649763791)
        ·
          refine ⟨16867671478621187474645687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11245114319080791649763791 16867671478621187474645687)
          ·
            refine ⟨25301507217931781211968531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16867671478621187474645687 25301507217931781211968531)
            ·
              refine ⟨37952260826897671817952797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25301507217931781211968531 37952260826897671817952797)
              ·
                refine ⟨14232097810086626931732299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37952260826897671817952797 14232097810086626931732299)
                ·
                  refine ⟨21348146715129940397598449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14232097810086626931732299 21348146715129940397598449)
                  ·
                    refine ⟨16011110036347455298198837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21348146715129940397598449 16011110036347455298198837)
                    ·
                      refine ⟨1501041565907573934206141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16011110036347455298198837 1501041565907573934206141)
                      ·
                        rfl

theorem cell23_2923268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2923268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923268 prefixEnd_2923268 := by exact prefixLift 2923268
  have htrace : WordTrace (prefixWord ++ tailWord_2923268) baseStart_2923268 baseEnd_2923268 := by
    simpa [prefixWord, tailWord_2923268, baseEnd_2923268] using wordTrace_append hprefix tailTrace_2923268
  have hstable : (prefixWord ++ tailWord_2923268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923268).length < 2 ^ (prefixWord ++ tailWord_2923268).sum := by decide
  have hdescent : baseEnd_2923268 < baseStart_2923268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923278 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2923278 : Nat := 118140960795 + 2923278 * 2 ^ 59
def prefixEnd_2923278 : Nat := 4983230072969 + 3 ^ 40 * 2923278 * 2
def baseEnd_2923278 : Nat := 1501046700714118895081095

theorem tailTrace_2923278 : CollatzResearch.WordTrace tailWord_2923278 prefixEnd_2923278 1501046700714118895081095 := by
  unfold tailWord_2923278
  simp only [CollatzResearch.WordTrace]
  refine ⟨13327588487933817122462311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71080471935647024653132325 13327588487933817122462311)
  ·
    refine ⟨19991382731900725683693467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13327588487933817122462311 19991382731900725683693467)
    ·
      refine ⟨29987074097851088525540201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19991382731900725683693467 29987074097851088525540201)
      ·
        refine ⟨22490305573388316394155151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29987074097851088525540201 22490305573388316394155151)
        ·
          refine ⟨33735458360082474591232727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22490305573388316394155151 33735458360082474591232727)
          ·
            refine ⟨50603187540123711886849091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33735458360082474591232727 50603187540123711886849091)
            ·
              refine ⟨75904781310185567830273637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50603187540123711886849091 75904781310185567830273637)
              ·
                refine ⟨14232146495659793968176307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75904781310185567830273637 14232146495659793968176307)
                ·
                  refine ⟨21348219743489690952264461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14232146495659793968176307 21348219743489690952264461)
                  ·
                    refine ⟨8005582403808634107099173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21348219743489690952264461 8005582403808634107099173)
                    ·
                      refine ⟨1501046700714118895081095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8005582403808634107099173 1501046700714118895081095)
                      ·
                        rfl

theorem cell23_2923278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2923278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923278 prefixEnd_2923278 := by exact prefixLift 2923278
  have htrace : WordTrace (prefixWord ++ tailWord_2923278) baseStart_2923278 baseEnd_2923278 := by
    simpa [prefixWord, tailWord_2923278, baseEnd_2923278] using wordTrace_append hprefix tailTrace_2923278
  have hstable : (prefixWord ++ tailWord_2923278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923278).length < 2 ^ (prefixWord ++ tailWord_2923278).sum := by decide
  have hdescent : baseEnd_2923278 < baseStart_2923278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923291 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 6]
def baseStart_2923291 : Nat := 118140960795 + 2923291 * 2 ^ 59
def prefixEnd_2923291 : Nat := 4983230072969 + 3 ^ 40 * 2923291 * 2
def baseEnd_2923291 : Nat := 1501053375962627344218535

theorem tailTrace_2923291 : CollatzResearch.WordTrace tailWord_2923291 prefixEnd_2923291 1501053375962627344218535 := by
  unfold tailWord_2923291
  simp only [CollatzResearch.WordTrace]
  refine ⟨106621182052423440199921727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71080788034948960133281151 106621182052423440199921727)
  ·
    refine ⟨159931773078635160299882591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106621182052423440199921727 159931773078635160299882591)
    ·
      refine ⟨239897659617952740449823887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159931773078635160299882591 239897659617952740449823887)
      ·
        refine ⟨359846489426929110674735831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239897659617952740449823887 359846489426929110674735831)
        ·
          refine ⟨539769734140393666012103747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359846489426929110674735831 539769734140393666012103747)
          ·
            refine ⟨809654601210590499018155621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539769734140393666012103747 809654601210590499018155621)
            ·
              refine ⟨151810237726985718565904179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 809654601210590499018155621 151810237726985718565904179)
              ·
                refine ⟨227715356590478577848856269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151810237726985718565904179 227715356590478577848856269)
                ·
                  refine ⟨85393258721429466693321101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227715356590478577848856269 85393258721429466693321101)
                  ·
                    refine ⟨32022472020536050009995413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85393258721429466693321101 32022472020536050009995413)
                    ·
                      refine ⟨1501053375962627344218535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32022472020536050009995413 1501053375962627344218535)
                      ·
                        rfl

theorem cell23_2923291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_2923291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923291 prefixEnd_2923291 := by exact prefixLift 2923291
  have htrace : WordTrace (prefixWord ++ tailWord_2923291) baseStart_2923291 baseEnd_2923291 := by
    simpa [prefixWord, tailWord_2923291, baseEnd_2923291] using wordTrace_append hprefix tailTrace_2923291
  have hstable : (prefixWord ++ tailWord_2923291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923291).length < 2 ^ (prefixWord ++ tailWord_2923291).sum := by decide
  have hdescent : baseEnd_2923291 < baseStart_2923291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923295 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 4]
def baseStart_2923295 : Nat := 118140960795 + 2923295 * 2 ^ 59
def prefixEnd_2923295 : Nat := 4983230072969 + 3 ^ 40 * 2923295 * 2
def baseEnd_2923295 : Nat := 1501055429885245328568517

theorem tailTrace_2923295 : CollatzResearch.WordTrace tailWord_2923295 prefixEnd_2923295 1501055429885245328568517 := by
  unfold tailWord_2923295
  simp only [CollatzResearch.WordTrace]
  refine ⟨106621327944408948883067339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71080885296272632588711559 106621327944408948883067339)
  ·
    refine ⟨159931991916613423324601009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106621327944408948883067339 159931991916613423324601009)
    ·
      refine ⟨119948993937460067493450757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159931991916613423324601009 119948993937460067493450757)
      ·
        refine ⟨22490436363273762655022017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119948993937460067493450757 22490436363273762655022017)
        ·
          refine ⟨16867827272455321991266513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22490436363273762655022017 16867827272455321991266513)
          ·
            refine ⟨12650870454341491493449885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16867827272455321991266513 12650870454341491493449885)
            ·
              refine ⟨4744076420378059310043707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12650870454341491493449885 4744076420378059310043707)
              ·
                refine ⟨7116114630567088965065561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4744076420378059310043707 7116114630567088965065561)
                ·
                  refine ⟨5337085972925316723799171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7116114630567088965065561 5337085972925316723799171)
                  ·
                    refine ⟨8005628959387975085698757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5337085972925316723799171 8005628959387975085698757)
                    ·
                      refine ⟨1501055429885245328568517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8005628959387975085698757 1501055429885245328568517)
                      ·
                        rfl

theorem cell23_2923295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_2923295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923295 prefixEnd_2923295 := by exact prefixLift 2923295
  have htrace : WordTrace (prefixWord ++ tailWord_2923295) baseStart_2923295 baseEnd_2923295 := by
    simpa [prefixWord, tailWord_2923295, baseEnd_2923295] using wordTrace_append hprefix tailTrace_2923295
  have hstable : (prefixWord ++ tailWord_2923295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923295).length < 2 ^ (prefixWord ++ tailWord_2923295).sum := by decide
  have hdescent : baseEnd_2923295 < baseStart_2923295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923322 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 3, 4]
def baseStart_2923322 : Nat := 118140960795 + 2923322 * 2 ^ 59
def prefixEnd_2923322 : Nat := 4983230072969 + 3 ^ 40 * 2923322 * 2
def baseEnd_2923322 : Nat := 500356431287638907643631

theorem tailTrace_2923322 : CollatzResearch.WordTrace tailWord_2923322 prefixEnd_2923322 500356431287638907643631 := by
  unfold tailWord_2923322
  simp only [CollatzResearch.WordTrace]
  refine ⟨26655578178827783123575055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71081541810207421662866813 26655578178827783123575055)
  ·
    refine ⟨39983367268241674685362583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26655578178827783123575055 39983367268241674685362583)
    ·
      refine ⟨59975050902362512028043875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39983367268241674685362583 59975050902362512028043875)
      ·
        refine ⟨89962576353543768042065813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59975050902362512028043875 89962576353543768042065813)
        ·
          refine ⟨4216995766572364126971835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89962576353543768042065813 4216995766572364126971835)
          ·
            refine ⟨6325493649858546190457753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4216995766572364126971835 6325493649858546190457753)
            ·
              refine ⟨4744120237393909642843315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6325493649858546190457753 4744120237393909642843315)
              ·
                refine ⟨7116180356090864464264973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4744120237393909642843315 7116180356090864464264973)
                ·
                  refine ⟨2668567633534074174099365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7116180356090864464264973 2668567633534074174099365)
                  ·
                    refine ⟨500356431287638907643631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668567633534074174099365 500356431287638907643631)
                    ·
                      rfl

theorem cell23_2923322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_2923322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923322 prefixEnd_2923322 := by exact prefixLift 2923322
  have htrace : WordTrace (prefixWord ++ tailWord_2923322) baseStart_2923322 baseEnd_2923322 := by
    simpa [prefixWord, tailWord_2923322, baseEnd_2923322] using wordTrace_append hprefix tailTrace_2923322
  have hstable : (prefixWord ++ tailWord_2923322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923322).length < 2 ^ (prefixWord ++ tailWord_2923322).sum := by decide
  have hdescent : baseEnd_2923322 < baseStart_2923322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923356 : List Nat := [2, 2, 4, 2, 1, 3, 1, 3, 1, 4]
def baseStart_2923356 : Nat := 118140960795 + 2923356 * 2 ^ 59
def prefixEnd_2923356 : Nat := 4983230072969 + 3 ^ 40 * 2923356 * 2
def baseEnd_2923356 : Nat := 500362250735056529968579

theorem tailTrace_2923356 : CollatzResearch.WordTrace tailWord_2923356 prefixEnd_2923356 500362250735056529968579 := by
  unfold tailWord_2923356
  simp only [CollatzResearch.WordTrace]
  refine ⟨53311776398593978150518961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71082368531458637534025281 53311776398593978150518961)
  ·
    refine ⟨39983832298945483612889221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53311776398593978150518961 39983832298945483612889221)
    ·
      refine ⟨7496968556052278177416729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39983832298945483612889221 7496968556052278177416729)
      ·
        refine ⟨5622726417039208633062547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7496968556052278177416729 5622726417039208633062547)
        ·
          refine ⟨8434089625558812949593821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622726417039208633062547 8434089625558812949593821)
          ·
            refine ⟨3162783609584554856097683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8434089625558812949593821 3162783609584554856097683)
            ·
              refine ⟨4744175414376832284146525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162783609584554856097683 4744175414376832284146525)
              ·
                refine ⟨1779065780391312106554947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4744175414376832284146525 1779065780391312106554947)
                ·
                  refine ⟨2668598670586968159832421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779065780391312106554947 2668598670586968159832421)
                  ·
                    refine ⟨500362250735056529968579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668598670586968159832421 500362250735056529968579)
                    ·
                      rfl

theorem cell23_2923356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_2923356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923356 prefixEnd_2923356 := by exact prefixLift 2923356
  have htrace : WordTrace (prefixWord ++ tailWord_2923356) baseStart_2923356 baseEnd_2923356 := by
    simpa [prefixWord, tailWord_2923356, baseEnd_2923356] using wordTrace_append hprefix tailTrace_2923356
  have hstable : (prefixWord ++ tailWord_2923356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923356).length < 2 ^ (prefixWord ++ tailWord_2923356).sum := by decide
  have hdescent : baseEnd_2923356 < baseStart_2923356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923365 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 1, 5]
def baseStart_2923365 : Nat := 118140960795 + 2923365 * 2 ^ 59
def prefixEnd_2923365 : Nat := 4983230072969 + 3 ^ 40 * 2923365 * 2
def baseEnd_2923365 : Nat := 500363791177020018231065

theorem tailTrace_2923365 : CollatzResearch.WordTrace tailWord_2923365 prefixEnd_2923365 500363791177020018231065 := by
  unfold tailWord_2923365
  simp only [CollatzResearch.WordTrace]
  refine ⟨106623881054155350838115549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71082587369436900558743699 106623881054155350838115549)
  ·
    refine ⟨39983955395308256564293331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106623881054155350838115549 39983955395308256564293331)
    ·
      refine ⟨59975933092962384846439997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39983955395308256564293331 59975933092962384846439997)
      ·
        refine ⟨22490974909860894317414999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59975933092962384846439997 22490974909860894317414999)
        ·
          refine ⟨33736462364791341476122499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22490974909860894317414999 33736462364791341476122499)
          ·
            refine ⟨50604693547187012214183749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33736462364791341476122499 50604693547187012214183749)
            ·
              refine ⟨9488380040097564790159453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50604693547187012214183749 9488380040097564790159453)
              ·
                refine ⟨3558142515036586796309795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9488380040097564790159453 3558142515036586796309795)
                ·
                  refine ⟨5337213772554880194464693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3558142515036586796309795 5337213772554880194464693)
                  ·
                    refine ⟨500363791177020018231065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5337213772554880194464693 500363791177020018231065)
                    ·
                      rfl

theorem cell23_2923365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_2923365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923365 prefixEnd_2923365 := by exact prefixLift 2923365
  have htrace : WordTrace (prefixWord ++ tailWord_2923365) baseStart_2923365 baseEnd_2923365 := by
    simpa [prefixWord, tailWord_2923365, baseEnd_2923365] using wordTrace_append hprefix tailTrace_2923365
  have hstable : (prefixWord ++ tailWord_2923365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923365).length < 2 ^ (prefixWord ++ tailWord_2923365).sum := by decide
  have hdescent : baseEnd_2923365 < baseStart_2923365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923372 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 2, 3, 2]
def baseStart_2923372 : Nat := 118140960795 + 2923372 * 2 ^ 59
def prefixEnd_2923372 : Nat := 4983230072969 + 3 ^ 40 * 2923372 * 2
def baseEnd_2923372 : Nat := 1501094967895641527305663

theorem tailTrace_2923372 : CollatzResearch.WordTrace tailWord_2923372 prefixEnd_2923372 1501094967895641527305663 := by
  unfold tailWord_2923372
  simp only [CollatzResearch.WordTrace]
  refine ⟨53312068182564995516810185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71082757576753327355746913 53312068182564995516810185)
  ·
    refine ⟨39984051136923746637607639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53312068182564995516810185 39984051136923746637607639)
    ·
      refine ⟨59976076705385619956411459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39984051136923746637607639 59976076705385619956411459)
      ·
        refine ⟨89964115058078429934617189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59976076705385619956411459 89964115058078429934617189)
        ·
          refine ⟨16868271573389705612740723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89964115058078429934617189 16868271573389705612740723)
          ·
            refine ⟨25302407360084558419111085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16868271573389705612740723 25302407360084558419111085)
            ·
              refine ⟨9488402760031709407166657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25302407360084558419111085 9488402760031709407166657)
              ·
                refine ⟨7116302070023782055374993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9488402760031709407166657 7116302070023782055374993)
                ·
                  refine ⟨5337226552517836541531245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7116302070023782055374993 5337226552517836541531245)
                  ·
                    refine ⟨2001459957194188703074217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5337226552517836541531245 2001459957194188703074217)
                    ·
                      refine ⟨1501094967895641527305663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2001459957194188703074217 1501094967895641527305663)
                      ·
                        rfl

theorem cell23_2923372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 3, 2].length) (baseStart_2923372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923372 prefixEnd_2923372 := by exact prefixLift 2923372
  have htrace : WordTrace (prefixWord ++ tailWord_2923372) baseStart_2923372 baseEnd_2923372 := by
    simpa [prefixWord, tailWord_2923372, baseEnd_2923372] using wordTrace_append hprefix tailTrace_2923372
  have hstable : (prefixWord ++ tailWord_2923372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923372).length < 2 ^ (prefixWord ++ tailWord_2923372).sum := by decide
  have hdescent : baseEnd_2923372 < baseStart_2923372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923402 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2923402 : Nat := 118140960795 + 2923402 * 2 ^ 59
def prefixEnd_2923402 : Nat := 4983230072969 + 3 ^ 40 * 2923402 * 2
def baseEnd_2923402 : Nat := 1501110372315276409930525

theorem tailTrace_2923402 : CollatzResearch.WordTrace tailWord_2923402 prefixEnd_2923402 1501110372315276409930525 := by
  unfold tailWord_2923402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26656307638755326539303115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71083487036680870771474973 26656307638755326539303115)
  ·
    refine ⟨39984461458132989808954673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26656307638755326539303115 39984461458132989808954673)
    ·
      refine ⟨29988346093599742356716005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39984461458132989808954673 29988346093599742356716005)
      ·
        refine ⟨5622814892549951691884251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29988346093599742356716005 5622814892549951691884251)
        ·
          refine ⟨8434222338824927537826377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622814892549951691884251 8434222338824927537826377)
          ·
            refine ⟨6325666754118695653369783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8434222338824927537826377 6325666754118695653369783)
            ·
              refine ⟨9488500131178043480054675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6325666754118695653369783 9488500131178043480054675)
              ·
                refine ⟨14232750196767065220082013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9488500131178043480054675 14232750196767065220082013)
                ·
                  refine ⟨5337281323787649457530755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14232750196767065220082013 5337281323787649457530755)
                  ·
                    refine ⟨8005921985681474186296133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5337281323787649457530755 8005921985681474186296133)
                    ·
                      refine ⟨1501110372315276409930525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8005921985681474186296133 1501110372315276409930525)
                      ·
                        rfl

theorem cell23_2923402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2923402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923402 prefixEnd_2923402 := by exact prefixLift 2923402
  have htrace : WordTrace (prefixWord ++ tailWord_2923402) baseStart_2923402 baseEnd_2923402 := by
    simpa [prefixWord, tailWord_2923402, baseEnd_2923402] using wordTrace_append hprefix tailTrace_2923402
  have hstable : (prefixWord ++ tailWord_2923402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923402).length < 2 ^ (prefixWord ++ tailWord_2923402).sum := by decide
  have hdescent : baseEnd_2923402 < baseStart_2923402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923415 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_2923415 : Nat := 118140960795 + 2923415 * 2 ^ 59
def prefixEnd_2923415 : Nat := 4983230072969 + 3 ^ 40 * 2923415 * 2
def baseEnd_2923415 : Nat := 1501117047563784859067965

theorem tailTrace_2923415 : CollatzResearch.WordTrace tailWord_2923415 prefixEnd_2923415 1501117047563784859067965 := by
  unfold tailWord_2923415
  simp only [CollatzResearch.WordTrace]
  refine ⟨106625704703974209377435699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71083803135982806251623799 106625704703974209377435699)
  ·
    refine ⟨159938557055961314066153549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106625704703974209377435699 159938557055961314066153549)
    ·
      refine ⟨59976958895985492774807581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159938557055961314066153549 59976958895985492774807581)
      ·
        refine ⟨22491359585994559790552843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59976958895985492774807581 22491359585994559790552843)
        ·
          refine ⟨33737039378991839685829265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22491359585994559790552843 33737039378991839685829265)
          ·
            refine ⟨25302779534243879764371949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33737039378991839685829265 25302779534243879764371949)
            ·
              refine ⟨9488542325341454911639481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25302779534243879764371949 9488542325341454911639481)
              ·
                refine ⟨7116406744006091183729611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9488542325341454911639481 7116406744006091183729611)
                ·
                  refine ⟨10674610116009136775594417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7116406744006091183729611 10674610116009136775594417)
                  ·
                    refine ⟨8005957587006852581695813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10674610116009136775594417 8005957587006852581695813)
                    ·
                      refine ⟨1501117047563784859067965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8005957587006852581695813 1501117047563784859067965)
                      ·
                        rfl

theorem cell23_2923415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_2923415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923415 prefixEnd_2923415 := by exact prefixLift 2923415
  have htrace : WordTrace (prefixWord ++ tailWord_2923415) baseStart_2923415 baseEnd_2923415 := by
    simpa [prefixWord, tailWord_2923415, baseEnd_2923415] using wordTrace_append hprefix tailTrace_2923415
  have hstable : (prefixWord ++ tailWord_2923415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923415).length < 2 ^ (prefixWord ++ tailWord_2923415).sum := by decide
  have hdescent : baseEnd_2923415 < baseStart_2923415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923545 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 4, 5]
def baseStart_2923545 : Nat := 118140960795 + 2923545 * 2 ^ 59
def prefixEnd_2923545 : Nat := 4983230072969 + 3 ^ 40 * 2923545 * 2
def baseEnd_2923545 : Nat := 500394600016289783480789

theorem tailTrace_2923545 : CollatzResearch.WordTrace tailWord_2923545 prefixEnd_2923545 500394600016289783480789 := by
  unfold tailWord_2923545
  simp only [CollatzResearch.WordTrace]
  refine ⟨106630446193503241579668089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71086964129002161053112059 106630446193503241579668089)
  ·
    refine ⟨79972834645127431184751067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106630446193503241579668089 79972834645127431184751067)
    ·
      refine ⟨119959251967691146777126601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79972834645127431184751067 119959251967691146777126601)
      ·
        refine ⟨89969438975768360082844951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119959251967691146777126601 89969438975768360082844951)
        ·
          refine ⟨134954158463652540124267427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89969438975768360082844951 134954158463652540124267427)
          ·
            refine ⟨202431237695478810186401141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134954158463652540124267427 202431237695478810186401141)
            ·
              refine ⟨18977928533951138454975107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202431237695478810186401141 18977928533951138454975107)
              ·
                refine ⟨28466892800926707682462661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18977928533951138454975107 28466892800926707682462661)
                ·
                  refine ⟨5337542400173757690461749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28466892800926707682462661 5337542400173757690461749)
                  ·
                    refine ⟨500394600016289783480789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5337542400173757690461749 500394600016289783480789)
                    ·
                      rfl

theorem cell23_2923545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_2923545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923545 prefixEnd_2923545 := by exact prefixLift 2923545
  have htrace : WordTrace (prefixWord ++ tailWord_2923545) baseStart_2923545 baseEnd_2923545 := by
    simpa [prefixWord, tailWord_2923545, baseEnd_2923545] using wordTrace_append hprefix tailTrace_2923545
  have hstable : (prefixWord ++ tailWord_2923545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923545).length < 2 ^ (prefixWord ++ tailWord_2923545).sum := by decide
  have hdescent : baseEnd_2923545 < baseStart_2923545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923549 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 7]
def baseStart_2923549 : Nat := 118140960795 + 2923549 * 2 ^ 59
def prefixEnd_2923549 : Nat := 4983230072969 + 3 ^ 40 * 2923549 * 2
def baseEnd_2923549 : Nat := 166798428219054148310261

theorem tailTrace_2923549 : CollatzResearch.WordTrace tailWord_2923549 prefixEnd_2923549 166798428219054148310261 := by
  unfold tailWord_2923549
  simp only [CollatzResearch.WordTrace]
  refine ⟨106630592085488750262813701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71087061390325833508542467 106630592085488750262813701)
  ·
    refine ⟨19993236016029140674277569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106630592085488750262813701 19993236016029140674277569)
    ·
      refine ⟨14994927012021855505708177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19993236016029140674277569 14994927012021855505708177)
      ·
        refine ⟨11246195259016391629281133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14994927012021855505708177 11246195259016391629281133)
        ·
          refine ⟨4217323222131146860980425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11246195259016391629281133 4217323222131146860980425)
          ·
            refine ⟨3162992416598360145735319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4217323222131146860980425 3162992416598360145735319)
            ·
              refine ⟨4744488624897540218602979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162992416598360145735319 4744488624897540218602979)
              ·
                refine ⟨7116732937346310327904469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4744488624897540218602979 7116732937346310327904469)
                ·
                  refine ⟨166798428219054148310261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7116732937346310327904469 166798428219054148310261)
                  ·
                    rfl

theorem cell23_2923549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_2923549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923549 prefixEnd_2923549 := by exact prefixLift 2923549
  have htrace : WordTrace (prefixWord ++ tailWord_2923549) baseStart_2923549 baseEnd_2923549 := by
    simpa [prefixWord, tailWord_2923549, baseEnd_2923549] using wordTrace_append hprefix tailTrace_2923549
  have hstable : (prefixWord ++ tailWord_2923549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923549).length < 2 ^ (prefixWord ++ tailWord_2923549).sum := by decide
  have hdescent : baseEnd_2923549 < baseStart_2923549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923555 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 7]
def baseStart_2923555 : Nat := 118140960795 + 2923555 * 2 ^ 59
def prefixEnd_2923555 : Nat := 4983230072969 + 3 ^ 40 * 2923555 * 2
def baseEnd_2923555 : Nat := 1501188934855414311317321

theorem tailTrace_2923555 : CollatzResearch.WordTrace tailWord_2923555 prefixEnd_2923555 1501188934855414311317321 := by
  unfold tailWord_2923555
  simp only [CollatzResearch.WordTrace]
  refine ⟨106630810923467013287532119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71087207282311342191688079 106630810923467013287532119)
  ·
    refine ⟨159946216385200519931298179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106630810923467013287532119 159946216385200519931298179)
    ·
      refine ⟨239919324577800779896947269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159946216385200519931298179 239919324577800779896947269)
      ·
        refine ⟨44984873358337646230677613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239919324577800779896947269 44984873358337646230677613)
        ·
          refine ⟨16869327509376617336504105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44984873358337646230677613 16869327509376617336504105)
          ·
            refine ⟨12651995632032463002378079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16869327509376617336504105 12651995632032463002378079)
            ·
              refine ⟨18977993448048694503567119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12651995632032463002378079 18977993448048694503567119)
              ·
                refine ⟨28466990172073041755350679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18977993448048694503567119 28466990172073041755350679)
                ·
                  refine ⟨42700485258109562633026019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28466990172073041755350679 42700485258109562633026019)
                  ·
                    refine ⟨64050727887164343949539029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42700485258109562633026019 64050727887164343949539029)
                    ·
                      refine ⟨1501188934855414311317321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64050727887164343949539029 1501188934855414311317321)
                      ·
                        rfl

theorem cell23_2923555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_2923555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923555 prefixEnd_2923555 := by exact prefixLift 2923555
  have htrace : WordTrace (prefixWord ++ tailWord_2923555) baseStart_2923555 baseEnd_2923555 := by
    simpa [prefixWord, tailWord_2923555, baseEnd_2923555] using wordTrace_append hprefix tailTrace_2923555
  have hstable : (prefixWord ++ tailWord_2923555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923555).length < 2 ^ (prefixWord ++ tailWord_2923555).sum := by decide
  have hdescent : baseEnd_2923555 < baseStart_2923555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923656 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 6]
def baseStart_2923656 : Nat := 118140960795 + 2923656 * 2 ^ 59
def prefixEnd_2923656 : Nat := 4983230072969 + 3 ^ 40 * 2923656 * 2
def baseEnd_2923656 : Nat := 166804532933502046239373

theorem tailTrace_2923656 : CollatzResearch.WordTrace tailWord_2923656 prefixEnd_2923656 166804532933502046239373 := by
  unfold tailWord_2923656
  simp only [CollatzResearch.WordTrace]
  refine ⟨53317247348050553768479411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71089663130734071691305881 53317247348050553768479411)
  ·
    refine ⟨79975871022075830652719117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53317247348050553768479411 79975871022075830652719117)
    ·
      refine ⟨29990951633278436494769669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79975871022075830652719117 29990951633278436494769669)
      ·
        refine ⟨5623303431239706842769313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29990951633278436494769669 5623303431239706842769313)
        ·
          refine ⟨4217477573429780132076985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5623303431239706842769313 4217477573429780132076985)
          ·
            refine ⟨3163108180072335099057739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4217477573429780132076985 3163108180072335099057739)
            ·
              refine ⟨4744662270108502648586609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163108180072335099057739 4744662270108502648586609)
              ·
                refine ⟨3558496702581376986439957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4744662270108502648586609 3558496702581376986439957)
                ·
                  refine ⟨166804532933502046239373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3558496702581376986439957 166804532933502046239373)
                  ·
                    rfl

theorem cell23_2923656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 6].length) (baseStart_2923656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923656 prefixEnd_2923656 := by exact prefixLift 2923656
  have htrace : WordTrace (prefixWord ++ tailWord_2923656) baseStart_2923656 baseEnd_2923656 := by
    simpa [prefixWord, tailWord_2923656, baseEnd_2923656] using wordTrace_append hprefix tailTrace_2923656
  have hstable : (prefixWord ++ tailWord_2923656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923656).length < 2 ^ (prefixWord ++ tailWord_2923656).sum := by decide
  have hdescent : baseEnd_2923656 < baseStart_2923656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923659 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 2, 3, 2]
def baseStart_2923659 : Nat := 118140960795 + 2923659 * 2 ^ 59
def prefixEnd_2923659 : Nat := 4983230072969 + 3 ^ 40 * 2923659 * 2
def baseEnd_2923659 : Nat := 1501242336843481904416843

theorem tailTrace_2923659 : CollatzResearch.WordTrace tailWord_2923659 prefixEnd_2923659 1501242336843481904416843 := by
  unfold tailWord_2923659
  simp only [CollatzResearch.WordTrace]
  refine ⟨106634604115090239049318031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71089736076726826032878687 106634604115090239049318031)
  ·
    refine ⟨159951906172635358573977047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106634604115090239049318031 159951906172635358573977047)
    ·
      refine ⟨239927859258953037860965571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159951906172635358573977047 239927859258953037860965571)
      ·
        refine ⟨359891788888429556791448357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239927859258953037860965571 359891788888429556791448357)
        ·
          refine ⟨67479710416580541898396567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 359891788888429556791448357 67479710416580541898396567)
          ·
            refine ⟨101219565624870812847594851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67479710416580541898396567 101219565624870812847594851)
            ·
              refine ⟨151829348437306219271392277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101219565624870812847594851 151829348437306219271392277)
              ·
                refine ⟨7117000707998729028346513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151829348437306219271392277 7117000707998729028346513)
                ·
                  refine ⟨5337750530999046771259885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7117000707998729028346513 5337750530999046771259885)
                  ·
                    refine ⟨2001656449124642539222457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5337750530999046771259885 2001656449124642539222457)
                    ·
                      refine ⟨1501242336843481904416843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2001656449124642539222457 1501242336843481904416843)
                      ·
                        rfl

theorem cell23_2923659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 3, 2].length) (baseStart_2923659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923659 prefixEnd_2923659 := by exact prefixLift 2923659
  have htrace : WordTrace (prefixWord ++ tailWord_2923659) baseStart_2923659 baseEnd_2923659 := by
    simpa [prefixWord, tailWord_2923659, baseEnd_2923659] using wordTrace_append hprefix tailTrace_2923659
  have hstable : (prefixWord ++ tailWord_2923659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923659).length < 2 ^ (prefixWord ++ tailWord_2923659).sum := by decide
  have hdescent : baseEnd_2923659 < baseStart_2923659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923665 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 1, 12]
def baseStart_2923665 : Nat := 118140960795 + 2923665 * 2 ^ 59
def prefixEnd_2923665 : Nat := 4983230072969 + 3 ^ 40 * 2923665 * 2
def baseEnd_2923665 : Nat := 500415139242469626980605

theorem tailTrace_2923665 : CollatzResearch.WordTrace tailWord_2923665 prefixEnd_2923665 500415139242469626980605 := by
  unfold tailWord_2923665
  simp only [CollatzResearch.WordTrace]
  refine ⟨106634822953068502074036449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71089881968712334716024299 106634822953068502074036449)
  ·
    refine ⟨79976117214801376555527337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106634822953068502074036449 79976117214801376555527337)
    ·
      refine ⟨59982087911101032416645503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79976117214801376555527337 59982087911101032416645503)
      ·
        refine ⟨89973131866651548624968255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59982087911101032416645503 89973131866651548624968255)
        ·
          refine ⟨134959697799977322937452383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89973131866651548624968255 134959697799977322937452383)
          ·
            refine ⟨202439546699965984406178575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134959697799977322937452383 202439546699965984406178575)
            ·
              refine ⟨303659320049948976609267863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202439546699965984406178575 303659320049948976609267863)
              ·
                refine ⟨455488980074923464913901795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303659320049948976609267863 455488980074923464913901795)
                ·
                  refine ⟨683233470112385197370852693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455488980074923464913901795 683233470112385197370852693)
                  ·
                    refine ⟨500415139242469626980605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 683233470112385197370852693 500415139242469626980605)
                    ·
                      rfl

theorem cell23_2923665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_2923665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923665 prefixEnd_2923665 := by exact prefixLift 2923665
  have htrace : WordTrace (prefixWord ++ tailWord_2923665) baseStart_2923665 baseEnd_2923665 := by
    simpa [prefixWord, tailWord_2923665, baseEnd_2923665] using wordTrace_append hprefix tailTrace_2923665
  have hstable : (prefixWord ++ tailWord_2923665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923665).length < 2 ^ (prefixWord ++ tailWord_2923665).sum := by decide
  have hdescent : baseEnd_2923665 < baseStart_2923665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923666 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2923666 : Nat := 118140960795 + 2923666 * 2 ^ 59
def prefixEnd_2923666 : Nat := 4983230072969 + 3 ^ 40 * 2923666 * 2
def baseEnd_2923666 : Nat := 1501245931208063377029311

theorem tailTrace_2923666 : CollatzResearch.WordTrace tailWord_2923666 prefixEnd_2923666 1501245931208063377029311 := by
  unfold tailWord_2923666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26658714856516219811205713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71089906284043252829881901 26658714856516219811205713)
  ·
    refine ⟨19994036142387164858404285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26658714856516219811205713 19994036142387164858404285)
    ·
      refine ⟨7497763553395186821901607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19994036142387164858404285 7497763553395186821901607)
      ·
        refine ⟨11246645330092780232852411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7497763553395186821901607 11246645330092780232852411)
        ·
          refine ⟨16869967995139170349278617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11246645330092780232852411 16869967995139170349278617)
          ·
            refine ⟨12652475996354377761958963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16869967995139170349278617 12652475996354377761958963)
            ·
              refine ⟨18978713994531566642938445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12652475996354377761958963 18978713994531566642938445)
              ·
                refine ⟨7117017747949337491101917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18978713994531566642938445 7117017747949337491101917)
                ·
                  refine ⟨2668881655481001559163219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7117017747949337491101917 2668881655481001559163219)
                  ·
                    refine ⟨4003322483221502338744829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2668881655481001559163219 4003322483221502338744829)
                    ·
                      refine ⟨1501245931208063377029311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4003322483221502338744829 1501245931208063377029311)
                      ·
                        rfl

theorem cell23_2923666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2923666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923666 prefixEnd_2923666 := by exact prefixLift 2923666
  have htrace : WordTrace (prefixWord ++ tailWord_2923666) baseStart_2923666 baseEnd_2923666 := by
    simpa [prefixWord, tailWord_2923666, baseEnd_2923666] using wordTrace_append hprefix tailTrace_2923666
  have hstable : (prefixWord ++ tailWord_2923666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923666).length < 2 ^ (prefixWord ++ tailWord_2923666).sum := by decide
  have hdescent : baseEnd_2923666 < baseStart_2923666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923733 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 2, 4]
def baseStart_2923733 : Nat := 118140960795 + 2923733 * 2 ^ 59
def prefixEnd_2923733 : Nat := 4983230072969 + 3 ^ 40 * 2923733 * 2
def baseEnd_2923733 : Nat := 500426778137304871630501

theorem tailTrace_2923733 : CollatzResearch.WordTrace tailWord_2923733 prefixEnd_2923733 500426778137304871630501 := by
  unfold tailWord_2923733
  simp only [CollatzResearch.WordTrace]
  refine ⟨106637303116822149687511853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71091535411214766458341235 106637303116822149687511853)
  ·
    refine ⟨39988988668808306132816945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106637303116822149687511853 39988988668808306132816945)
    ·
      refine ⟨29991741501606229599612709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39988988668808306132816945 29991741501606229599612709)
      ·
        refine ⟨5623451531551168049927383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29991741501606229599612709 5623451531551168049927383)
        ·
          refine ⟨8435177297326752074891075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5623451531551168049927383 8435177297326752074891075)
          ·
            refine ⟨12652765945990128112336613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8435177297326752074891075 12652765945990128112336613)
            ·
              refine ⟨2372393614873149021063115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12652765945990128112336613 2372393614873149021063115)
              ·
                refine ⟨3558590422309723531594673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2372393614873149021063115 3558590422309723531594673)
                ·
                  refine ⟨2668942816732292648696005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3558590422309723531594673 2668942816732292648696005)
                  ·
                    refine ⟨500426778137304871630501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668942816732292648696005 500426778137304871630501)
                    ·
                      rfl

theorem cell23_2923733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_2923733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923733 prefixEnd_2923733 := by exact prefixLift 2923733
  have htrace : WordTrace (prefixWord ++ tailWord_2923733) baseStart_2923733 baseEnd_2923733 := by
    simpa [prefixWord, tailWord_2923733, baseEnd_2923733] using wordTrace_append hprefix tailTrace_2923733
  have hstable : (prefixWord ++ tailWord_2923733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923733).length < 2 ^ (prefixWord ++ tailWord_2923733).sum := by decide
  have hdescent : baseEnd_2923733 < baseStart_2923733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923774 : List Nat := [4, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_2923774 : Nat := 118140960795 + 2923774 * 2 ^ 59
def prefixEnd_2923774 : Nat := 4983230072969 + 3 ^ 40 * 2923774 * 2
def baseEnd_2923774 : Nat := 1501301387118748954478815

theorem tailTrace_2923774 : CollatzResearch.WordTrace tailWord_2923774 prefixEnd_2923774 1501301387118748954478815 := by
  unfold tailWord_2923774
  simp only [CollatzResearch.WordTrace]
  refine ⟨13329849813709201711219297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71092532339782409126502917 13329849813709201711219297)
  ·
    refine ⟨9997387360281901283414473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13329849813709201711219297 9997387360281901283414473)
    ·
      refine ⟨7498040520211425962560855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9997387360281901283414473 7498040520211425962560855)
      ·
        refine ⟨11247060780317138943841283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7498040520211425962560855 11247060780317138943841283)
        ·
          refine ⟨16870591170475708415761925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11247060780317138943841283 16870591170475708415761925)
          ·
            refine ⟨3163235844464195327955361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16870591170475708415761925 3163235844464195327955361)
            ·
              refine ⟨2372426883348146495966521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3163235844464195327955361 2372426883348146495966521)
              ·
                refine ⟨1779320162511109871974891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372426883348146495966521 1779320162511109871974891)
                ·
                  refine ⟨2668980243766664807962337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779320162511109871974891 2668980243766664807962337)
                  ·
                    refine ⟨2001735182824998605971753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2668980243766664807962337 2001735182824998605971753)
                    ·
                      refine ⟨1501301387118748954478815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2001735182824998605971753 1501301387118748954478815)
                      ·
                        rfl

theorem cell23_2923774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_2923774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923774 prefixEnd_2923774 := by exact prefixLift 2923774
  have htrace : WordTrace (prefixWord ++ tailWord_2923774) baseStart_2923774 baseEnd_2923774 := by
    simpa [prefixWord, tailWord_2923774, baseEnd_2923774] using wordTrace_append hprefix tailTrace_2923774
  have hstable : (prefixWord ++ tailWord_2923774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923774).length < 2 ^ (prefixWord ++ tailWord_2923774).sum := by decide
  have hdescent : baseEnd_2923774 < baseStart_2923774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923799 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2923799 : Nat := 118140960795 + 2923799 * 2 ^ 59
def prefixEnd_2923799 : Nat := 4983230072969 + 3 ^ 40 * 2923799 * 2
def baseEnd_2923799 : Nat := 1501314224135111356666199

theorem tailTrace_2923799 : CollatzResearch.WordTrace tailWord_2923799 prefixEnd_2923799 1501314224135111356666199 := by
  unfold tailWord_2923799
  simp only [CollatzResearch.WordTrace]
  refine ⟨106639710334583042959414451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71093140223055361972942967 106639710334583042959414451)
  ·
    refine ⟨159959565501874564439121677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106639710334583042959414451 159959565501874564439121677)
    ·
      refine ⟨59984837063202961664670629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159959565501874564439121677 59984837063202961664670629)
      ·
        refine ⟨11247156949350555312125743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59984837063202961664670629 11247156949350555312125743)
        ·
          refine ⟨16870735424025832968188615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11247156949350555312125743 16870735424025832968188615)
          ·
            refine ⟨25306103136038749452282923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16870735424025832968188615 25306103136038749452282923)
            ·
              refine ⟨37959154704058124178424385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25306103136038749452282923 37959154704058124178424385)
              ·
                refine ⟨28469366028043593133818289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37959154704058124178424385 28469366028043593133818289)
                ·
                  refine ⟨21352024521032694850363717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28469366028043593133818289 21352024521032694850363717)
                  ·
                    refine ⟨4003504597693630284443197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21352024521032694850363717 4003504597693630284443197)
                    ·
                      refine ⟨1501314224135111356666199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4003504597693630284443197 1501314224135111356666199)
                      ·
                        rfl

theorem cell23_2923799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2923799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923799 prefixEnd_2923799 := by exact prefixLift 2923799
  have htrace : WordTrace (prefixWord ++ tailWord_2923799) baseStart_2923799 baseEnd_2923799 := by
    simpa [prefixWord, tailWord_2923799, baseEnd_2923799] using wordTrace_append hprefix tailTrace_2923799
  have hstable : (prefixWord ++ tailWord_2923799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923799).length < 2 ^ (prefixWord ++ tailWord_2923799).sum := by decide
  have hdescent : baseEnd_2923799 < baseStart_2923799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923836 : List Nat := [2, 2, 2, 2, 1, 3, 2, 4, 5]
def baseStart_2923836 : Nat := 118140960795 + 2923836 * 2 ^ 59
def prefixEnd_2923836 : Nat := 4983230072969 + 3 ^ 40 * 2923836 * 2
def baseEnd_2923836 : Nat := 166814802546591967989281

theorem tailTrace_2923836 : CollatzResearch.WordTrace tailWord_2923836 prefixEnd_2923836 166814802546591967989281 := by
  unfold tailWord_2923836
  simp only [CollatzResearch.WordTrace]
  refine ⟨53320529917724499139255681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71094039890299332185674241 53320529917724499139255681)
  ·
    refine ⟨39990397438293374354441761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53320529917724499139255681 39990397438293374354441761)
    ·
      refine ⟨29992798078720030765831321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39990397438293374354441761 29992798078720030765831321)
      ·
        refine ⟨22494598559040023074373491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29992798078720030765831321 22494598559040023074373491)
        ·
          refine ⟨33741897838560034611560237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22494598559040023074373491 33741897838560034611560237)
          ·
            refine ⟨12653211689460012979335089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33741897838560034611560237 12653211689460012979335089)
            ·
              refine ⟨9489908767095009734501317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12653211689460012979335089 9489908767095009734501317)
              ·
                refine ⟨1779357893830314325218997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9489908767095009734501317 1779357893830314325218997)
                ·
                  refine ⟨166814802546591967989281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1779357893830314325218997 166814802546591967989281)
                  ·
                    rfl

theorem cell23_2923836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_2923836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923836 prefixEnd_2923836 := by exact prefixLift 2923836
  have htrace : WordTrace (prefixWord ++ tailWord_2923836) baseStart_2923836 baseEnd_2923836 := by
    simpa [prefixWord, tailWord_2923836, baseEnd_2923836] using wordTrace_append hprefix tailTrace_2923836
  have hstable : (prefixWord ++ tailWord_2923836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923836).length < 2 ^ (prefixWord ++ tailWord_2923836).sum := by decide
  have hdescent : baseEnd_2923836 < baseStart_2923836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923953 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 3, 1, 3]
def baseStart_2923953 : Nat := 118140960795 + 2923953 * 2 ^ 59
def prefixEnd_2923953 : Nat := 4983230072969 + 3 ^ 40 * 2923953 * 2
def baseEnd_2923953 : Nat := 1501393300155903754140491

theorem tailTrace_2923953 : CollatzResearch.WordTrace tailWord_2923953 prefixEnd_2923953 1501393300155903754140491 := by
  unfold tailWord_2923953
  simp only [CollatzResearch.WordTrace]
  refine ⟨106645327176025127260520513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71096884784016751507013675 106645327176025127260520513)
  ·
    refine ⟨79983995382018845445390385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106645327176025127260520513 79983995382018845445390385)
    ·
      refine ⟨59987996536514134084042789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79983995382018845445390385 59987996536514134084042789)
      ·
        refine ⟨11247749350596400140758023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59987996536514134084042789 11247749350596400140758023)
        ·
          refine ⟨16871624025894600211137035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11247749350596400140758023 16871624025894600211137035)
          ·
            refine ⟨25307436038841900316705553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16871624025894600211137035 25307436038841900316705553)
            ·
              refine ⟨18980577029131425237529165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25307436038841900316705553 18980577029131425237529165)
              ·
                refine ⟨7117716385924284464073437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18980577029131425237529165 7117716385924284464073437)
                ·
                  refine ⟨2669143644721606674027539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7117716385924284464073437 2669143644721606674027539)
                  ·
                    refine ⟨4003715467082410011041309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2669143644721606674027539 4003715467082410011041309)
                    ·
                      refine ⟨1501393300155903754140491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4003715467082410011041309 1501393300155903754140491)
                      ·
                        rfl

theorem cell23_2923953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_2923953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923953 prefixEnd_2923953 := by exact prefixLift 2923953
  have htrace : WordTrace (prefixWord ++ tailWord_2923953) baseStart_2923953 baseEnd_2923953 := by
    simpa [prefixWord, tailWord_2923953, baseEnd_2923953] using wordTrace_append hprefix tailTrace_2923953
  have hstable : (prefixWord ++ tailWord_2923953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923953).length < 2 ^ (prefixWord ++ tailWord_2923953).sum := by decide
  have hdescent : baseEnd_2923953 < baseStart_2923953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923976 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_2923976 : Nat := 118140960795 + 2923976 * 2 ^ 59
def prefixEnd_2923976 : Nat := 4983230072969 + 3 ^ 40 * 2923976 * 2
def baseEnd_2923976 : Nat := 1501405110210957164152885

theorem tailTrace_2923976 : CollatzResearch.WordTrace tailWord_2923976 prefixEnd_2923976 1501405110210957164152885 := by
  unfold tailWord_2923976
  simp only [CollatzResearch.WordTrace]
  refine ⟨53323083027470901094303891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71097444036627868125738521 53323083027470901094303891)
  ·
    refine ⟨79984624541206351641455837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53323083027470901094303891 79984624541206351641455837)
    ·
      refine ⟨29994234202952381865545939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79984624541206351641455837 29994234202952381865545939)
      ·
        refine ⟨44991351304428572798318909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29994234202952381865545939 44991351304428572798318909)
        ·
          refine ⟨16871756739160714799369591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44991351304428572798318909 16871756739160714799369591)
          ·
            refine ⟨25307635108741072199054387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16871756739160714799369591 25307635108741072199054387)
            ·
              refine ⟨37961452663111608298581581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25307635108741072199054387 37961452663111608298581581)
              ·
                refine ⟨14235544748666853111968093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37961452663111608298581581 14235544748666853111968093)
                ·
                  refine ⟨5338329280750069916988035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14235544748666853111968093 5338329280750069916988035)
                  ·
                    refine ⟨8007493921125104875482053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5338329280750069916988035 8007493921125104875482053)
                    ·
                      refine ⟨1501405110210957164152885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8007493921125104875482053 1501405110210957164152885)
                      ·
                        rfl

theorem cell23_2923976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_2923976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923976 prefixEnd_2923976 := by exact prefixLift 2923976
  have htrace : WordTrace (prefixWord ++ tailWord_2923976) baseStart_2923976 baseEnd_2923976 := by
    simpa [prefixWord, tailWord_2923976, baseEnd_2923976] using wordTrace_append hprefix tailTrace_2923976
  have hstable : (prefixWord ++ tailWord_2923976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923976).length < 2 ^ (prefixWord ++ tailWord_2923976).sum := by decide
  have hdescent : baseEnd_2923976 < baseStart_2923976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923980 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 2, 3, 2]
def baseStart_2923980 : Nat := 118140960795 + 2923980 * 2 ^ 59
def prefixEnd_2923980 : Nat := 4983230072969 + 3 ^ 40 * 2923980 * 2
def baseEnd_2923980 : Nat := 1501407164133575148502867

theorem tailTrace_2923980 : CollatzResearch.WordTrace tailWord_2923980 prefixEnd_2923980 1501407164133575148502867 := by
  unfold tailWord_2923980
  simp only [CollatzResearch.WordTrace]
  refine ⟨53323155973463655435876697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71097541297951540581168929 53323155973463655435876697)
  ·
    refine ⟨39992366980097741576907523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53323155973463655435876697 39992366980097741576907523)
    ·
      refine ⟨59988550470146612365361285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39992366980097741576907523 59988550470146612365361285)
      ·
        refine ⟨11247853213152489818505241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59988550470146612365361285 11247853213152489818505241)
        ·
          refine ⟨8435889909864367363878931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11247853213152489818505241 8435889909864367363878931)
          ·
            refine ⟨12653834864796551045818397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8435889909864367363878931 12653834864796551045818397)
            ·
              refine ⟨4745188074298706642181899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12653834864796551045818397 4745188074298706642181899)
              ·
                refine ⟨7117782111448059963272849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4745188074298706642181899 7117782111448059963272849)
                ·
                  refine ⟨5338336583586044972454637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7117782111448059963272849 5338336583586044972454637)
                  ·
                    refine ⟨2001876218844766864670489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5338336583586044972454637 2001876218844766864670489)
                    ·
                      refine ⟨1501407164133575148502867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2001876218844766864670489 1501407164133575148502867)
                      ·
                        rfl

theorem cell23_2923980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_2923980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923980 prefixEnd_2923980 := by exact prefixLift 2923980
  have htrace : WordTrace (prefixWord ++ tailWord_2923980) baseStart_2923980 baseEnd_2923980 := by
    simpa [prefixWord, tailWord_2923980, baseEnd_2923980] using wordTrace_append hprefix tailTrace_2923980
  have hstable : (prefixWord ++ tailWord_2923980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923980).length < 2 ^ (prefixWord ++ tailWord_2923980).sum := by decide
  have hdescent : baseEnd_2923980 < baseStart_2923980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923990 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_2923990 : Nat := 118140960795 + 2923990 * 2 ^ 59
def prefixEnd_2923990 : Nat := 4983230072969 + 3 ^ 40 * 2923990 * 2
def baseEnd_2923990 : Nat := 500470766313373369792607

theorem tailTrace_2923990 : CollatzResearch.WordTrace tailWord_2923990 prefixEnd_2923990 500470766313373369792607 := by
  unfold tailWord_2923990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6665417292305692661226089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71097784451260721719744949 6665417292305692661226089)
  ·
    refine ⟨4999062969229269495919567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6665417292305692661226089 4999062969229269495919567)
    ·
      refine ⟨7498594453843904243879351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999062969229269495919567 7498594453843904243879351)
      ·
        refine ⟨11247891680765856365819027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7498594453843904243879351 11247891680765856365819027)
        ·
          refine ⟨16871837521148784548728541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11247891680765856365819027 16871837521148784548728541)
          ·
            refine ⟨6326939070430794205773203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16871837521148784548728541 6326939070430794205773203)
            ·
              refine ⟨9490408605646191308659805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6326939070430794205773203 9490408605646191308659805)
              ·
                refine ⟨3558903227117321740747427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9490408605646191308659805 3558903227117321740747427)
                ·
                  refine ⟨5338354840675982611121141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3558903227117321740747427 5338354840675982611121141)
                  ·
                    refine ⟨500470766313373369792607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5338354840675982611121141 500470766313373369792607)
                    ·
                      rfl

theorem cell23_2923990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_2923990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923990 prefixEnd_2923990 := by exact prefixLift 2923990
  have htrace : WordTrace (prefixWord ++ tailWord_2923990) baseStart_2923990 baseEnd_2923990 := by
    simpa [prefixWord, tailWord_2923990, baseEnd_2923990] using wordTrace_append hprefix tailTrace_2923990
  have hstable : (prefixWord ++ tailWord_2923990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923990).length < 2 ^ (prefixWord ++ tailWord_2923990).sum := by decide
  have hdescent : baseEnd_2923990 < baseStart_2923990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923993 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 4]
def baseStart_2923993 : Nat := 118140960795 + 2923993 * 2 ^ 59
def prefixEnd_2923993 : Nat := 4983230072969 + 3 ^ 40 * 2923993 * 2
def baseEnd_2923993 : Nat := 1501413839382083597640307

theorem tailTrace_2923993 : CollatzResearch.WordTrace tailWord_2923993 prefixEnd_2923993 1501413839382083597640307 := by
  unfold tailWord_2923993
  simp only [CollatzResearch.WordTrace]
  refine ⟨106646786095880214091976633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71097857397253476061317755 106646786095880214091976633)
  ·
    refine ⟨79985089571910160568982475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106646786095880214091976633 79985089571910160568982475)
    ·
      refine ⟨119977634357865240853473713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79985089571910160568982475 119977634357865240853473713)
      ·
        refine ⟨89983225768398930640105285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119977634357865240853473713 89983225768398930640105285)
        ·
          refine ⟨16871854831574799495019741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89983225768398930640105285 16871854831574799495019741)
          ·
            refine ⟨6326945561840549810632403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16871854831574799495019741 6326945561840549810632403)
            ·
              refine ⟨9490418342760824715948605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6326945561840549810632403 9490418342760824715948605)
              ·
                refine ⟨3558906878535309268480727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9490418342760824715948605 3558906878535309268480727)
                ·
                  refine ⟨5338360317802963902721091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3558906878535309268480727 5338360317802963902721091)
                  ·
                    refine ⟨8007540476704445854081637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5338360317802963902721091 8007540476704445854081637)
                    ·
                      refine ⟨1501413839382083597640307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8007540476704445854081637 1501413839382083597640307)
                      ·
                        rfl

theorem cell23_2923993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_2923993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923993 prefixEnd_2923993 := by exact prefixLift 2923993
  have htrace : WordTrace (prefixWord ++ tailWord_2923993) baseStart_2923993 baseEnd_2923993 := by
    simpa [prefixWord, tailWord_2923993, baseEnd_2923993] using wordTrace_append hprefix tailTrace_2923993
  have hstable : (prefixWord ++ tailWord_2923993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923993).length < 2 ^ (prefixWord ++ tailWord_2923993).sum := by decide
  have hdescent : baseEnd_2923993 < baseStart_2923993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2923999 : List Nat := [1, 1, 2, 3, 3, 1, 12]
def baseStart_2923999 : Nat := 118140960795 + 2923999 * 2 ^ 59
def prefixEnd_2923999 : Nat := 4983230072969 + 3 ^ 40 * 2923999 * 2
def baseEnd_2923999 : Nat := 18536011361308772520559

theorem tailTrace_2923999 : CollatzResearch.WordTrace tailWord_2923999 prefixEnd_2923999 18536011361308772520559 := by
  unfold tailWord_2923999
  simp only [CollatzResearch.WordTrace]
  refine ⟨106647004933858477116695051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71098003289238984744463367 106647004933858477116695051)
  ·
    refine ⟨159970507400787715675042577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106647004933858477116695051 159970507400787715675042577)
    ·
      refine ⟨119977880550590786756281933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159970507400787715675042577 119977880550590786756281933)
      ·
        refine ⟨44991705206471545033605725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119977880550590786756281933 44991705206471545033605725)
        ·
          refine ⟨16871889452426829387602147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44991705206471545033605725 16871889452426829387602147)
          ·
            refine ⟨25307834178640244081403221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16871889452426829387602147 25307834178640244081403221)
            ·
              refine ⟨18536011361308772520559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 25307834178640244081403221 18536011361308772520559)
              ·
                rfl

theorem cell23_2923999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 12].length) (baseStart_2923999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2923999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2923999 prefixEnd_2923999 := by exact prefixLift 2923999
  have htrace : WordTrace (prefixWord ++ tailWord_2923999) baseStart_2923999 baseEnd_2923999 := by
    simpa [prefixWord, tailWord_2923999, baseEnd_2923999] using wordTrace_append hprefix tailTrace_2923999
  have hstable : (prefixWord ++ tailWord_2923999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2923999).length < 2 ^ (prefixWord ++ tailWord_2923999).sum := by decide
  have hdescent : baseEnd_2923999 < baseStart_2923999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2923999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924003 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 4, 4]
def baseStart_2924003 : Nat := 118140960795 + 2924003 * 2 ^ 59
def prefixEnd_2924003 : Nat := 4983230072969 + 3 ^ 40 * 2924003 * 2
def baseEnd_2924003 : Nat := 500472991396209519505087

theorem tailTrace_2924003 : CollatzResearch.WordTrace tailWord_2924003 prefixEnd_2924003 500472991396209519505087 := by
  unfold tailWord_2924003
  simp only [CollatzResearch.WordTrace]
  refine ⟨106647150825843985799840663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71098100550562657199893775 106647150825843985799840663)
  ·
    refine ⟨159970726238765978699760995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106647150825843985799840663 159970726238765978699760995)
    ·
      refine ⟨239956089358148968049641493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159970726238765978699760995 239956089358148968049641493)
      ·
        refine ⟨11247941688663232877326945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 239956089358148968049641493 11247941688663232877326945)
        ·
          refine ⟨8435956266497424657995209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11247941688663232877326945 8435956266497424657995209)
          ·
            refine ⟨6326967199873068493496407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8435956266497424657995209 6326967199873068493496407)
            ·
              refine ⟨9490450799809602740244611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6326967199873068493496407 9490450799809602740244611)
              ·
                refine ⟨14235676199714404110366917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9490450799809602740244611 14235676199714404110366917)
                ·
                  refine ⟨2669189287446450770693797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14235676199714404110366917 2669189287446450770693797)
                  ·
                    refine ⟨500472991396209519505087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2669189287446450770693797 500472991396209519505087)
                    ·
                      rfl

theorem cell23_2924003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 4].length) (baseStart_2924003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924003 prefixEnd_2924003 := by exact prefixLift 2924003
  have htrace : WordTrace (prefixWord ++ tailWord_2924003) baseStart_2924003 baseEnd_2924003 := by
    simpa [prefixWord, tailWord_2924003, baseEnd_2924003] using wordTrace_append hprefix tailTrace_2924003
  have hstable : (prefixWord ++ tailWord_2924003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924003).length < 2 ^ (prefixWord ++ tailWord_2924003).sum := by decide
  have hdescent : baseEnd_2924003 < baseStart_2924003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924019 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 6]
def baseStart_2924019 : Nat := 118140960795 + 2924019 * 2 ^ 59
def prefixEnd_2924019 : Nat := 4983230072969 + 3 ^ 40 * 2924019 * 2
def baseEnd_2924019 : Nat := 1501427189879100495915187

theorem tailTrace_2924019 : CollatzResearch.WordTrace tailWord_2924019 prefixEnd_2924019 1501427189879100495915187 := by
  unfold tailWord_2924019
  simp only [CollatzResearch.WordTrace]
  refine ⟨106647734393786020532423111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71098489595857347021615407 106647734393786020532423111)
  ·
    refine ⟨159971601590679030798634667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106647734393786020532423111 159971601590679030798634667)
    ·
      refine ⟨239957402386018546197952001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159971601590679030798634667 239957402386018546197952001)
      ·
        refine ⟨179968051789513909648464001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239957402386018546197952001 179968051789513909648464001)
        ·
          refine ⟨134976038842135432236348001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179968051789513909648464001 134976038842135432236348001)
          ·
            refine ⟨101232029131601574177261001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134976038842135432236348001 101232029131601574177261001)
            ·
              refine ⟨75924021848701180632945751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101232029131601574177261001 75924021848701180632945751)
              ·
                refine ⟨113886032773051770949418627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75924021848701180632945751 113886032773051770949418627)
                ·
                  refine ⟨170829049159577656424127941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113886032773051770949418627 170829049159577656424127941)
                  ·
                    refine ⟨32030446717420810579523989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170829049159577656424127941 32030446717420810579523989)
                    ·
                      refine ⟨1501427189879100495915187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32030446717420810579523989 1501427189879100495915187)
                      ·
                        rfl

theorem cell23_2924019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_2924019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924019 prefixEnd_2924019 := by exact prefixLift 2924019
  have htrace : WordTrace (prefixWord ++ tailWord_2924019) baseStart_2924019 baseEnd_2924019 := by
    simpa [prefixWord, tailWord_2924019, baseEnd_2924019] using wordTrace_append hprefix tailTrace_2924019
  have hstable : (prefixWord ++ tailWord_2924019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924019).length < 2 ^ (prefixWord ++ tailWord_2924019).sum := by decide
  have hdescent : baseEnd_2924019 < baseStart_2924019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924060 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_2924060 : Nat := 118140960795 + 2924060 * 2 ^ 59
def prefixEnd_2924060 : Nat := 4983230072969 + 3 ^ 40 * 2924060 * 2
def baseEnd_2924060 : Nat := 1501448242585934835502499

theorem tailTrace_2924060 : CollatzResearch.WordTrace tailWord_2924060 prefixEnd_2924060 1501448242585934835502499 := by
  unfold tailWord_2924060
  simp only [CollatzResearch.WordTrace]
  refine ⟨53324614893318742267332817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71099486524424989689777089 53324614893318742267332817)
  ·
    refine ⟨39993461169989056700499613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53324614893318742267332817 39993461169989056700499613)
    ·
      refine ⟨14997547938745896262687355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39993461169989056700499613 14997547938745896262687355)
      ·
        refine ⟨22496321908118844394031033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14997547938745896262687355 22496321908118844394031033)
        ·
          refine ⟨16872241431089133295523275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22496321908118844394031033 16872241431089133295523275)
          ·
            refine ⟨25308362146633699943284913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16872241431089133295523275 25308362146633699943284913)
            ·
              refine ⟨18981271609975274957463685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25308362146633699943284913 18981271609975274957463685)
              ·
                refine ⟨3558988426870364054524441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18981271609975274957463685 3558988426870364054524441)
                ·
                  refine ⟨2669241320152773040893331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3558988426870364054524441 2669241320152773040893331)
                  ·
                    refine ⟨4003861980229159561339997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2669241320152773040893331 4003861980229159561339997)
                    ·
                      refine ⟨1501448242585934835502499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4003861980229159561339997 1501448242585934835502499)
                      ·
                        rfl

theorem cell23_2924060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_2924060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924060 prefixEnd_2924060 := by exact prefixLift 2924060
  have htrace : WordTrace (prefixWord ++ tailWord_2924060) baseStart_2924060 baseEnd_2924060 := by
    simpa [prefixWord, tailWord_2924060, baseEnd_2924060] using wordTrace_append hprefix tailTrace_2924060
  have hstable : (prefixWord ++ tailWord_2924060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924060).length < 2 ^ (prefixWord ++ tailWord_2924060).sum := by decide
  have hdescent : baseEnd_2924060 < baseStart_2924060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924087 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 1, 3, 2]
def baseStart_2924087 : Nat := 118140960795 + 2924087 * 2 ^ 59
def prefixEnd_2924087 : Nat := 4983230072969 + 3 ^ 40 * 2924087 * 2
def baseEnd_2924087 : Nat := 1501462106563606229864875

theorem tailTrace_2924087 : CollatzResearch.WordTrace tailWord_2924087 prefixEnd_2924087 1501462106563606229864875 := by
  unfold tailWord_2924087
  simp only [CollatzResearch.WordTrace]
  refine ⟨106650214557539668145898515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71100143038359778763932343 106650214557539668145898515)
  ·
    refine ⟨159975321836309502218847773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106650214557539668145898515 159975321836309502218847773)
    ·
      refine ⟨59990745688616063332067915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159975321836309502218847773 59990745688616063332067915)
      ·
        refine ⟨89986118532924094998101873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59990745688616063332067915 89986118532924094998101873)
        ·
          refine ⟨67489588899693071248576405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89986118532924094998101873 67489588899693071248576405)
          ·
            refine ⟨3163574479673112714777019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67489588899693071248576405 3163574479673112714777019)
            ·
              refine ⟨4745361719509669072165529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163574479673112714777019 4745361719509669072165529)
              ·
                refine ⟨3559021289632251804124147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4745361719509669072165529 3559021289632251804124147)
                ·
                  refine ⟨5338531934448377706186221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559021289632251804124147 5338531934448377706186221)
                  ·
                    refine ⟨2001949475418141639819833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5338531934448377706186221 2001949475418141639819833)
                    ·
                      refine ⟨1501462106563606229864875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2001949475418141639819833 1501462106563606229864875)
                      ·
                        rfl

theorem cell23_2924087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 3, 2].length) (baseStart_2924087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924087 prefixEnd_2924087 := by exact prefixLift 2924087
  have htrace : WordTrace (prefixWord ++ tailWord_2924087) baseStart_2924087 baseEnd_2924087 := by
    simpa [prefixWord, tailWord_2924087, baseEnd_2924087] using wordTrace_append hprefix tailTrace_2924087
  have hstable : (prefixWord ++ tailWord_2924087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924087).length < 2 ^ (prefixWord ++ tailWord_2924087).sum := by decide
  have hdescent : baseEnd_2924087 < baseStart_2924087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924096 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 4]
def baseStart_2924096 : Nat := 118140960795 + 2924096 * 2 ^ 59
def prefixEnd_2924096 : Nat := 4983230072969 + 3 ^ 40 * 2924096 * 2
def baseEnd_2924096 : Nat := 1501466727889496694652333

theorem tailTrace_2924096 : CollatzResearch.WordTrace tailWord_2924096 prefixEnd_2924096 1501466727889496694652333 := by
  unfold tailWord_2924096
  simp only [CollatzResearch.WordTrace]
  refine ⟨53325271407253531341488071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71100361876338041788650761 53325271407253531341488071)
  ·
    refine ⟨79987907110880297012232107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53325271407253531341488071 79987907110880297012232107)
    ·
      refine ⟨119981860666320445518348161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79987907110880297012232107 119981860666320445518348161)
      ·
        refine ⟨89986395499740334138761121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119981860666320445518348161 89986395499740334138761121)
        ·
          refine ⟨67489796624805250604070841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89986395499740334138761121 67489796624805250604070841)
          ·
            refine ⟨50617347468603937953053131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67489796624805250604070841 50617347468603937953053131)
            ·
              refine ⟨75926021202905906929579697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50617347468603937953053131 75926021202905906929579697)
              ·
                refine ⟨56944515902179430197184773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75926021202905906929579697 56944515902179430197184773)
                ·
                  refine ⟨10677096731658643161972145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56944515902179430197184773 10677096731658643161972145)
                  ·
                    refine ⟨8007822548743982371479109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10677096731658643161972145 8007822548743982371479109)
                    ·
                      refine ⟨1501466727889496694652333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8007822548743982371479109 1501466727889496694652333)
                      ·
                        rfl

theorem cell23_2924096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_2924096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924096 prefixEnd_2924096 := by exact prefixLift 2924096
  have htrace : WordTrace (prefixWord ++ tailWord_2924096) baseStart_2924096 baseEnd_2924096 := by
    simpa [prefixWord, tailWord_2924096, baseEnd_2924096] using wordTrace_append hprefix tailTrace_2924096
  have hstable : (prefixWord ++ tailWord_2924096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924096).length < 2 ^ (prefixWord ++ tailWord_2924096).sum := by decide
  have hdescent : baseEnd_2924096 < baseStart_2924096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924133 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 1, 5, 3]
def baseStart_2924133 : Nat := 118140960795 + 2924133 * 2 ^ 59
def prefixEnd_2924133 : Nat := 4983230072969 + 3 ^ 40 * 2924133 * 2
def baseEnd_2924133 : Nat := 1501485726673713049889663

theorem tailTrace_2924133 : CollatzResearch.WordTrace tailWord_2924133 prefixEnd_2924133 1501485726673713049889663 := by
  unfold tailWord_2924133
  simp only [CollatzResearch.WordTrace]
  refine ⟨106651892315373018002073053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71101261543582012001382035 106651892315373018002073053)
  ·
    refine ⟨39994459618264881750777395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106651892315373018002073053 39994459618264881750777395)
    ·
      refine ⟨59991689427397322626166093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39994459618264881750777395 59991689427397322626166093)
      ·
        refine ⟨22496883535273995984812285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59991689427397322626166093 22496883535273995984812285)
        ·
          refine ⟨8436331325727748494304607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22496883535273995984812285 8436331325727748494304607)
          ·
            refine ⟨12654496988591622741456911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8436331325727748494304607 12654496988591622741456911)
            ·
              refine ⟨18981745482887434112185367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12654496988591622741456911 18981745482887434112185367)
              ·
                refine ⟨28472618224331151168278051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18981745482887434112185367 28472618224331151168278051)
                ·
                  refine ⟨42708927336496726752417077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28472618224331151168278051 42708927336496726752417077)
                  ·
                    refine ⟨4003961937796568133039101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42708927336496726752417077 4003961937796568133039101)
                    ·
                      refine ⟨1501485726673713049889663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4003961937796568133039101 1501485726673713049889663)
                      ·
                        rfl

theorem cell23_2924133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_2924133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924133 prefixEnd_2924133 := by exact prefixLift 2924133
  have htrace : WordTrace (prefixWord ++ tailWord_2924133) baseStart_2924133 baseEnd_2924133 := by
    simpa [prefixWord, tailWord_2924133, baseEnd_2924133] using wordTrace_append hprefix tailTrace_2924133
  have hstable : (prefixWord ++ tailWord_2924133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924133).length < 2 ^ (prefixWord ++ tailWord_2924133).sum := by decide
  have hdescent : baseEnd_2924133 < baseStart_2924133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924143 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 4, 5, 2]
def baseStart_2924143 : Nat := 118140960795 + 2924143 * 2 ^ 59
def prefixEnd_2924143 : Nat := 4983230072969 + 3 ^ 40 * 2924143 * 2
def baseEnd_2924143 : Nat := 1501490861480258010764617

theorem tailTrace_2924143 : CollatzResearch.WordTrace tailWord_2924143 prefixEnd_2924143 1501490861480258010764617 := by
  unfold tailWord_2924143
  simp only [CollatzResearch.WordTrace]
  refine ⟨106652257045336789709937083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71101504696891193139958055 106652257045336789709937083)
  ·
    refine ⟨159978385568005184564905625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106652257045336789709937083 159978385568005184564905625)
    ·
      refine ⟨119983789176003888423679219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159978385568005184564905625 119983789176003888423679219)
      ·
        refine ⟨179975683764005832635518829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119983789176003888423679219 179975683764005832635518829)
        ·
          refine ⟨67490881411502187238319561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179975683764005832635518829 67490881411502187238319561)
          ·
            refine ⟨50618161058626640428739671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67490881411502187238319561 50618161058626640428739671)
            ·
              refine ⟨75927241587939960643109507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50618161058626640428739671 75927241587939960643109507)
              ·
                refine ⟨113890862381909940964664261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75927241587939960643109507 113890862381909940964664261)
                ·
                  refine ⟨21354536696608113930874549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113890862381909940964664261 21354536696608113930874549)
                  ·
                    refine ⟨2001987815307010681019489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21354536696608113930874549 2001987815307010681019489)
                    ·
                      refine ⟨1501490861480258010764617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2001987815307010681019489 1501490861480258010764617)
                      ·
                        rfl

theorem cell23_2924143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 5, 2].length) (baseStart_2924143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924143 prefixEnd_2924143 := by exact prefixLift 2924143
  have htrace : WordTrace (prefixWord ++ tailWord_2924143) baseStart_2924143 baseEnd_2924143 := by
    simpa [prefixWord, tailWord_2924143, baseEnd_2924143] using wordTrace_append hprefix tailTrace_2924143
  have hstable : (prefixWord ++ tailWord_2924143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924143).length < 2 ^ (prefixWord ++ tailWord_2924143).sum := by decide
  have hdescent : baseEnd_2924143 < baseStart_2924143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924168 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2924168 : Nat := 118140960795 + 2924168 * 2 ^ 59
def prefixEnd_2924168 : Nat := 4983230072969 + 3 ^ 40 * 2924168 * 2
def baseEnd_2924168 : Nat := 1501503698496620412952003

theorem tailTrace_2924168 : CollatzResearch.WordTrace tailWord_2924168 prefixEnd_2924168 1501503698496620412952003 := by
  unfold tailWord_2924168
  simp only [CollatzResearch.WordTrace]
  refine ⟨53326584435123109489798579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71102112580164145986398105 53326584435123109489798579)
  ·
    refine ⟨79989876652684664234697869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53326584435123109489798579 79989876652684664234697869)
    ·
      refine ⟨29996203744756749088011701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79989876652684664234697869 29996203744756749088011701)
      ·
        refine ⟨2812144101070945227001097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29996203744756749088011701 2812144101070945227001097)
        ·
          refine ⟨2109108075803208920250823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2812144101070945227001097 2109108075803208920250823)
          ·
            refine ⟨3163662113704813380376235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109108075803208920250823 3163662113704813380376235)
            ·
              refine ⟨4745493170557220070564353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163662113704813380376235 4745493170557220070564353)
              ·
                refine ⟨3559119877917915052923265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4745493170557220070564353 3559119877917915052923265)
                ·
                  refine ⟨2669339908438436289692449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3559119877917915052923265 2669339908438436289692449)
                  ·
                    refine ⟨2002004931328827217269337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2669339908438436289692449 2002004931328827217269337)
                    ·
                      refine ⟨1501503698496620412952003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2002004931328827217269337 1501503698496620412952003)
                      ·
                        rfl

theorem cell23_2924168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2924168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924168 prefixEnd_2924168 := by exact prefixLift 2924168
  have htrace : WordTrace (prefixWord ++ tailWord_2924168) baseStart_2924168 baseEnd_2924168 := by
    simpa [prefixWord, tailWord_2924168, baseEnd_2924168] using wordTrace_append hprefix tailTrace_2924168
  have hstable : (prefixWord ++ tailWord_2924168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924168).length < 2 ^ (prefixWord ++ tailWord_2924168).sum := by decide
  have hdescent : baseEnd_2924168 < baseStart_2924168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924176 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_2924176 : Nat := 118140960795 + 2924176 * 2 ^ 59
def prefixEnd_2924176 : Nat := 4983230072969 + 3 ^ 40 * 2924176 * 2
def baseEnd_2924176 : Nat := 1501507806341856381651965

theorem tailTrace_2924176 : CollatzResearch.WordTrace tailWord_2924176 prefixEnd_2924176 1501507806341856381651965 := by
  unfold tailWord_2924176
  simp only [CollatzResearch.WordTrace]
  refine ⟨53326730327108618172944191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71102307102811490897258921 53326730327108618172944191)
  ·
    refine ⟨79990095490662927259416287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53326730327108618172944191 79990095490662927259416287)
    ·
      refine ⟨119985143235994390889124431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79990095490662927259416287 119985143235994390889124431)
      ·
        refine ⟨179977714853991586333686647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119985143235994390889124431 179977714853991586333686647)
        ·
          refine ⟨269966572280987379500529971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179977714853991586333686647 269966572280987379500529971)
          ·
            refine ⟨404949858421481069250794957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269966572280987379500529971 404949858421481069250794957)
            ·
              refine ⟨151856196908055400969048109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404949858421481069250794957 151856196908055400969048109)
              ·
                refine ⟨56946073840520775363393041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151856196908055400969048109 56946073840520775363393041)
                ·
                  refine ⟨42709555380390581522544781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56946073840520775363393041 42709555380390581522544781)
                  ·
                    refine ⟨16016083267646468070954293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42709555380390581522544781 16016083267646468070954293)
                    ·
                      refine ⟨1501507806341856381651965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16016083267646468070954293 1501507806341856381651965)
                      ·
                        rfl

theorem cell23_2924176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_2924176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924176 prefixEnd_2924176 := by exact prefixLift 2924176
  have htrace : WordTrace (prefixWord ++ tailWord_2924176) baseStart_2924176 baseEnd_2924176 := by
    simpa [prefixWord, tailWord_2924176, baseEnd_2924176] using wordTrace_append hprefix tailTrace_2924176
  have hstable : (prefixWord ++ tailWord_2924176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924176).length < 2 ^ (prefixWord ++ tailWord_2924176).sum := by decide
  have hdescent : baseEnd_2924176 < baseStart_2924176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924190 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2924190 : Nat := 118140960795 + 2924190 * 2 ^ 59
def prefixEnd_2924190 : Nat := 4983230072969 + 3 ^ 40 * 2924190 * 2
def baseEnd_2924190 : Nat := 1501514995071019326876901

theorem tailTrace_2924190 : CollatzResearch.WordTrace tailWord_2924190 prefixEnd_2924190 1501514995071019326876901 := by
  unfold tailWord_2924190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13331746409520814592112253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71102647517444344491265349 13331746409520814592112253)
  ·
    refine ⟨4999404903570305472042095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13331746409520814592112253 4999404903570305472042095)
    ·
      refine ⟨7499107355355458208063143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999404903570305472042095 7499107355355458208063143)
      ·
        refine ⟨11248661033033187312094715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7499107355355458208063143 11248661033033187312094715)
        ·
          refine ⟨16872991549549780968142073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11248661033033187312094715 16872991549549780968142073)
          ·
            refine ⟨12654743662162335726106555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16872991549549780968142073 12654743662162335726106555)
            ·
              refine ⟨18982115493243503589159833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12654743662162335726106555 18982115493243503589159833)
              ·
                refine ⟨14236586619932627691869875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18982115493243503589159833 14236586619932627691869875)
                ·
                  refine ⟨21354879929898941537804813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14236586619932627691869875 21354879929898941537804813)
                  ·
                    refine ⟨8008079973712103076676805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21354879929898941537804813 8008079973712103076676805)
                    ·
                      refine ⟨1501514995071019326876901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8008079973712103076676805 1501514995071019326876901)
                      ·
                        rfl

theorem cell23_2924190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2924190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924190 prefixEnd_2924190 := by exact prefixLift 2924190
  have htrace : WordTrace (prefixWord ++ tailWord_2924190) baseStart_2924190 baseEnd_2924190 := by
    simpa [prefixWord, tailWord_2924190, baseEnd_2924190] using wordTrace_append hprefix tailTrace_2924190
  have hstable : (prefixWord ++ tailWord_2924190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924190).length < 2 ^ (prefixWord ++ tailWord_2924190).sum := by decide
  have hdescent : baseEnd_2924190 < baseStart_2924190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924217 : List Nat := [1, 2, 1, 4, 1, 1, 5, 3, 1, 4]
def baseStart_2924217 : Nat := 118140960795 + 2924217 * 2 ^ 59
def prefixEnd_2924217 : Nat := 4983230072969 + 3 ^ 40 * 2924217 * 2
def baseEnd_2924217 : Nat := 500509619682896907079759

theorem tailTrace_2924217 : CollatzResearch.WordTrace tailWord_2924217 prefixEnd_2924217 500509619682896907079759 := by
  unfold tailWord_2924217
  simp only [CollatzResearch.WordTrace]
  refine ⟨106654956047068700348130905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71103304031379133565420603 106654956047068700348130905)
  ·
    refine ⟨79991217035301525261098179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106654956047068700348130905 79991217035301525261098179)
    ·
      refine ⟨119986825552952287891647269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79991217035301525261098179 119986825552952287891647269)
      ·
        refine ⟨22497529791178553979683863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119986825552952287891647269 22497529791178553979683863)
        ·
          refine ⟨33746294686767830969525795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22497529791178553979683863 33746294686767830969525795)
          ·
            refine ⟨50619442030151746454288693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33746294686767830969525795 50619442030151746454288693)
            ·
              refine ⟨4745572690326726230089565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50619442030151746454288693 4745572690326726230089565)
              ·
                refine ⟨1779589758872522336283587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4745572690326726230089565 1779589758872522336283587)
                ·
                  refine ⟨2669384638308783504425381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779589758872522336283587 2669384638308783504425381)
                  ·
                    refine ⟨500509619682896907079759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2669384638308783504425381 500509619682896907079759)
                    ·
                      rfl

theorem cell23_2924217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 1, 4].length) (baseStart_2924217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924217 prefixEnd_2924217 := by exact prefixLift 2924217
  have htrace : WordTrace (prefixWord ++ tailWord_2924217) baseStart_2924217 baseEnd_2924217 := by
    simpa [prefixWord, tailWord_2924217, baseEnd_2924217] using wordTrace_append hprefix tailTrace_2924217
  have hstable : (prefixWord ++ tailWord_2924217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924217).length < 2 ^ (prefixWord ++ tailWord_2924217).sum := by decide
  have hdescent : baseEnd_2924217 < baseStart_2924217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924234 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 3, 4]
def baseStart_2924234 : Nat := 118140960795 + 2924234 * 2 ^ 59
def prefixEnd_2924234 : Nat := 4983230072969 + 3 ^ 40 * 2924234 * 2
def baseEnd_2924234 : Nat := 500512529406605718242233

theorem tailTrace_2924234 : CollatzResearch.WordTrace tailWord_2924234 prefixEnd_2924234 500512529406605718242233 := by
  unfold tailWord_2924234
  simp only [CollatzResearch.WordTrace]
  refine ⟨26663894022001778062874939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71103717392004741500999837 26663894022001778062874939)
  ·
    refine ⟨39995841033002667094312409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26663894022001778062874939 39995841033002667094312409)
    ·
      refine ⟨29996880774752000320734307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39995841033002667094312409 29996880774752000320734307)
      ·
        refine ⟨44995321162128000481101461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29996880774752000320734307 44995321162128000481101461)
        ·
          refine ⟨2109155679474750022551631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44995321162128000481101461 2109155679474750022551631)
          ·
            refine ⟨3163733519212125033827447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109155679474750022551631 3163733519212125033827447)
            ·
              refine ⟨4745600278818187550741171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163733519212125033827447 4745600278818187550741171)
              ·
                refine ⟨7118400418227281326111757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4745600278818187550741171 7118400418227281326111757)
                ·
                  refine ⟨2669400156835230497291909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7118400418227281326111757 2669400156835230497291909)
                  ·
                    refine ⟨500512529406605718242233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2669400156835230497291909 500512529406605718242233)
                    ·
                      rfl

theorem cell23_2924234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_2924234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924234 prefixEnd_2924234 := by exact prefixLift 2924234
  have htrace : WordTrace (prefixWord ++ tailWord_2924234) baseStart_2924234 baseEnd_2924234 := by
    simpa [prefixWord, tailWord_2924234, baseEnd_2924234] using wordTrace_append hprefix tailTrace_2924234
  have hstable : (prefixWord ++ tailWord_2924234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924234).length < 2 ^ (prefixWord ++ tailWord_2924234).sum := by decide
  have hdescent : baseEnd_2924234 < baseStart_2924234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924240 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 3, 1, 3]
def baseStart_2924240 : Nat := 118140960795 + 2924240 * 2 ^ 59
def prefixEnd_2924240 : Nat := 4983230072969 + 3 ^ 40 * 2924240 * 2
def baseEnd_2924240 : Nat := 1501540669103744131251671

theorem tailTrace_2924240 : CollatzResearch.WordTrace tailWord_2924240 prefixEnd_2924240 1501540669103744131251671 := by
  unfold tailWord_2924240
  simp only [CollatzResearch.WordTrace]
  refine ⟨53327897462992687638109087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71103863283990250184145449 53327897462992687638109087)
  ·
    refine ⟨79991846194489031457163631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53327897462992687638109087 79991846194489031457163631)
    ·
      refine ⟨119987769291733547185745447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79991846194489031457163631 119987769291733547185745447)
      ·
        refine ⟨179981653937600320778618171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119987769291733547185745447 179981653937600320778618171)
        ·
          refine ⟨269972480906400481167927257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179981653937600320778618171 269972480906400481167927257)
          ·
            refine ⟨202479360679800360875945443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269972480906400481167927257 202479360679800360875945443)
            ·
              refine ⟨303719041019700541313918165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202479360679800360875945443 303719041019700541313918165)
              ·
                refine ⟨7118415023899231437044957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 303719041019700541313918165 7118415023899231437044957)
                ·
                  refine ⟨2669405633962211788891859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7118415023899231437044957 2669405633962211788891859)
                  ·
                    refine ⟨4004108450943317683337789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2669405633962211788891859 4004108450943317683337789)
                    ·
                      refine ⟨1501540669103744131251671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4004108450943317683337789 1501540669103744131251671)
                      ·
                        rfl

theorem cell23_2924240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3, 1, 3].length) (baseStart_2924240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924240 prefixEnd_2924240 := by exact prefixLift 2924240
  have htrace : WordTrace (prefixWord ++ tailWord_2924240) baseStart_2924240 baseEnd_2924240 := by
    simpa [prefixWord, tailWord_2924240, baseEnd_2924240] using wordTrace_append hprefix tailTrace_2924240
  have hstable : (prefixWord ++ tailWord_2924240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924240).length < 2 ^ (prefixWord ++ tailWord_2924240).sum := by decide
  have hdescent : baseEnd_2924240 < baseStart_2924240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924273 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 3, 6]
def baseStart_2924273 : Nat := 118140960795 + 2924273 * 2 ^ 59
def prefixEnd_2924273 : Nat := 4983230072969 + 3 ^ 40 * 2924273 * 2
def baseEnd_2924273 : Nat := 500519204655114167379673

theorem tailTrace_2924273 : CollatzResearch.WordTrace tailWord_2924273 prefixEnd_2924273 500519204655114167379673 := by
  unfold tailWord_2924273
  simp only [CollatzResearch.WordTrace]
  refine ⟨106656998534865821912169473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71104665689910547941446315 106656998534865821912169473)
  ·
    refine ⟨79992748901149366434127105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106656998534865821912169473 79992748901149366434127105)
    ·
      refine ⟨59994561675862024825595329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79992748901149366434127105 59994561675862024825595329)
      ·
        refine ⟨44995921256896518619196497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59994561675862024825595329 44995921256896518619196497)
        ·
          refine ⟨33746940942672388964397373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44995921256896518619196497 33746940942672388964397373)
          ·
            refine ⟨12655102853502145861649015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33746940942672388964397373 12655102853502145861649015)
            ·
              refine ⟨18982654280253218792473523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12655102853502145861649015 18982654280253218792473523)
              ·
                refine ⟨28473981420379828188710285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18982654280253218792473523 28473981420379828188710285)
                ·
                  refine ⟨10677743032642435570766357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28473981420379828188710285 10677743032642435570766357)
                  ·
                    refine ⟨500519204655114167379673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10677743032642435570766357 500519204655114167379673)
                    ·
                      rfl

theorem cell23_2924273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_2924273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924273 prefixEnd_2924273 := by exact prefixLift 2924273
  have htrace : WordTrace (prefixWord ++ tailWord_2924273) baseStart_2924273 baseEnd_2924273 := by
    simpa [prefixWord, tailWord_2924273, baseEnd_2924273] using wordTrace_append hprefix tailTrace_2924273
  have hstable : (prefixWord ++ tailWord_2924273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924273).length < 2 ^ (prefixWord ++ tailWord_2924273).sum := by decide
  have hdescent : baseEnd_2924273 < baseStart_2924273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924274 : List Nat := [3, 2, 1, 3, 1, 1, 2, 5, 1, 1, 3]
def baseStart_2924274 : Nat := 118140960795 + 2924274 * 2 ^ 59
def prefixEnd_2924274 : Nat := 4983230072969 + 3 ^ 40 * 2924274 * 2
def baseEnd_2924274 : Nat := 1501558127445996998226515

theorem tailTrace_2924274 : CollatzResearch.WordTrace tailWord_2924274 prefixEnd_2924274 1501558127445996998226515 := by
  unfold tailWord_2924274
  simp only [CollatzResearch.WordTrace]
  refine ⟨26664258751965549770738969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71104690005241466055303917 26664258751965549770738969)
  ·
    refine ⟨19998194063974162328054227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26664258751965549770738969 19998194063974162328054227)
    ·
      refine ⟨29997291095961243492081341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19998194063974162328054227 29997291095961243492081341)
      ·
        refine ⟨11248984160985466309530503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29997291095961243492081341 11248984160985466309530503)
        ·
          refine ⟨16873476241478199464295755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11248984160985466309530503 16873476241478199464295755)
          ·
            refine ⟨25310214362217299196443633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16873476241478199464295755 25310214362217299196443633)
            ·
              refine ⟨18982660771662974397332725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25310214362217299196443633 18982660771662974397332725)
              ·
                refine ⟨1779624447343403849749943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18982660771662974397332725 1779624447343403849749943)
                ·
                  refine ⟨2669436671015105774624915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779624447343403849749943 2669436671015105774624915)
                  ·
                    refine ⟨4004155006522658661937373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2669436671015105774624915 4004155006522658661937373)
                    ·
                      refine ⟨1501558127445996998226515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4004155006522658661937373 1501558127445996998226515)
                      ·
                        rfl

theorem cell23_2924274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_2924274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924274 prefixEnd_2924274 := by exact prefixLift 2924274
  have htrace : WordTrace (prefixWord ++ tailWord_2924274) baseStart_2924274 baseEnd_2924274 := by
    simpa [prefixWord, tailWord_2924274, baseEnd_2924274] using wordTrace_append hprefix tailTrace_2924274
  have hstable : (prefixWord ++ tailWord_2924274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924274).length < 2 ^ (prefixWord ++ tailWord_2924274).sum := by decide
  have hdescent : baseEnd_2924274 < baseStart_2924274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924283 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 5]
def baseStart_2924283 : Nat := 118140960795 + 2924283 * 2 ^ 59
def prefixEnd_2924283 : Nat := 4983230072969 + 3 ^ 40 * 2924283 * 2
def baseEnd_2924283 : Nat := 1501562748771887463013973

theorem tailTrace_2924283 : CollatzResearch.WordTrace tailWord_2924283 prefixEnd_2924283 1501562748771887463013973 := by
  unfold tailWord_2924283
  simp only [CollatzResearch.WordTrace]
  refine ⟨106657363264829593620033503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71104908843219729080022335 106657363264829593620033503)
  ·
    refine ⟨159986044897244390430050255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106657363264829593620033503 159986044897244390430050255)
    ·
      refine ⟨239979067345866585645075383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159986044897244390430050255 239979067345866585645075383)
      ·
        refine ⟨359968601018799878467613075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239979067345866585645075383 359968601018799878467613075)
        ·
          refine ⟨539952901528199817701419613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359968601018799878467613075 539952901528199817701419613)
          ·
            refine ⟨202482338073074931638032355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 539952901528199817701419613 202482338073074931638032355)
            ·
              refine ⟨303723507109612397457048533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202482338073074931638032355 303723507109612397457048533)
              ·
                refine ⟨7118519697881540565399575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 303723507109612397457048533 7118519697881540565399575)
                ·
                  refine ⟨10677779546822310848099363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7118519697881540565399575 10677779546822310848099363)
                  ·
                    refine ⟨16016669320233466272149045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10677779546822310848099363 16016669320233466272149045)
                    ·
                      refine ⟨1501562748771887463013973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16016669320233466272149045 1501562748771887463013973)
                      ·
                        rfl

theorem cell23_2924283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 5].length) (baseStart_2924283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924283 prefixEnd_2924283 := by exact prefixLift 2924283
  have htrace : WordTrace (prefixWord ++ tailWord_2924283) baseStart_2924283 baseEnd_2924283 := by
    simpa [prefixWord, tailWord_2924283, baseEnd_2924283] using wordTrace_append hprefix tailTrace_2924283
  have hstable : (prefixWord ++ tailWord_2924283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924283).length < 2 ^ (prefixWord ++ tailWord_2924283).sum := by decide
  have hdescent : baseEnd_2924283 < baseStart_2924283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924290 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_2924290 : Nat := 118140960795 + 2924290 * 2 ^ 59
def prefixEnd_2924290 : Nat := 4983230072969 + 3 ^ 40 * 2924290 * 2
def baseEnd_2924290 : Nat := 500522114378822978542147

theorem tailTrace_2924290 : CollatzResearch.WordTrace tailWord_2924290 prefixEnd_2924290 500522114378822978542147 := by
  unfold tailWord_2924290
  simp only [CollatzResearch.WordTrace]
  refine ⟨26664404643951058453884581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71105079050536155877025549 26664404643951058453884581)
  ·
    refine ⟨4999575870740823460103359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26664404643951058453884581 4999575870740823460103359)
    ·
      refine ⟨7499363806111235190155039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999575870740823460103359 7499363806111235190155039)
      ·
        refine ⟨11249045709166852785232559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7499363806111235190155039 11249045709166852785232559)
        ·
          refine ⟨16873568563750279177848839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11249045709166852785232559 16873568563750279177848839)
          ·
            refine ⟨25310352845625418766773259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16873568563750279177848839 25310352845625418766773259)
            ·
              refine ⟨37965529268438128150159889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25310352845625418766773259 37965529268438128150159889)
              ·
                refine ⟨28474146951328596112619917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37965529268438128150159889 28474146951328596112619917)
                ·
                  refine ⟨10677805106748223542232469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28474146951328596112619917 10677805106748223542232469)
                  ·
                    refine ⟨500522114378822978542147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10677805106748223542232469 500522114378822978542147)
                    ·
                      rfl

theorem cell23_2924290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_2924290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924290 prefixEnd_2924290 := by exact prefixLift 2924290
  have htrace : WordTrace (prefixWord ++ tailWord_2924290) baseStart_2924290 baseEnd_2924290 := by
    simpa [prefixWord, tailWord_2924290, baseEnd_2924290] using wordTrace_append hprefix tailTrace_2924290
  have hstable : (prefixWord ++ tailWord_2924290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924290).length < 2 ^ (prefixWord ++ tailWord_2924290).sum := by decide
  have hdescent : baseEnd_2924290 < baseStart_2924290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924297 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 3, 2, 2]
def baseStart_2924297 : Nat := 118140960795 + 2924297 * 2 ^ 59
def prefixEnd_2924297 : Nat := 4983230072969 + 3 ^ 40 * 2924297 * 2
def baseEnd_2924297 : Nat := 1501569937501050408238909

theorem tailTrace_2924297 : CollatzResearch.WordTrace tailWord_2924297 prefixEnd_2924297 1501569937501050408238909 := by
  unfold tailWord_2924297
  simp only [CollatzResearch.WordTrace]
  refine ⟨106657873886778874011043145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71105249257852582674028763 106657873886778874011043145)
  ·
    refine ⟨79993405415084155508282359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106657873886778874011043145 79993405415084155508282359)
    ·
      refine ⟨119990108122626233262423539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79993405415084155508282359 119990108122626233262423539)
      ·
        refine ⟨179985162183939349893635309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119990108122626233262423539 179985162183939349893635309)
        ·
          refine ⟨67494435818977256210113241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179985162183939349893635309 67494435818977256210113241)
          ·
            refine ⟨50620826864232942157584931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67494435818977256210113241 50620826864232942157584931)
            ·
              refine ⟨75931240296349413236377397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50620826864232942157584931 75931240296349413236377397)
              ·
                refine ⟨7118553777782757490910381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75931240296349413236377397 7118553777782757490910381)
                ·
                  refine ⟨2669457666668534059091393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7118553777782757490910381 2669457666668534059091393)
                  ·
                    refine ⟨2002093250001400544318545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2669457666668534059091393 2002093250001400544318545)
                    ·
                      refine ⟨1501569937501050408238909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2002093250001400544318545 1501569937501050408238909)
                      ·
                        rfl

theorem cell23_2924297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 2, 2].length) (baseStart_2924297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924297 prefixEnd_2924297 := by exact prefixLift 2924297
  have htrace : WordTrace (prefixWord ++ tailWord_2924297) baseStart_2924297 baseEnd_2924297 := by
    simpa [prefixWord, tailWord_2924297, baseEnd_2924297] using wordTrace_append hprefix tailTrace_2924297
  have hstable : (prefixWord ++ tailWord_2924297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924297).length < 2 ^ (prefixWord ++ tailWord_2924297).sum := by decide
  have hdescent : baseEnd_2924297 < baseStart_2924297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924300 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 3, 2, 3]
def baseStart_2924300 : Nat := 118140960795 + 2924300 * 2 ^ 59
def prefixEnd_2924300 : Nat := 4983230072969 + 3 ^ 40 * 2924300 * 2
def baseEnd_2924300 : Nat := 1501571477943013896501395

theorem tailTrace_2924300 : CollatzResearch.WordTrace tailWord_2924300 prefixEnd_2924300 1501571477943013896501395 := by
  unfold tailWord_2924300
  simp only [CollatzResearch.WordTrace]
  refine ⟨53328991652884002761701177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71105322203845337015601569 53328991652884002761701177)
  ·
    refine ⟨39996743739663002071275883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53328991652884002761701177 39996743739663002071275883)
    ·
      refine ⟨59995115609494503106913825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39996743739663002071275883 59995115609494503106913825)
      ·
        refine ⟨44996336707120877330185369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59995115609494503106913825 44996336707120877330185369)
        ·
          refine ⟨33747252530340657997639027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44996336707120877330185369 33747252530340657997639027)
          ·
            refine ⟨50620878795510986996458541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33747252530340657997639027 50620878795510986996458541)
            ·
              refine ⟨18982829548316620123671953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50620878795510986996458541 18982829548316620123671953)
              ·
                refine ⟨14237122161237465092753965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18982829548316620123671953 14237122161237465092753965)
                ·
                  refine ⟨5338920810464049409782737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14237122161237465092753965 5338920810464049409782737)
                  ·
                    refine ⟨4004190607848037057337053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5338920810464049409782737 4004190607848037057337053)
                    ·
                      refine ⟨1501571477943013896501395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4004190607848037057337053 1501571477943013896501395)
                      ·
                        rfl

theorem cell23_2924300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_2924300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924300 prefixEnd_2924300 := by exact prefixLift 2924300
  have htrace : WordTrace (prefixWord ++ tailWord_2924300) baseStart_2924300 baseEnd_2924300 := by
    simpa [prefixWord, tailWord_2924300, baseEnd_2924300] using wordTrace_append hprefix tailTrace_2924300
  have hstable : (prefixWord ++ tailWord_2924300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924300).length < 2 ^ (prefixWord ++ tailWord_2924300).sum := by decide
  have hdescent : baseEnd_2924300 < baseStart_2924300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924308 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2924308 : Nat := 118140960795 + 2924308 * 2 ^ 59
def prefixEnd_2924308 : Nat := 4983230072969 + 3 ^ 40 * 2924308 * 2
def baseEnd_2924308 : Nat := 1501575585788249865201359

theorem tailTrace_2924308 : CollatzResearch.WordTrace tailWord_2924308 prefixEnd_2924308 1501575585788249865201359 := by
  unfold tailWord_2924308
  simp only [CollatzResearch.WordTrace]
  refine ⟨53329137544869511444846789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71105516726492681926462385 53329137544869511444846789)
  ·
    refine ⟨9999213289663033395908773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53329137544869511444846789 9999213289663033395908773)
    ·
      refine ⟨1874852491811818761732895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9999213289663033395908773 1874852491811818761732895)
      ·
        refine ⟨2812278737717728142599343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874852491811818761732895 2812278737717728142599343)
        ·
          refine ⟨4218418106576592213899015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2812278737717728142599343 4218418106576592213899015)
          ·
            refine ⟨6327627159864888320848523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4218418106576592213899015 6327627159864888320848523)
            ·
              refine ⟨9491440739797332481272785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6327627159864888320848523 9491440739797332481272785)
              ·
                refine ⟨7118580554847999360954589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9491440739797332481272785 7118580554847999360954589)
                ·
                  refine ⟨2669467708067999760357971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7118580554847999360954589 2669467708067999760357971)
                  ·
                    refine ⟨4004201562101999640536957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2669467708067999760357971 4004201562101999640536957)
                    ·
                      refine ⟨1501575585788249865201359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4004201562101999640536957 1501575585788249865201359)
                      ·
                        rfl

theorem cell23_2924308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2924308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924308 prefixEnd_2924308 := by exact prefixLift 2924308
  have htrace : WordTrace (prefixWord ++ tailWord_2924308) baseStart_2924308 baseEnd_2924308 := by
    simpa [prefixWord, tailWord_2924308, baseEnd_2924308] using wordTrace_append hprefix tailTrace_2924308
  have hstable : (prefixWord ++ tailWord_2924308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924308).length < 2 ^ (prefixWord ++ tailWord_2924308).sum := by decide
  have hdescent : baseEnd_2924308 < baseStart_2924308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924314 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2]
def baseStart_2924314 : Nat := 118140960795 + 2924314 * 2 ^ 59
def prefixEnd_2924314 : Nat := 4983230072969 + 3 ^ 40 * 2924314 * 2
def baseEnd_2924314 : Nat := 1501578666672176841726331

theorem tailTrace_2924314 : CollatzResearch.WordTrace tailWord_2924314 prefixEnd_2924314 1501578666672176841726331 := by
  unfold tailWord_2924314
  simp only [CollatzResearch.WordTrace]
  refine ⟨26664623481929321478602999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71105662618478190609607997 26664623481929321478602999)
  ·
    refine ⟨39996935222893982217904499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26664623481929321478602999 39996935222893982217904499)
    ·
      refine ⟨59995402834340973326856749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39996935222893982217904499 59995402834340973326856749)
      ·
        refine ⟨22498276062877864997571281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59995402834340973326856749 22498276062877864997571281)
        ·
          refine ⟨16873707047158398748178461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22498276062877864997571281 16873707047158398748178461)
          ·
            refine ⟨6327640142684399530566923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16873707047158398748178461 6327640142684399530566923)
            ·
              refine ⟨9491460214026599295850385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6327640142684399530566923 9491460214026599295850385)
              ·
                refine ⟨7118595160519949471887789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9491460214026599295850385 7118595160519949471887789)
                ·
                  refine ⟨2669473185194981051957921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7118595160519949471887789 2669473185194981051957921)
                  ·
                    refine ⟨2002104888896235788968441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2669473185194981051957921 2002104888896235788968441)
                    ·
                      refine ⟨1501578666672176841726331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2002104888896235788968441 1501578666672176841726331)
                      ·
                        rfl

theorem cell23_2924314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_2924314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924314 prefixEnd_2924314 := by exact prefixLift 2924314
  have htrace : WordTrace (prefixWord ++ tailWord_2924314) baseStart_2924314 baseEnd_2924314 := by
    simpa [prefixWord, tailWord_2924314, baseEnd_2924314] using wordTrace_append hprefix tailTrace_2924314
  have hstable : (prefixWord ++ tailWord_2924314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924314).length < 2 ^ (prefixWord ++ tailWord_2924314).sum := by decide
  have hdescent : baseEnd_2924314 < baseStart_2924314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924320 : List Nat := [2, 1, 1, 5, 1, 1, 5, 7]
def baseStart_2924320 : Nat := 118140960795 + 2924320 * 2 ^ 59
def prefixEnd_2924320 : Nat := 4983230072969 + 3 ^ 40 * 2924320 * 2
def baseEnd_2924320 : Nat := 55614138798374215490789

theorem tailTrace_2924320 : CollatzResearch.WordTrace tailWord_2924320 prefixEnd_2924320 55614138798374215490789 := by
  unfold tailWord_2924320
  simp only [CollatzResearch.WordTrace]
  refine ⟨53329356382847774469565207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71105808510463699292753609 53329356382847774469565207)
  ·
    refine ⟨79994034574271661704347811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53329356382847774469565207 79994034574271661704347811)
    ·
      refine ⟨119991051861407492556521717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79994034574271661704347811 119991051861407492556521717)
      ·
        refine ⟨11249161112006952427173911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119991051861407492556521717 11249161112006952427173911)
        ·
          refine ⟨16873741668010428640760867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11249161112006952427173911 16873741668010428640760867)
          ·
            refine ⟨25310612502015642961141301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16873741668010428640760867 25310612502015642961141301)
            ·
              refine ⟨2372869922063966527606997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25310612502015642961141301 2372869922063966527606997)
              ·
                refine ⟨55614138798374215490789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2372869922063966527606997 55614138798374215490789)
                ·
                  rfl

theorem cell23_2924320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 7].length) (baseStart_2924320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924320 prefixEnd_2924320 := by exact prefixLift 2924320
  have htrace : WordTrace (prefixWord ++ tailWord_2924320) baseStart_2924320 baseEnd_2924320 := by
    simpa [prefixWord, tailWord_2924320, baseEnd_2924320] using wordTrace_append hprefix tailTrace_2924320
  have hstable : (prefixWord ++ tailWord_2924320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924320).length < 2 ^ (prefixWord ++ tailWord_2924320).sum := by decide
  have hdescent : baseEnd_2924320 < baseStart_2924320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924341 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 2, 4]
def baseStart_2924341 : Nat := 118140960795 + 2924341 * 2 ^ 59
def prefixEnd_2924341 : Nat := 4983230072969 + 3 ^ 40 * 2924341 * 2
def baseEnd_2924341 : Nat := 500530843549949412029569

theorem tailTrace_2924341 : CollatzResearch.WordTrace tailWord_2924341 prefixEnd_2924341 500530843549949412029569 := by
  unfold tailWord_2924341
  simp only [CollatzResearch.WordTrace]
  refine ⟨106659478698619469525644877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71106319132412979683763251 106659478698619469525644877)
  ·
    refine ⟨39997304511982301072116829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106659478698619469525644877 39997304511982301072116829)
    ·
      refine ⟨14998989191993362902043811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39997304511982301072116829 14998989191993362902043811)
      ·
        refine ⟨22498483787990044353065717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14998989191993362902043811 22498483787990044353065717)
        ·
          refine ⟨2109232855124066658099911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22498483787990044353065717 2109232855124066658099911)
          ·
            refine ⟨3163849282686099987149867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109232855124066658099911 3163849282686099987149867)
            ·
              refine ⟨4745773924029149980724801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163849282686099987149867 4745773924029149980724801)
              ·
                refine ⟨3559330443021862485543601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4745773924029149980724801 3559330443021862485543601)
                ·
                  refine ⟨2669497832266396864157701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3559330443021862485543601 2669497832266396864157701)
                  ·
                    refine ⟨500530843549949412029569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2669497832266396864157701 500530843549949412029569)
                    ·
                      rfl

theorem cell23_2924341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_2924341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924341 prefixEnd_2924341 := by exact prefixLift 2924341
  have htrace : WordTrace (prefixWord ++ tailWord_2924341) baseStart_2924341 baseEnd_2924341 := by
    simpa [prefixWord, tailWord_2924341, baseEnd_2924341] using wordTrace_append hprefix tailTrace_2924341
  have hstable : (prefixWord ++ tailWord_2924341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924341).length < 2 ^ (prefixWord ++ tailWord_2924341).sum := by decide
  have hdescent : baseEnd_2924341 < baseStart_2924341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924343 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_2924343 : Nat := 118140960795 + 2924343 * 2 ^ 59
def prefixEnd_2924343 : Nat := 4983230072969 + 3 ^ 40 * 2924343 * 2
def baseEnd_2924343 : Nat := 1501593557611157228263697

theorem tailTrace_2924343 : CollatzResearch.WordTrace tailWord_2924343 prefixEnd_2924343 1501593557611157228263697 := by
  unfold tailWord_2924343
  simp only [CollatzResearch.WordTrace]
  refine ⟨106659551644612223867217683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71106367763074815911478455 106659551644612223867217683)
  ·
    refine ⟨159989327466918335800826525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106659551644612223867217683 159989327466918335800826525)
    ·
      refine ⟨59995997800094375925309947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159989327466918335800826525 59995997800094375925309947)
      ·
        refine ⟨89993996700141563887964921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59995997800094375925309947 89993996700141563887964921)
        ·
          refine ⟨67495497525106172915973691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89993996700141563887964921 67495497525106172915973691)
          ·
            refine ⟨101243246287659259373960537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67495497525106172915973691 101243246287659259373960537)
            ·
              refine ⟨75932434715744444530470403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101243246287659259373960537 75932434715744444530470403)
              ·
                refine ⟨113898652073616666795705605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75932434715744444530470403 113898652073616666795705605)
                ·
                  refine ⟨21355997263803125024194801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113898652073616666795705605 21355997263803125024194801)
                  ·
                    refine ⟨16016997947852343768146101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21355997263803125024194801 16016997947852343768146101)
                    ·
                      refine ⟨1501593557611157228263697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16016997947852343768146101 1501593557611157228263697)
                      ·
                        rfl

theorem cell23_2924343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_2924343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924343 prefixEnd_2924343 := by exact prefixLift 2924343
  have htrace : WordTrace (prefixWord ++ tailWord_2924343) baseStart_2924343 baseEnd_2924343 := by
    simpa [prefixWord, tailWord_2924343, baseEnd_2924343] using wordTrace_append hprefix tailTrace_2924343
  have hstable : (prefixWord ++ tailWord_2924343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924343).length < 2 ^ (prefixWord ++ tailWord_2924343).sum := by decide
  have hdescent : baseEnd_2924343 < baseStart_2924343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924358 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_2924358 : Nat := 118140960795 + 2924358 * 2 ^ 59
def prefixEnd_2924358 : Nat := 4983230072969 + 3 ^ 40 * 2924358 * 2
def baseEnd_2924358 : Nat := 500533753273658223192043

theorem tailTrace_2924358 : CollatzResearch.WordTrace tailWord_2924358 prefixEnd_2924358 500533753273658223192043 := by
  unfold tailWord_2924358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333128085611183794656679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71106732493038587619342485 3333128085611183794656679)
  ·
    refine ⟨4999692128416775691985019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3333128085611183794656679 4999692128416775691985019)
    ·
      refine ⟨7499538192625163537977529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999692128416775691985019 7499538192625163537977529)
      ·
        refine ⟨5624653644468872653483147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7499538192625163537977529 5624653644468872653483147)
        ·
          refine ⟨8436980466703308980224721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624653644468872653483147 8436980466703308980224721)
          ·
            refine ⟨6327735350027481735168541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8436980466703308980224721 6327735350027481735168541)
            ·
              refine ⟨2372900756260305650688203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6327735350027481735168541 2372900756260305650688203)
              ·
                refine ⟨3559351134390458476032305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2372900756260305650688203 3559351134390458476032305)
                ·
                  refine ⟨2669513350792843857024229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3559351134390458476032305 2669513350792843857024229)
                  ·
                    refine ⟨500533753273658223192043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2669513350792843857024229 500533753273658223192043)
                    ·
                      rfl

theorem cell23_2924358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_2924358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924358 prefixEnd_2924358 := by exact prefixLift 2924358
  have htrace : WordTrace (prefixWord ++ tailWord_2924358) baseStart_2924358 baseEnd_2924358 := by
    simpa [prefixWord, tailWord_2924358, baseEnd_2924358] using wordTrace_append hprefix tailTrace_2924358
  have hstable : (prefixWord ++ tailWord_2924358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924358).length < 2 ^ (prefixWord ++ tailWord_2924358).sum := by decide
  have hdescent : baseEnd_2924358 < baseStart_2924358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924364 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 1, 3, 3]
def baseStart_2924364 : Nat := 118140960795 + 2924364 * 2 ^ 59
def prefixEnd_2924364 : Nat := 4983230072969 + 3 ^ 40 * 2924364 * 2
def baseEnd_2924364 : Nat := 1501604340704901646101101

theorem tailTrace_2924364 : CollatzResearch.WordTrace tailWord_2924364 prefixEnd_2924364 1501604340704901646101101 := by
  unfold tailWord_2924364
  simp only [CollatzResearch.WordTrace]
  refine ⟨53330158788768072226866073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71106878385024096302488097 53330158788768072226866073)
  ·
    refine ⟨39997619091576054170149555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53330158788768072226866073 39997619091576054170149555)
    ·
      refine ⟨59996428637364081255224333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39997619091576054170149555 59996428637364081255224333)
      ·
        refine ⟨22498660739011530470709125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59996428637364081255224333 22498660739011530470709125)
        ·
          refine ⟨4218498888564661963257961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22498660739011530470709125 4218498888564661963257961)
          ·
            refine ⟨3163874166423496472443471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4218498888564661963257961 3163874166423496472443471)
            ·
              refine ⟨4745811249635244708665207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163874166423496472443471 4745811249635244708665207)
              ·
                refine ⟨7118716874452867062997811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4745811249635244708665207 7118716874452867062997811)
                ·
                  refine ⟨10678075311679300594496717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7118716874452867062997811 10678075311679300594496717)
                  ·
                    refine ⟨4004278241879737722936269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10678075311679300594496717 4004278241879737722936269)
                    ·
                      refine ⟨1501604340704901646101101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4004278241879737722936269 1501604340704901646101101)
                      ·
                        rfl

theorem cell23_2924364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_2924364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924364 prefixEnd_2924364 := by exact prefixLift 2924364
  have htrace : WordTrace (prefixWord ++ tailWord_2924364) baseStart_2924364 baseEnd_2924364 := by
    simpa [prefixWord, tailWord_2924364, baseEnd_2924364] using wordTrace_append hprefix tailTrace_2924364
  have hstable : (prefixWord ++ tailWord_2924364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924364).length < 2 ^ (prefixWord ++ tailWord_2924364).sum := by decide
  have hdescent : baseEnd_2924364 < baseStart_2924364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924393 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 9]
def baseStart_2924393 : Nat := 118140960795 + 2924393 * 2 ^ 59
def prefixEnd_2924393 : Nat := 4983230072969 + 3 ^ 40 * 2924393 * 2
def baseEnd_2924393 : Nat := 166846581293764670293163

theorem tailTrace_2924393 : CollatzResearch.WordTrace tailWord_2924393 prefixEnd_2924393 166846581293764670293163 := by
  unfold tailWord_2924393
  simp only [CollatzResearch.WordTrace]
  refine ⟨106661375294431082406537833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71107583529620721604358555 106661375294431082406537833)
  ·
    refine ⟨79996031470823311804903375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106661375294431082406537833 79996031470823311804903375)
    ·
      refine ⟨119994047206234967707355063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79996031470823311804903375 119994047206234967707355063)
      ·
        refine ⟨179991070809352451561032595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119994047206234967707355063 179991070809352451561032595)
        ·
          refine ⟨269986606214028677341548893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179991070809352451561032595 269986606214028677341548893)
          ·
            refine ⟨101244977330260754003080835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269986606214028677341548893 101244977330260754003080835)
            ·
              refine ⟨151867465995391131004621253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101244977330260754003080835 151867465995391131004621253)
              ·
                refine ⟨28475149874135837063366485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151867465995391131004621253 28475149874135837063366485)
                ·
                  refine ⟨166846581293764670293163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28475149874135837063366485 166846581293764670293163)
                  ·
                    rfl

theorem cell23_2924393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 9].length) (baseStart_2924393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924393 prefixEnd_2924393 := by exact prefixLift 2924393
  have htrace : WordTrace (prefixWord ++ tailWord_2924393) baseStart_2924393 baseEnd_2924393 := by
    simpa [prefixWord, tailWord_2924393, baseEnd_2924393] using wordTrace_append hprefix tailTrace_2924393
  have hstable : (prefixWord ++ tailWord_2924393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924393).length < 2 ^ (prefixWord ++ tailWord_2924393).sum := by decide
  have hdescent : baseEnd_2924393 < baseStart_2924393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924403 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 9]
def baseStart_2924403 : Nat := 118140960795 + 2924403 * 2 ^ 59
def prefixEnd_2924403 : Nat := 4983230072969 + 3 ^ 40 * 2924403 * 2
def baseEnd_2924403 : Nat := 1501624366450426993513421

theorem tailTrace_2924403 : CollatzResearch.WordTrace tailWord_2924403 prefixEnd_2924403 1501624366450426993513421 := by
  unfold tailWord_2924403
  simp only [CollatzResearch.WordTrace]
  refine ⟨106661740024394854114401863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71107826682929902742934575 106661740024394854114401863)
  ·
    refine ⟨159992610036592281171602795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106661740024394854114401863 159992610036592281171602795)
    ·
      refine ⟨239988915054888421757404193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159992610036592281171602795 239988915054888421757404193)
      ·
        refine ⟨179991686291166316318053145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239988915054888421757404193 179991686291166316318053145)
        ·
          refine ⟨134993764718374737238539859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179991686291166316318053145 134993764718374737238539859)
          ·
            refine ⟨202490647077562105857809789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134993764718374737238539859 202490647077562105857809789)
            ·
              refine ⟨75933992654085789696678671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202490647077562105857809789 75933992654085789696678671)
              ·
                refine ⟨113900988981128684545018007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75933992654085789696678671 113900988981128684545018007)
                ·
                  refine ⟨170851483471693026817527011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113900988981128684545018007 170851483471693026817527011)
                  ·
                    refine ⟨256277225207539540226290517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170851483471693026817527011 256277225207539540226290517)
                    ·
                      refine ⟨1501624366450426993513421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 256277225207539540226290517 1501624366450426993513421)
                      ·
                        rfl

theorem cell23_2924403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_2924403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924403 prefixEnd_2924403 := by exact prefixLift 2924403
  have htrace : WordTrace (prefixWord ++ tailWord_2924403) baseStart_2924403 baseEnd_2924403 := by
    simpa [prefixWord, tailWord_2924403, baseEnd_2924403] using wordTrace_append hprefix tailTrace_2924403
  have hstable : (prefixWord ++ tailWord_2924403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924403).length < 2 ^ (prefixWord ++ tailWord_2924403).sum := by decide
  have hdescent : baseEnd_2924403 < baseStart_2924403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924410 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 7]
def baseStart_2924410 : Nat := 118140960795 + 2924410 * 2 ^ 59
def prefixEnd_2924410 : Nat := 4983230072969 + 3 ^ 40 * 2924410 * 2
def baseEnd_2924410 : Nat := 166847551201667607347321

theorem tailTrace_2924410 : CollatzResearch.WordTrace tailWord_2924410 prefixEnd_2924410 166847551201667607347321 := by
  unfold tailWord_2924410
  simp only [CollatzResearch.WordTrace]
  refine ⟨26665498833842373577476671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71107996890246329539937789 26665498833842373577476671)
  ·
    refine ⟨39998248250763560366215007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26665498833842373577476671 39998248250763560366215007)
    ·
      refine ⟨59997372376145340549322511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39998248250763560366215007 59997372376145340549322511)
      ·
        refine ⟨89996058564218010823983767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59997372376145340549322511 89996058564218010823983767)
        ·
          refine ⟨134994087846327016235975651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89996058564218010823983767 134994087846327016235975651)
          ·
            refine ⟨202491131769490524353963477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134994087846327016235975651 202491131769490524353963477)
            ·
              refine ⟨4745885900847434164546019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 202491131769490524353963477 4745885900847434164546019)
              ·
                refine ⟨7118828851271151246819029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4745885900847434164546019 7118828851271151246819029)
                ·
                  refine ⟨166847551201667607347321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7118828851271151246819029 166847551201667607347321)
                  ·
                    rfl

theorem cell23_2924410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_2924410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924410 prefixEnd_2924410 := by exact prefixLift 2924410
  have htrace : WordTrace (prefixWord ++ tailWord_2924410) baseStart_2924410 baseEnd_2924410 := by
    simpa [prefixWord, tailWord_2924410, baseEnd_2924410] using wordTrace_append hprefix tailTrace_2924410
  have hstable : (prefixWord ++ tailWord_2924410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924410).length < 2 ^ (prefixWord ++ tailWord_2924410).sum := by decide
  have hdescent : baseEnd_2924410 < baseStart_2924410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924497 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 2, 2, 3]
def baseStart_2924497 : Nat := 118140960795 + 2924497 * 2 ^ 59
def prefixEnd_2924497 : Nat := 4983230072969 + 3 ^ 40 * 2924497 * 2
def baseEnd_2924497 : Nat := 1501672633631949625737989

theorem tailTrace_2924497 : CollatzResearch.WordTrace tailWord_2924497 prefixEnd_2924497 1501672633631949625737989 := by
  unfold tailWord_2924497
  simp only [CollatzResearch.WordTrace]
  refine ⟨106665168486054308168323745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71110112324036205445549163 106665168486054308168323745)
  ·
    refine ⟨79998876364540731126242809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106665168486054308168323745 79998876364540731126242809)
    ·
      refine ⟨59999157273405548344682107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79998876364540731126242809 59999157273405548344682107)
      ·
        refine ⟨89998735910108322517023161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59999157273405548344682107 89998735910108322517023161)
        ·
          refine ⟨67499051932581241887767371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89998735910108322517023161 67499051932581241887767371)
          ·
            refine ⟨101248577898871862831651057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67499051932581241887767371 101248577898871862831651057)
            ·
              refine ⟨75936433424153897123738293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101248577898871862831651057 75936433424153897123738293)
              ·
                refine ⟨7119040633514427855350465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75936433424153897123738293 7119040633514427855350465)
                ·
                  refine ⟨5339280475135820891512849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7119040633514427855350465 5339280475135820891512849)
                  ·
                    refine ⟨4004460356351865668634637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5339280475135820891512849 4004460356351865668634637)
                    ·
                      refine ⟨1501672633631949625737989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4004460356351865668634637 1501672633631949625737989)
                      ·
                        rfl

theorem cell23_2924497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_2924497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924497 prefixEnd_2924497 := by exact prefixLift 2924497
  have htrace : WordTrace (prefixWord ++ tailWord_2924497) baseStart_2924497 baseEnd_2924497 := by
    simpa [prefixWord, tailWord_2924497, baseEnd_2924497] using wordTrace_append hprefix tailTrace_2924497
  have hstable : (prefixWord ++ tailWord_2924497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924497).length < 2 ^ (prefixWord ++ tailWord_2924497).sum := by decide
  have hdescent : baseEnd_2924497 < baseStart_2924497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924597 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_2924597 : Nat := 118140960795 + 2924597 * 2 ^ 59
def prefixEnd_2924597 : Nat := 4983230072969 + 3 ^ 40 * 2924597 * 2
def baseEnd_2924597 : Nat := 1501723981697399234487529

theorem tailTrace_2924597 : CollatzResearch.WordTrace tailWord_2924597 prefixEnd_2924597 1501723981697399234487529 := by
  unfold tailWord_2924597
  simp only [CollatzResearch.WordTrace]
  refine ⟨106668815785692025246964045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71112543857128016831309363 106668815785692025246964045)
  ·
    refine ⟨40000805919634509467611517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106668815785692025246964045 40000805919634509467611517)
    ·
      refine ⟨15000302219862941050354319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40000805919634509467611517 15000302219862941050354319)
      ·
        refine ⟨22500453329794411575531479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15000302219862941050354319 22500453329794411575531479)
        ·
          refine ⟨33750679994691617363297219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22500453329794411575531479 33750679994691617363297219)
          ·
            refine ⟨50626019992037426044945829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33750679994691617363297219 50626019992037426044945829)
            ·
              refine ⟨9492378748507017383427343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50626019992037426044945829 9492378748507017383427343)
              ·
                refine ⟨14238568122760526075141015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9492378748507017383427343 14238568122760526075141015)
                ·
                  refine ⟨21357852184140789112711523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14238568122760526075141015 21357852184140789112711523)
                  ·
                    refine ⟨32036778276211183669067285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21357852184140789112711523 32036778276211183669067285)
                    ·
                      refine ⟨1501723981697399234487529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32036778276211183669067285 1501723981697399234487529)
                      ·
                        rfl

theorem cell23_2924597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_2924597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924597 prefixEnd_2924597 := by exact prefixLift 2924597
  have htrace : WordTrace (prefixWord ++ tailWord_2924597) baseStart_2924597 baseEnd_2924597 := by
    simpa [prefixWord, tailWord_2924597, baseEnd_2924597] using wordTrace_append hprefix tailTrace_2924597
  have hstable : (prefixWord ++ tailWord_2924597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924597).length < 2 ^ (prefixWord ++ tailWord_2924597).sum := by decide
  have hdescent : baseEnd_2924597 < baseStart_2924597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924604 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_2924604 : Nat := 118140960795 + 2924604 * 2 ^ 59
def prefixEnd_2924604 : Nat := 4983230072969 + 3 ^ 40 * 2924604 * 2
def baseEnd_2924604 : Nat := 1501727576061980707099997

theorem tailTrace_2924604 : CollatzResearch.WordTrace tailWord_2924604 prefixEnd_2924604 1501727576061980707099997 := by
  unfold tailWord_2924604
  simp only [CollatzResearch.WordTrace]
  refine ⟨53334535548333332721234433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71112714064444443628312577 53334535548333332721234433)
  ·
    refine ⟨40000901661249999540925825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53334535548333332721234433 40000901661249999540925825)
    ·
      refine ⟨30000676245937499655694369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40000901661249999540925825 30000676245937499655694369)
      ·
        refine ⟨22500507184453124741770777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30000676245937499655694369 22500507184453124741770777)
        ·
          refine ⟨16875380388339843556328083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22500507184453124741770777 16875380388339843556328083)
          ·
            refine ⟨25313070582509765334492125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16875380388339843556328083 25313070582509765334492125)
            ·
              refine ⟨9492401468441162000434547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25313070582509765334492125 9492401468441162000434547)
              ·
                refine ⟨14238602202661743000651821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9492401468441162000434547 14238602202661743000651821)
                ·
                  refine ⟨5339475825998153625244433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14238602202661743000651821 5339475825998153625244433)
                  ·
                    refine ⟨4004606869498615218933325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5339475825998153625244433 4004606869498615218933325)
                    ·
                      refine ⟨1501727576061980707099997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4004606869498615218933325 1501727576061980707099997)
                      ·
                        rfl

theorem cell23_2924604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_2924604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924604 prefixEnd_2924604 := by exact prefixLift 2924604
  have htrace : WordTrace (prefixWord ++ tailWord_2924604) baseStart_2924604 baseEnd_2924604 := by
    simpa [prefixWord, tailWord_2924604, baseEnd_2924604] using wordTrace_append hprefix tailTrace_2924604
  have hstable : (prefixWord ++ tailWord_2924604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924604).length < 2 ^ (prefixWord ++ tailWord_2924604).sum := by decide
  have hdescent : baseEnd_2924604 < baseStart_2924604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924618 : List Nat := [3, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2]
def baseStart_2924618 : Nat := 118140960795 + 2924618 * 2 ^ 59
def prefixEnd_2924618 : Nat := 4983230072969 + 3 ^ 40 * 2924618 * 2
def baseEnd_2924618 : Nat := 1501734764791143652324933

theorem tailTrace_2924618 : CollatzResearch.WordTrace tailWord_2924618 prefixEnd_2924618 1501734764791143652324933 := by
  unfold tailWord_2924618
  simp only [CollatzResearch.WordTrace]
  refine ⟨26667395429653986458369627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71113054479077297222319005 26667395429653986458369627)
  ·
    refine ⟨40001093144480979687554441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26667395429653986458369627 40001093144480979687554441)
    ·
      refine ⟨30000819858360734765665831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40001093144480979687554441 30000819858360734765665831)
      ·
        refine ⟨45001229787541102148498747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30000819858360734765665831 45001229787541102148498747)
        ·
          refine ⟨67501844681311653222748121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45001229787541102148498747 67501844681311653222748121)
          ·
            refine ⟨50626383510983739917061091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67501844681311653222748121 50626383510983739917061091)
            ·
              refine ⟨75939575266475609875591637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50626383510983739917061091 75939575266475609875591637)
              ·
                refine ⟨1779833795308022106459179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 75939575266475609875591637 1779833795308022106459179)
                ·
                  refine ⟨2669750692962033159688769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779833795308022106459179 2669750692962033159688769)
                  ·
                    refine ⟨2002313019721524869766577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2669750692962033159688769 2002313019721524869766577)
                    ·
                      refine ⟨1501734764791143652324933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2002313019721524869766577 1501734764791143652324933)
                      ·
                        rfl

theorem cell23_2924618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_2924618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924618 prefixEnd_2924618 := by exact prefixLift 2924618
  have htrace : WordTrace (prefixWord ++ tailWord_2924618) baseStart_2924618 baseEnd_2924618 := by
    simpa [prefixWord, tailWord_2924618, baseEnd_2924618] using wordTrace_append hprefix tailTrace_2924618
  have hstable : (prefixWord ++ tailWord_2924618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924618).length < 2 ^ (prefixWord ++ tailWord_2924618).sum := by decide
  have hdescent : baseEnd_2924618 < baseStart_2924618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924657 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_2924657 : Nat := 118140960795 + 2924657 * 2 ^ 59
def prefixEnd_2924657 : Nat := 4983230072969 + 3 ^ 40 * 2924657 * 2
def baseEnd_2924657 : Nat := 1501754790536668999737253

theorem tailTrace_2924657 : CollatzResearch.WordTrace tailWord_2924657 prefixEnd_2924657 1501754790536668999737253 := by
  unfold tailWord_2924657
  simp only [CollatzResearch.WordTrace]
  refine ⟨106671004165474655494148225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71114002776983103662765483 106671004165474655494148225)
  ·
    refine ⟨80003253124105991620611169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106671004165474655494148225 80003253124105991620611169)
    ·
      refine ⟨60002439843079493715458377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80003253124105991620611169 60002439843079493715458377)
      ·
        refine ⟨45001829882309620286593783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60002439843079493715458377 45001829882309620286593783)
        ·
          refine ⟨67502744823464430429890675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45001829882309620286593783 67502744823464430429890675)
          ·
            refine ⟨101254117235196645644836013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67502744823464430429890675 101254117235196645644836013)
            ·
              refine ⟨37970293963198742116813505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101254117235196645644836013 37970293963198742116813505)
              ·
                refine ⟨28477720472399056587610129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37970293963198742116813505 28477720472399056587610129)
                ·
                  refine ⟨21358290354299292440707597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28477720472399056587610129 21358290354299292440707597)
                  ·
                    refine ⟨8009358882862234665265349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21358290354299292440707597 8009358882862234665265349)
                    ·
                      refine ⟨1501754790536668999737253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8009358882862234665265349 1501754790536668999737253)
                      ·
                        rfl

theorem cell23_2924657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_2924657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924657 prefixEnd_2924657 := by exact prefixLift 2924657
  have htrace : WordTrace (prefixWord ++ tailWord_2924657) baseStart_2924657 baseEnd_2924657 := by
    simpa [prefixWord, tailWord_2924657, baseEnd_2924657] using wordTrace_append hprefix tailTrace_2924657
  have hstable : (prefixWord ++ tailWord_2924657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924657).length < 2 ^ (prefixWord ++ tailWord_2924657).sum := by decide
  have hdescent : baseEnd_2924657 < baseStart_2924657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924702 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_2924702 : Nat := 118140960795 + 2924702 * 2 ^ 59
def prefixEnd_2924702 : Nat := 4983230072969 + 3 ^ 40 * 2924702 * 2
def baseEnd_2924702 : Nat := 1501777897166121323674547

theorem tailTrace_2924702 : CollatzResearch.WordTrace tailWord_2924702 prefixEnd_2924702 1501777897166121323674547 := by
  unfold tailWord_2924702
  simp only [CollatzResearch.WordTrace]
  refine ⟨13334080681288953522442045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71115096966874418786357573 13334080681288953522442045)
  ·
    refine ⟨5000280255483357570915767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13334080681288953522442045 5000280255483357570915767)
    ·
      refine ⟨7500420383225036356373651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5000280255483357570915767 7500420383225036356373651)
      ·
        refine ⟨11250630574837554534560477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7500420383225036356373651 11250630574837554534560477)
        ·
          refine ⟨4218986465564082950460179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11250630574837554534560477 4218986465564082950460179)
          ·
            refine ⟨6328479698346124425690269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4218986465564082950460179 6328479698346124425690269)
            ·
              refine ⟨2373179886879796659633851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6328479698346124425690269 2373179886879796659633851)
              ·
                refine ⟨3559769830319694989450777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373179886879796659633851 3559769830319694989450777)
                ·
                  refine ⟨2669827372739771242088083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3559769830319694989450777 2669827372739771242088083)
                  ·
                    refine ⟨4004741059109656863132125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2669827372739771242088083 4004741059109656863132125)
                    ·
                      refine ⟨1501777897166121323674547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4004741059109656863132125 1501777897166121323674547)
                      ·
                        rfl

theorem cell23_2924702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_2924702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924702 prefixEnd_2924702 := by exact prefixLift 2924702
  have htrace : WordTrace (prefixWord ++ tailWord_2924702) baseStart_2924702 baseEnd_2924702 := by
    simpa [prefixWord, tailWord_2924702, baseEnd_2924702] using wordTrace_append hprefix tailTrace_2924702
  have hstable : (prefixWord ++ tailWord_2924702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924702).length < 2 ^ (prefixWord ++ tailWord_2924702).sum := by decide
  have hdescent : baseEnd_2924702 < baseStart_2924702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924704 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 4]
def baseStart_2924704 : Nat := 118140960795 + 2924704 * 2 ^ 59
def prefixEnd_2924704 : Nat := 4983230072969 + 3 ^ 40 * 2924704 * 2
def baseEnd_2924704 : Nat := 1501778924127430315849537

theorem tailTrace_2924704 : CollatzResearch.WordTrace tailWord_2924704 prefixEnd_2924704 1501778924127430315849537 := by
  unfold tailWord_2924704
  simp only [CollatzResearch.WordTrace]
  refine ⟨53336359198152191260554583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71115145597536255014072777 53336359198152191260554583)
  ·
    refine ⟨80004538797228286890831875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53336359198152191260554583 80004538797228286890831875)
    ·
      refine ⟨120006808195842430336247813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80004538797228286890831875 120006808195842430336247813)
      ·
        refine ⟨22501276536720455688046465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120006808195842430336247813 22501276536720455688046465)
        ·
          refine ⟨16875957402540341766034849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22501276536720455688046465 16875957402540341766034849)
          ·
            refine ⟨12656968051905256324526137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16875957402540341766034849 12656968051905256324526137)
            ·
              refine ⟨9492726038928942243394603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12656968051905256324526137 9492726038928942243394603)
              ·
                refine ⟨14239089058393413365091905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9492726038928942243394603 14239089058393413365091905)
                ·
                  refine ⟨10679316793795060023818929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14239089058393413365091905 10679316793795060023818929)
                  ·
                    refine ⟨8009487595346295017864197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10679316793795060023818929 8009487595346295017864197)
                    ·
                      refine ⟨1501778924127430315849537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8009487595346295017864197 1501778924127430315849537)
                      ·
                        rfl

theorem cell23_2924704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_2924704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924704 prefixEnd_2924704 := by exact prefixLift 2924704
  have htrace : WordTrace (prefixWord ++ tailWord_2924704) baseStart_2924704 baseEnd_2924704 := by
    simpa [prefixWord, tailWord_2924704, baseEnd_2924704] using wordTrace_append hprefix tailTrace_2924704
  have hstable : (prefixWord ++ tailWord_2924704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924704).length < 2 ^ (prefixWord ++ tailWord_2924704).sum := by decide
  have hdescent : baseEnd_2924704 < baseStart_2924704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924748 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 7]
def baseStart_2924748 : Nat := 118140960795 + 2924748 * 2 ^ 59
def prefixEnd_2924748 : Nat := 4983230072969 + 3 ^ 40 * 2924748 * 2
def baseEnd_2924748 : Nat := 166866835252914238188815

theorem tailTrace_2924748 : CollatzResearch.WordTrace tailWord_2924748 prefixEnd_2924748 166866835252914238188815 := by
  unfold tailWord_2924748
  simp only [CollatzResearch.WordTrace]
  refine ⟨53337161604072489017855449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71116215472096652023807265 53337161604072489017855449)
  ·
    refine ⟨40002871203054366763391587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53337161604072489017855449 40002871203054366763391587)
    ·
      refine ⟨60004306804581550145087381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40002871203054366763391587 60004306804581550145087381)
      ·
        refine ⟨2812701881464760163050971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60004306804581550145087381 2812701881464760163050971)
        ·
          refine ⟨4219052822197140244576457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2812701881464760163050971 4219052822197140244576457)
          ·
            refine ⟨3164289616647855183432343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4219052822197140244576457 3164289616647855183432343)
            ·
              refine ⟨4746434424971782775148515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164289616647855183432343 4746434424971782775148515)
              ·
                refine ⟨7119651637457674162722773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4746434424971782775148515 7119651637457674162722773)
                ·
                  refine ⟨166866835252914238188815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7119651637457674162722773 166866835252914238188815)
                  ·
                    rfl

theorem cell23_2924748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_2924748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924748 prefixEnd_2924748 := by exact prefixLift 2924748
  have htrace : WordTrace (prefixWord ++ tailWord_2924748) baseStart_2924748 baseEnd_2924748 := by
    simpa [prefixWord, tailWord_2924748, baseEnd_2924748] using wordTrace_append hprefix tailTrace_2924748
  have hstable : (prefixWord ++ tailWord_2924748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924748).length < 2 ^ (prefixWord ++ tailWord_2924748).sum := by decide
  have hdescent : baseEnd_2924748 < baseStart_2924748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924754 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2924754 : Nat := 118140960795 + 2924754 * 2 ^ 59
def prefixEnd_2924754 : Nat := 4983230072969 + 3 ^ 40 * 2924754 * 2
def baseEnd_2924754 : Nat := 1501804598160155120224307

theorem tailTrace_2924754 : CollatzResearch.WordTrace tailWord_2924754 prefixEnd_2924754 1501804598160155120224307 := by
  unfold tailWord_2924754
  simp only [CollatzResearch.WordTrace]
  refine ⟨26668635511530810265107329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71116361364082160706952877 26668635511530810265107329)
  ·
    refine ⟨20001476633648107698830497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26668635511530810265107329 20001476633648107698830497)
    ·
      refine ⟨15001107475236080774122873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20001476633648107698830497 15001107475236080774122873)
      ·
        refine ⟨11250830606427060580592155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15001107475236080774122873 11250830606427060580592155)
        ·
          refine ⟨16876245909640590870888233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11250830606427060580592155 16876245909640590870888233)
          ·
            refine ⟨12657184432230443153166175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16876245909640590870888233 12657184432230443153166175)
            ·
              refine ⟨18985776648345664729749263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12657184432230443153166175 18985776648345664729749263)
              ·
                refine ⟨28478664972518497094623895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18985776648345664729749263 28478664972518497094623895)
                ·
                  refine ⟨42717997458777745641935843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28478664972518497094623895 42717997458777745641935843)
                  ·
                    refine ⟨64076996188166618462903765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42717997458777745641935843 64076996188166618462903765)
                    ·
                      refine ⟨1501804598160155120224307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64076996188166618462903765 1501804598160155120224307)
                      ·
                        rfl

theorem cell23_2924754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2924754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924754 prefixEnd_2924754 := by exact prefixLift 2924754
  have htrace : WordTrace (prefixWord ++ tailWord_2924754) baseStart_2924754 baseEnd_2924754 := by
    simpa [prefixWord, tailWord_2924754, baseEnd_2924754] using wordTrace_append hprefix tailTrace_2924754
  have hstable : (prefixWord ++ tailWord_2924754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924754).length < 2 ^ (prefixWord ++ tailWord_2924754).sum := by decide
  have hdescent : baseEnd_2924754 < baseStart_2924754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924784 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 3]
def baseStart_2924784 : Nat := 118140960795 + 2924784 * 2 ^ 59
def prefixEnd_2924784 : Nat := 4983230072969 + 3 ^ 40 * 2924784 * 2
def baseEnd_2924784 : Nat := 1501820002579790002849169

theorem tailTrace_2924784 : CollatzResearch.WordTrace tailWord_2924784 prefixEnd_2924784 1501820002579790002849169 := by
  unfold tailWord_2924784
  simp only [CollatzResearch.WordTrace]
  refine ⟨53337818118007278092010703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71117090824009704122680937 53337818118007278092010703)
  ·
    refine ⟨80006727177010917138016055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53337818118007278092010703 80006727177010917138016055)
    ·
      refine ⟨120010090765516375707024083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80006727177010917138016055 120010090765516375707024083)
      ·
        refine ⟨180015136148274563560536125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120010090765516375707024083 180015136148274563560536125)
        ·
          refine ⟨67505676055602961335201047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180015136148274563560536125 67505676055602961335201047)
          ·
            refine ⟨101258514083404442002801571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67505676055602961335201047 101258514083404442002801571)
            ·
              refine ⟨151887771125106663004202357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101258514083404442002801571 151887771125106663004202357)
              ·
                refine ⟨14239478542978749656643971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151887771125106663004202357 14239478542978749656643971)
                ·
                  refine ⟨21359217814468124484965957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14239478542978749656643971 21359217814468124484965957)
                  ·
                    refine ⟨4004853340212773340931117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21359217814468124484965957 4004853340212773340931117)
                    ·
                      refine ⟨1501820002579790002849169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4004853340212773340931117 1501820002579790002849169)
                      ·
                        rfl

theorem cell23_2924784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 3].length) (baseStart_2924784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924784 prefixEnd_2924784 := by exact prefixLift 2924784
  have htrace : WordTrace (prefixWord ++ tailWord_2924784) baseStart_2924784 baseEnd_2924784 := by
    simpa [prefixWord, tailWord_2924784, baseEnd_2924784] using wordTrace_append hprefix tailTrace_2924784
  have hstable : (prefixWord ++ tailWord_2924784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924784).length < 2 ^ (prefixWord ++ tailWord_2924784).sum := by decide
  have hdescent : baseEnd_2924784 < baseStart_2924784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924798 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_2924798 : Nat := 118140960795 + 2924798 * 2 ^ 59
def prefixEnd_2924798 : Nat := 4983230072969 + 3 ^ 40 * 2924798 * 2
def baseEnd_2924798 : Nat := 1501827191308952948074105

theorem tailTrace_2924798 : CollatzResearch.WordTrace tailWord_2924798 prefixEnd_2924798 1501827191308952948074105 := by
  unfold tailWord_2924798
  simp only [CollatzResearch.WordTrace]
  refine ⟨13334518357245479571878881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71117431238642557716687365 13334518357245479571878881)
  ·
    refine ⟨10000888767934109678909161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13334518357245479571878881 10000888767934109678909161)
    ·
      refine ⟨7500666575950582259181871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10000888767934109678909161 7500666575950582259181871)
      ·
        refine ⟨11250999863925873388772807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7500666575950582259181871 11250999863925873388772807)
        ·
          refine ⟨16876499795888810083159211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11250999863925873388772807 16876499795888810083159211)
          ·
            refine ⟨25314749693833215124738817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16876499795888810083159211 25314749693833215124738817)
            ·
              refine ⟨18986062270374911343554113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25314749693833215124738817 18986062270374911343554113)
              ·
                refine ⟨14239546702781183507665585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18986062270374911343554113 14239546702781183507665585)
                ·
                  refine ⟨10679660027085887630749189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14239546702781183507665585 10679660027085887630749189)
                  ·
                    refine ⟨2002436255078603930765473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10679660027085887630749189 2002436255078603930765473)
                    ·
                      refine ⟨1501827191308952948074105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2002436255078603930765473 1501827191308952948074105)
                      ·
                        rfl

theorem cell23_2924798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_2924798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924798 prefixEnd_2924798 := by exact prefixLift 2924798
  have htrace : WordTrace (prefixWord ++ tailWord_2924798) baseStart_2924798 baseEnd_2924798 := by
    simpa [prefixWord, tailWord_2924798, baseEnd_2924798] using wordTrace_append hprefix tailTrace_2924798
  have hstable : (prefixWord ++ tailWord_2924798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924798).length < 2 ^ (prefixWord ++ tailWord_2924798).sum := by decide
  have hdescent : baseEnd_2924798 < baseStart_2924798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924801 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_2924801 : Nat := 118140960795 + 2924801 * 2 ^ 59
def prefixEnd_2924801 : Nat := 4983230072969 + 3 ^ 40 * 2924801 * 2
def baseEnd_2924801 : Nat := 1501828731750916436336591

theorem tailTrace_2924801 : CollatzResearch.WordTrace tailWord_2924801 prefixEnd_2924801 1501828731750916436336591 := by
  unfold tailWord_2924801
  simp only [CollatzResearch.WordTrace]
  refine ⟨106676256276952968087390257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71117504184635312058260171 106676256276952968087390257)
  ·
    refine ⟨80007192207714726065542693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106676256276952968087390257 80007192207714726065542693)
    ·
      refine ⟨15001348538946511137289255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80007192207714726065542693 15001348538946511137289255)
      ·
        refine ⟨22502022808419766705933883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15001348538946511137289255 22502022808419766705933883)
        ·
          refine ⟨33753034212629650058900825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22502022808419766705933883 33753034212629650058900825)
          ·
            refine ⟨25314775659472237544175619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33753034212629650058900825 25314775659472237544175619)
            ·
              refine ⟨37972163489208356316263429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25314775659472237544175619 37972163489208356316263429)
              ·
                refine ⟨7119780654226566809299393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37972163489208356316263429 7119780654226566809299393)
                ·
                  refine ⟨5339835490669925106974545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7119780654226566809299393 5339835490669925106974545)
                  ·
                    refine ⟨4004876618002443830230909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5339835490669925106974545 4004876618002443830230909)
                    ·
                      refine ⟨1501828731750916436336591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4004876618002443830230909 1501828731750916436336591)
                      ·
                        rfl

theorem cell23_2924801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_2924801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924801 prefixEnd_2924801 := by exact prefixLift 2924801
  have htrace : WordTrace (prefixWord ++ tailWord_2924801) baseStart_2924801 baseEnd_2924801 := by
    simpa [prefixWord, tailWord_2924801, baseEnd_2924801] using wordTrace_append hprefix tailTrace_2924801
  have hstable : (prefixWord ++ tailWord_2924801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924801).length < 2 ^ (prefixWord ++ tailWord_2924801).sum := by decide
  have hdescent : baseEnd_2924801 < baseStart_2924801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924842 : List Nat := [3, 1, 4, 2, 2, 1, 2, 3, 1, 4]
def baseStart_2924842 : Nat := 118140960795 + 2924842 * 2 ^ 59
def prefixEnd_2924842 : Nat := 4983230072969 + 3 ^ 40 * 2924842 * 2
def baseEnd_2924842 : Nat := 500616594819250258641301

theorem tailTrace_2924842 : CollatzResearch.WordTrace tailWord_2924842 prefixEnd_2924842 500616594819250258641301 := by
  unfold tailWord_2924842
  simp only [CollatzResearch.WordTrace]
  refine ⟨26669437917451108022408195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71118501113202954726421853 26669437917451108022408195)
  ·
    refine ⟨40004156876176662033612293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26669437917451108022408195 40004156876176662033612293)
    ·
      refine ⟨7500779414283124131302305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40004156876176662033612293 7500779414283124131302305)
      ·
        refine ⟨5625584560712343098476729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7500779414283124131302305 5625584560712343098476729)
        ·
          refine ⟨4219188420534257323857547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5625584560712343098476729 4219188420534257323857547)
          ·
            refine ⟨6328782630801385985786321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4219188420534257323857547 6328782630801385985786321)
            ·
              refine ⟨4746586973101039489339741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6328782630801385985786321 4746586973101039489339741)
              ·
                refine ⟨1779970114912889808502403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4746586973101039489339741 1779970114912889808502403)
                ·
                  refine ⟨2669955172369334712753605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779970114912889808502403 2669955172369334712753605)
                  ·
                    refine ⟨500616594819250258641301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2669955172369334712753605 500616594819250258641301)
                    ·
                      rfl

theorem cell23_2924842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_2924842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924842 prefixEnd_2924842 := by exact prefixLift 2924842
  have htrace : WordTrace (prefixWord ++ tailWord_2924842) baseStart_2924842 baseEnd_2924842 := by
    simpa [prefixWord, tailWord_2924842, baseEnd_2924842] using wordTrace_append hprefix tailTrace_2924842
  have hstable : (prefixWord ++ tailWord_2924842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924842).length < 2 ^ (prefixWord ++ tailWord_2924842).sum := by decide
  have hdescent : baseEnd_2924842 < baseStart_2924842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924851 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 1, 5]
def baseStart_2924851 : Nat := 118140960795 + 2924851 * 2 ^ 59
def prefixEnd_2924851 : Nat := 4983230072969 + 3 ^ 40 * 2924851 * 2
def baseEnd_2924851 : Nat := 500618135261213746903787

theorem tailTrace_2924851 : CollatzResearch.WordTrace tailWord_2924851 prefixEnd_2924851 500618135261213746903787 := by
  unfold tailWord_2924851
  simp only [CollatzResearch.WordTrace]
  refine ⟨106678079926771826626710407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71118719951181217751140271 106678079926771826626710407)
  ·
    refine ⟨160017119890157739940065611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106678079926771826626710407 160017119890157739940065611)
    ·
      refine ⟨240025679835236609910098417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160017119890157739940065611 240025679835236609910098417)
      ·
        refine ⟨180019259876427457432573813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240025679835236609910098417 180019259876427457432573813)
        ·
          refine ⟨16876805613415074134303795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180019259876427457432573813 16876805613415074134303795)
          ·
            refine ⟨25315208420122611201455693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16876805613415074134303795 25315208420122611201455693)
            ·
              refine ⟨9493203157545979200545885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25315208420122611201455693 9493203157545979200545885)
              ·
                refine ⟨3559951184079742200204707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9493203157545979200545885 3559951184079742200204707)
                ·
                  refine ⟨5339926776119613300307061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559951184079742200204707 5339926776119613300307061)
                  ·
                    refine ⟨500618135261213746903787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5339926776119613300307061 500618135261213746903787)
                    ·
                      rfl

theorem cell23_2924851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 5].length) (baseStart_2924851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924851 prefixEnd_2924851 := by exact prefixLift 2924851
  have htrace : WordTrace (prefixWord ++ tailWord_2924851) baseStart_2924851 baseEnd_2924851 := by
    simpa [prefixWord, tailWord_2924851, baseEnd_2924851] using wordTrace_append hprefix tailTrace_2924851
  have hstable : (prefixWord ++ tailWord_2924851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924851).length < 2 ^ (prefixWord ++ tailWord_2924851).sum := by decide
  have hdescent : baseEnd_2924851 < baseStart_2924851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924881 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 1, 6]
def baseStart_2924881 : Nat := 118140960795 + 2924881 * 2 ^ 59
def prefixEnd_2924881 : Nat := 4983230072969 + 3 ^ 40 * 2924881 * 2
def baseEnd_2924881 : Nat := 500623270067758707778741

theorem tailTrace_2924881 : CollatzResearch.WordTrace tailWord_2924881 prefixEnd_2924881 500623270067758707778741 := by
  unfold tailWord_2924881
  simp only [CollatzResearch.WordTrace]
  refine ⟨106679174116663141750302497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71119449411108761166868331 106679174116663141750302497)
  ·
    refine ⟨80009380587497356312726873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106679174116663141750302497 80009380587497356312726873)
    ·
      refine ⟨60007035440623017234545155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80009380587497356312726873 60007035440623017234545155)
      ·
        refine ⟨90010553160934525851817733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60007035440623017234545155 90010553160934525851817733)
        ·
          refine ⟨16876978717675223597215825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90010553160934525851817733 16876978717675223597215825)
          ·
            refine ⟨12657734038256417697911869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16876978717675223597215825 12657734038256417697911869)
            ·
              refine ⟨4746650264346156636716951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12657734038256417697911869 4746650264346156636716951)
              ·
                refine ⟨7119975396519234955075427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4746650264346156636716951 7119975396519234955075427)
                ·
                  refine ⟨10679963094778852432613141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7119975396519234955075427 10679963094778852432613141)
                  ·
                    refine ⟨500623270067758707778741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10679963094778852432613141 500623270067758707778741)
                    ·
                      rfl

theorem cell23_2924881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_2924881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924881 prefixEnd_2924881 := by exact prefixLift 2924881
  have htrace : WordTrace (prefixWord ++ tailWord_2924881) baseStart_2924881 baseEnd_2924881 := by
    simpa [prefixWord, tailWord_2924881, baseEnd_2924881] using wordTrace_append hprefix tailTrace_2924881
  have hstable : (prefixWord ++ tailWord_2924881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924881).length < 2 ^ (prefixWord ++ tailWord_2924881).sum := by decide
  have hdescent : baseEnd_2924881 < baseStart_2924881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924888 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 5, 2, 2]
def baseStart_2924888 : Nat := 118140960795 + 2924888 * 2 ^ 59
def prefixEnd_2924888 : Nat := 4983230072969 + 3 ^ 40 * 2924888 * 2
def baseEnd_2924888 : Nat := 1501873404567857595948691

theorem tailTrace_2924888 : CollatzResearch.WordTrace tailWord_2924888 prefixEnd_2924888 1501873404567857595948691 := by
  unfold tailWord_2924888
  simp only [CollatzResearch.WordTrace]
  refine ⟨53339714713818890972903659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71119619618425187963871545 53339714713818890972903659)
  ·
    refine ⟨80009572070728336459355489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53339714713818890972903659 80009572070728336459355489)
    ·
      refine ⟨60007179053046252344516617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80009572070728336459355489 60007179053046252344516617)
      ·
        refine ⟨45005384289784689258387463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60007179053046252344516617 45005384289784689258387463)
        ·
          refine ⟨67508076434677033887581195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45005384289784689258387463 67508076434677033887581195)
          ·
            refine ⟨101262114652015550831371793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67508076434677033887581195 101262114652015550831371793)
            ·
              refine ⟨75946585989011663123528845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101262114652015550831371793 75946585989011663123528845)
              ·
                refine ⟨28479969745879373671323317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75946585989011663123528845 28479969745879373671323317)
                ·
                  refine ⟨2669997163676191281686561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28479969745879373671323317 2669997163676191281686561)
                  ·
                    refine ⟨2002497872757143461264921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2669997163676191281686561 2002497872757143461264921)
                    ·
                      refine ⟨1501873404567857595948691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2002497872757143461264921 1501873404567857595948691)
                      ·
                        rfl

theorem cell23_2924888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_2924888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924888 prefixEnd_2924888 := by exact prefixLift 2924888
  have htrace : WordTrace (prefixWord ++ tailWord_2924888) baseStart_2924888 baseEnd_2924888 := by
    simpa [prefixWord, tailWord_2924888, baseEnd_2924888] using wordTrace_append hprefix tailTrace_2924888
  have hstable : (prefixWord ++ tailWord_2924888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924888).length < 2 ^ (prefixWord ++ tailWord_2924888).sum := by decide
  have hdescent : baseEnd_2924888 < baseStart_2924888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924898 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2924898 : Nat := 118140960795 + 2924898 * 2 ^ 59
def prefixEnd_2924898 : Nat := 4983230072969 + 3 ^ 40 * 2924898 * 2
def baseEnd_2924898 : Nat := 500626179791467518941215

theorem tailTrace_2924898 : CollatzResearch.WordTrace tailWord_2924898 prefixEnd_2924898 500626179791467518941215 := by
  unfold tailWord_2924898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26669948539400388413417837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71119862771734369102447565 26669948539400388413417837)
  ·
    refine ⟨10001230702275145655031689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26669948539400388413417837 10001230702275145655031689)
    ·
      refine ⟨7500923026706359241273767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10001230702275145655031689 7500923026706359241273767)
      ·
        refine ⟨11251384540059538861910651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7500923026706359241273767 11251384540059538861910651)
        ·
          refine ⟨16877076810089308292865977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11251384540059538861910651 16877076810089308292865977)
          ·
            refine ⟨12657807607566981219649483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16877076810089308292865977 12657807607566981219649483)
            ·
              refine ⟨18986711411350471829474225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12657807607566981219649483 18986711411350471829474225)
              ·
                refine ⟨14240033558512853872105669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18986711411350471829474225 14240033558512853872105669)
                ·
                  refine ⟨2670006292221160101019813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14240033558512853872105669 2670006292221160101019813)
                  ·
                    refine ⟨500626179791467518941215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2670006292221160101019813 500626179791467518941215)
                    ·
                      rfl

theorem cell23_2924898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2924898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924898 prefixEnd_2924898 := by exact prefixLift 2924898
  have htrace : WordTrace (prefixWord ++ tailWord_2924898) baseStart_2924898 baseEnd_2924898 := by
    simpa [prefixWord, tailWord_2924898, baseEnd_2924898] using wordTrace_append hprefix tailTrace_2924898
  have hstable : (prefixWord ++ tailWord_2924898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924898).length < 2 ^ (prefixWord ++ tailWord_2924898).sum := by decide
  have hdescent : baseEnd_2924898 < baseStart_2924898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924908 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 5]
def baseStart_2924908 : Nat := 118140960795 + 2924908 * 2 ^ 59
def prefixEnd_2924908 : Nat := 4983230072969 + 3 ^ 40 * 2924908 * 2
def baseEnd_2924908 : Nat := 1501883674180947517698599

theorem tailTrace_2924908 : CollatzResearch.WordTrace tailWord_2924908 prefixEnd_2924908 1501883674180947517698599 := by
  unfold tailWord_2924908
  simp only [CollatzResearch.WordTrace]
  refine ⟨53340079443782662680767689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71120105925043550241023585 53340079443782662680767689)
  ·
    refine ⟨40005059582836997010575767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53340079443782662680767689 40005059582836997010575767)
    ·
      refine ⟨60007589374255495515863651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40005059582836997010575767 60007589374255495515863651)
      ·
        refine ⟨90011384061383243273795477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60007589374255495515863651 90011384061383243273795477)
        ·
          refine ⟨4219283627877339528459163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90011384061383243273795477 4219283627877339528459163)
          ·
            refine ⟨6328925441816009292688745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4219283627877339528459163 6328925441816009292688745)
            ·
              refine ⟨4746694081362006969516559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6328925441816009292688745 4746694081362006969516559)
              ·
                refine ⟨7120041122043010454274839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4746694081362006969516559 7120041122043010454274839)
                ·
                  refine ⟨10680061683064515681412259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7120041122043010454274839 10680061683064515681412259)
                  ·
                    refine ⟨16020092524596773522118389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10680061683064515681412259 16020092524596773522118389)
                    ·
                      refine ⟨1501883674180947517698599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16020092524596773522118389 1501883674180947517698599)
                      ·
                        rfl

theorem cell23_2924908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_2924908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924908 prefixEnd_2924908 := by exact prefixLift 2924908
  have htrace : WordTrace (prefixWord ++ tailWord_2924908) baseStart_2924908 baseEnd_2924908 := by
    simpa [prefixWord, tailWord_2924908, baseEnd_2924908] using wordTrace_append hprefix tailTrace_2924908
  have hstable : (prefixWord ++ tailWord_2924908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924908).length < 2 ^ (prefixWord ++ tailWord_2924908).sum := by decide
  have hdescent : baseEnd_2924908 < baseStart_2924908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924942 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2924942 : Nat := 118140960795 + 2924942 * 2 ^ 59
def prefixEnd_2924942 : Nat := 4983230072969 + 3 ^ 40 * 2924942 * 2
def baseEnd_2924942 : Nat := 1501901132523200384673443

theorem tailTrace_2924942 : CollatzResearch.WordTrace tailWord_2924942 prefixEnd_2924942 1501901132523200384673443 := by
  unfold tailWord_2924942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13335174871180268646034135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71120932646294766112182053 13335174871180268646034135)
  ·
    refine ⟨20002762306770402969051203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13335174871180268646034135 20002762306770402969051203)
    ·
      refine ⟨30004143460155604453576805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20002762306770402969051203 30004143460155604453576805)
      ·
        refine ⟨5625776898779175835045651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30004143460155604453576805 5625776898779175835045651)
        ·
          refine ⟨8438665348168763752568477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5625776898779175835045651 8438665348168763752568477)
          ·
            refine ⟨3164499505563286407213179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8438665348168763752568477 3164499505563286407213179)
            ·
              refine ⟨4746749258344929610819769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164499505563286407213179 4746749258344929610819769)
              ·
                refine ⟨3560061943758697208114827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4746749258344929610819769 3560061943758697208114827)
                ·
                  refine ⟨5340092915638045812172241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560061943758697208114827 5340092915638045812172241)
                  ·
                    refine ⟨4005069686728534359129181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5340092915638045812172241 4005069686728534359129181)
                    ·
                      refine ⟨1501901132523200384673443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4005069686728534359129181 1501901132523200384673443)
                      ·
                        rfl

theorem cell23_2924942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2924942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924942 prefixEnd_2924942 := by exact prefixLift 2924942
  have htrace : WordTrace (prefixWord ++ tailWord_2924942) baseStart_2924942 baseEnd_2924942 := by
    simpa [prefixWord, tailWord_2924942, baseEnd_2924942] using wordTrace_append hprefix tailTrace_2924942
  have hstable : (prefixWord ++ tailWord_2924942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924942).length < 2 ^ (prefixWord ++ tailWord_2924942).sum := by decide
  have hdescent : baseEnd_2924942 < baseStart_2924942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924973 : List Nat := [1, 5, 2, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_2924973 : Nat := 118140960795 + 2924973 * 2 ^ 59
def prefixEnd_2924973 : Nat := 4983230072969 + 3 ^ 40 * 2924973 * 2
def baseEnd_2924973 : Nat := 1501917050423489763385801

theorem tailTrace_2924973 : CollatzResearch.WordTrace tailWord_2924973 prefixEnd_2924973 1501917050423489763385801 := by
  unfold tailWord_2924973
  simp only [CollatzResearch.WordTrace]
  refine ⟨106682529632329841462651573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71121686421553227641767715 106682529632329841462651573)
  ·
    refine ⟨10001487153030922637123585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106682529632329841462651573 10001487153030922637123585)
    ·
      refine ⟨7501115364773191977842689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10001487153030922637123585 7501115364773191977842689)
      ·
        refine ⟨5625836523579893983382017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7501115364773191977842689 5625836523579893983382017)
        ·
          refine ⟨4219377392684920487536513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5625836523579893983382017 4219377392684920487536513)
          ·
            refine ⟨3164533044513690365652385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4219377392684920487536513 3164533044513690365652385)
            ·
              refine ⟨2373399783385267774239289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3164533044513690365652385 2373399783385267774239289)
              ·
                refine ⟨1780049837538950830679467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2373399783385267774239289 1780049837538950830679467)
                ·
                  refine ⟨2670074756308426246019201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780049837538950830679467 2670074756308426246019201)
                  ·
                    refine ⟨2002556067231319684514401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2670074756308426246019201 2002556067231319684514401)
                    ·
                      refine ⟨1501917050423489763385801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2002556067231319684514401 1501917050423489763385801)
                      ·
                        rfl

theorem cell23_2924973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_2924973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924973 prefixEnd_2924973 := by exact prefixLift 2924973
  have htrace : WordTrace (prefixWord ++ tailWord_2924973) baseStart_2924973 baseEnd_2924973 := by
    simpa [prefixWord, tailWord_2924973, baseEnd_2924973] using wordTrace_append hprefix tailTrace_2924973
  have hstable : (prefixWord ++ tailWord_2924973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924973).length < 2 ^ (prefixWord ++ tailWord_2924973).sum := by decide
  have hdescent : baseEnd_2924973 < baseStart_2924973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924978 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2]
def baseStart_2924978 : Nat := 118140960795 + 2924978 * 2 ^ 59
def prefixEnd_2924978 : Nat := 4983230072969 + 3 ^ 40 * 2924978 * 2
def baseEnd_2924978 : Nat := 1501919617826762243823277

theorem tailTrace_2924978 : CollatzResearch.WordTrace tailWord_2924978 prefixEnd_2924978 1501919617826762243823277 := by
  unfold tailWord_2924978
  simp only [CollatzResearch.WordTrace]
  refine ⟨26670677999327931829145897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71121807998207818211055725 26670677999327931829145897)
  ·
    refine ⟨20003008499495948871859423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26670677999327931829145897 20003008499495948871859423)
    ·
      refine ⟨30004512749243923307789135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20003008499495948871859423 30004512749243923307789135)
      ·
        refine ⟨45006769123865884961683703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30004512749243923307789135 45006769123865884961683703)
        ·
          refine ⟨67510153685798827442525555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45006769123865884961683703 67510153685798827442525555)
          ·
            refine ⟨101265230528698241163788333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67510153685798827442525555 101265230528698241163788333)
            ·
              refine ⟨37974461448261840436420625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101265230528698241163788333 37974461448261840436420625)
              ·
                refine ⟨28480846086196380327315469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37974461448261840436420625 28480846086196380327315469)
                ·
                  refine ⟨10680317282323642622743301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28480846086196380327315469 10680317282323642622743301)
                  ·
                    refine ⟨2002559490435682991764369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10680317282323642622743301 2002559490435682991764369)
                    ·
                      refine ⟨1501919617826762243823277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2002559490435682991764369 1501919617826762243823277)
                      ·
                        rfl

theorem cell23_2924978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_2924978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924978 prefixEnd_2924978 := by exact prefixLift 2924978
  have htrace : WordTrace (prefixWord ++ tailWord_2924978) baseStart_2924978 baseEnd_2924978 := by
    simpa [prefixWord, tailWord_2924978, baseEnd_2924978] using wordTrace_append hprefix tailTrace_2924978
  have hstable : (prefixWord ++ tailWord_2924978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924978).length < 2 ^ (prefixWord ++ tailWord_2924978).sum := by decide
  have hdescent : baseEnd_2924978 < baseStart_2924978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2924988 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_2924988 : Nat := 118140960795 + 2924988 * 2 ^ 59
def prefixEnd_2924988 : Nat := 4983230072969 + 3 ^ 40 * 2924988 * 2
def baseEnd_2924988 : Nat := 500641584211102401566077

theorem tailTrace_2924988 : CollatzResearch.WordTrace tailWord_2924988 prefixEnd_2924988 500641584211102401566077 := by
  unfold tailWord_2924988
  simp only [CollatzResearch.WordTrace]
  refine ⟨53341538363637749512223809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71122051151516999349631745 53341538363637749512223809)
  ·
    refine ⟨40006153772728312134167857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53341538363637749512223809 40006153772728312134167857)
    ·
      refine ⟨30004615329546234100625893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40006153772728312134167857 30004615329546234100625893)
      ·
        refine ⟨5625865374289918893867355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30004615329546234100625893 5625865374289918893867355)
        ·
          refine ⟨8438798061434878340801033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5625865374289918893867355 8438798061434878340801033)
          ·
            refine ⟨6329098546076158755600775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8438798061434878340801033 6329098546076158755600775)
            ·
              refine ⟨9493647819114238133401163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6329098546076158755600775 9493647819114238133401163)
              ·
                refine ⟨14240471728671357200101745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9493647819114238133401163 14240471728671357200101745)
                ·
                  refine ⟨10680353796503517900076309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14240471728671357200101745 10680353796503517900076309)
                  ·
                    refine ⟨500641584211102401566077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10680353796503517900076309 500641584211102401566077)
                    ·
                      rfl

theorem cell23_2924988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_2924988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2924988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2924988 prefixEnd_2924988 := by exact prefixLift 2924988
  have htrace : WordTrace (prefixWord ++ tailWord_2924988) baseStart_2924988 baseEnd_2924988 := by
    simpa [prefixWord, tailWord_2924988, baseEnd_2924988] using wordTrace_append hprefix tailTrace_2924988
  have hstable : (prefixWord ++ tailWord_2924988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2924988).length < 2 ^ (prefixWord ++ tailWord_2924988).sum := by decide
  have hdescent : baseEnd_2924988 < baseStart_2924988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2924988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925041 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_2925041 : Nat := 118140960795 + 2925041 * 2 ^ 59
def prefixEnd_2925041 : Nat := 4983230072969 + 3 ^ 40 * 2925041 * 2
def baseEnd_2925041 : Nat := 1501951967107995497335487

theorem tailTrace_2925041 : CollatzResearch.WordTrace tailWord_2925041 prefixEnd_2925041 1501951967107995497335487 := by
  unfold tailWord_2925041
  simp only [CollatzResearch.WordTrace]
  refine ⟨106685009796083489076126977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71123339864055659384084651 106685009796083489076126977)
  ·
    refine ⟨80013757347062616807095233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106685009796083489076126977 80013757347062616807095233)
    ·
      refine ⟨60010318010296962605321425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80013757347062616807095233 60010318010296962605321425)
      ·
        refine ⟨45007738507722721953991069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60010318010296962605321425 45007738507722721953991069)
        ·
          refine ⟨16877901940396020732746651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45007738507722721953991069 16877901940396020732746651)
          ·
            refine ⟨25316852910594031099119977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16877901940396020732746651 25316852910594031099119977)
            ·
              refine ⟨18987639682945523324339983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25316852910594031099119977 18987639682945523324339983)
              ·
                refine ⟨28481459524418284986509975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18987639682945523324339983 28481459524418284986509975)
                ·
                  refine ⟨42722189286627427479764963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28481459524418284986509975 42722189286627427479764963)
                  ·
                    refine ⟨64083283929941141219647445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42722189286627427479764963 64083283929941141219647445)
                    ·
                      refine ⟨1501951967107995497335487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64083283929941141219647445 1501951967107995497335487)
                      ·
                        rfl

theorem cell23_2925041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_2925041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925041 prefixEnd_2925041 := by exact prefixLift 2925041
  have htrace : WordTrace (prefixWord ++ tailWord_2925041) baseStart_2925041 baseEnd_2925041 := by
    simpa [prefixWord, tailWord_2925041, baseEnd_2925041] using wordTrace_append hprefix tailTrace_2925041
  have hstable : (prefixWord ++ tailWord_2925041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925041).length < 2 ^ (prefixWord ++ tailWord_2925041).sum := by decide
  have hdescent : baseEnd_2925041 < baseStart_2925041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925068 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_2925068 : Nat := 118140960795 + 2925068 * 2 ^ 59
def prefixEnd_2925068 : Nat := 4983230072969 + 3 ^ 40 * 2925068 * 2
def baseEnd_2925068 : Nat := 1501965831085666891697863

theorem tailTrace_2925068 : CollatzResearch.WordTrace tailWord_2925068 prefixEnd_2925068 1501965831085666891697863 := by
  unfold tailWord_2925068
  simp only [CollatzResearch.WordTrace]
  refine ⟨53342997283492836343679929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71123996377990448458239905 53342997283492836343679929)
  ·
    refine ⟨40007247962619627257759947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53342997283492836343679929 40007247962619627257759947)
    ·
      refine ⟨60010871943929440886639921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40007247962619627257759947 60010871943929440886639921)
      ·
        refine ⟨45008153957947080664979941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60010871943929440886639921 45008153957947080664979941)
        ·
          refine ⟨8439028867115077624683739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45008153957947080664979941 8439028867115077624683739)
          ·
            refine ⟨12658543300672616437025609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8439028867115077624683739 12658543300672616437025609)
            ·
              refine ⟨9493907475504462327769207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12658543300672616437025609 9493907475504462327769207)
              ·
                refine ⟨14240861213256693491653811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9493907475504462327769207 14240861213256693491653811)
                ·
                  refine ⟨21361291819885040237480717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14240861213256693491653811 21361291819885040237480717)
                  ·
                    refine ⟨8010484432456890089055269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21361291819885040237480717 8010484432456890089055269)
                    ·
                      refine ⟨1501965831085666891697863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8010484432456890089055269 1501965831085666891697863)
                      ·
                        rfl

theorem cell23_2925068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_2925068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925068 prefixEnd_2925068 := by exact prefixLift 2925068
  have htrace : WordTrace (prefixWord ++ tailWord_2925068) baseStart_2925068 baseEnd_2925068 := by
    simpa [prefixWord, tailWord_2925068, baseEnd_2925068] using wordTrace_append hprefix tailTrace_2925068
  have hstable : (prefixWord ++ tailWord_2925068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925068).length < 2 ^ (prefixWord ++ tailWord_2925068).sum := by decide
  have hdescent : baseEnd_2925068 < baseStart_2925068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925069 : List Nat := [1, 7, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2925069 : Nat := 118140960795 + 2925069 * 2 ^ 59
def prefixEnd_2925069 : Nat := 4983230072969 + 3 ^ 40 * 2925069 * 2
def baseEnd_2925069 : Nat := 166885149396257931976151

theorem tailTrace_2925069 : CollatzResearch.WordTrace tailWord_2925069 prefixEnd_2925069 166885149396257931976151 := by
  unfold tailWord_2925069
  simp only [CollatzResearch.WordTrace]
  refine ⟨106686031039982049858146261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71124020693321366572097507 106686031039982049858146261)
  ·
    refine ⟨2500453852499579293550303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 106686031039982049858146261 2500453852499579293550303)
    ·
      refine ⟨3750680778749368940325455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2500453852499579293550303 3750680778749368940325455)
      ·
        refine ⟨5626021168124053410488183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3750680778749368940325455 5626021168124053410488183)
        ·
          refine ⟨8439031752186080115732275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626021168124053410488183 8439031752186080115732275)
          ·
            refine ⟨12658547628279120173598413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8439031752186080115732275 12658547628279120173598413)
            ·
              refine ⟨4746955360604670065099405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12658547628279120173598413 4746955360604670065099405)
              ·
                refine ⟨1780108260226751274412277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4746955360604670065099405 1780108260226751274412277)
                ·
                  refine ⟨166885149396257931976151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1780108260226751274412277 166885149396257931976151)
                  ·
                    rfl

theorem cell23_2925069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2925069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925069 prefixEnd_2925069 := by exact prefixLift 2925069
  have htrace : WordTrace (prefixWord ++ tailWord_2925069) baseStart_2925069 baseEnd_2925069 := by
    simpa [prefixWord, tailWord_2925069, baseEnd_2925069] using wordTrace_append hprefix tailTrace_2925069
  have hstable : (prefixWord ++ tailWord_2925069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925069).length < 2 ^ (prefixWord ++ tailWord_2925069).sum := by decide
  have hdescent : baseEnd_2925069 < baseStart_2925069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925081 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 4]
def baseStart_2925081 : Nat := 118140960795 + 2925081 * 2 ^ 59
def prefixEnd_2925081 : Nat := 4983230072969 + 3 ^ 40 * 2925081 * 2
def baseEnd_2925081 : Nat := 1501972506334175340835303

theorem tailTrace_2925081 : CollatzResearch.WordTrace tailWord_2925081 prefixEnd_2925081 1501972506334175340835303 := by
  unfold tailWord_2925081
  simp only [CollatzResearch.WordTrace]
  refine ⟨106686468715938575907583097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71124312477292383938388731 106686468715938575907583097)
  ·
    refine ⟨80014851536953931930687323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106686468715938575907583097 80014851536953931930687323)
    ·
      refine ⟨120022277305430897896030985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80014851536953931930687323 120022277305430897896030985)
      ·
        refine ⟨90016707979073173422023239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120022277305430897896030985 90016707979073173422023239)
        ·
          refine ⟨135025061968609760133034859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90016707979073173422023239 135025061968609760133034859)
          ·
            refine ⟨202537592952914640199552289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135025061968609760133034859 202537592952914640199552289)
            ·
              refine ⟨151903194714685980149664217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202537592952914640199552289 151903194714685980149664217)
              ·
                refine ⟨113927396036014485112248163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151903194714685980149664217 113927396036014485112248163)
                ·
                  refine ⟨170891094054021727668372245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113927396036014485112248163 170891094054021727668372245)
                  ·
                    refine ⟨8010520033782268484454949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 170891094054021727668372245 8010520033782268484454949)
                    ·
                      refine ⟨1501972506334175340835303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8010520033782268484454949 1501972506334175340835303)
                      ·
                        rfl

theorem cell23_2925081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_2925081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925081 prefixEnd_2925081 := by exact prefixLift 2925081
  have htrace : WordTrace (prefixWord ++ tailWord_2925081) baseStart_2925081 baseEnd_2925081 := by
    simpa [prefixWord, tailWord_2925081, baseEnd_2925081] using wordTrace_append hprefix tailTrace_2925081
  have hstable : (prefixWord ++ tailWord_2925081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925081).length < 2 ^ (prefixWord ++ tailWord_2925081).sum := by decide
  have hdescent : baseEnd_2925081 < baseStart_2925081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925085 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_2925085 : Nat := 118140960795 + 2925085 * 2 ^ 59
def prefixEnd_2925085 : Nat := 4983230072969 + 3 ^ 40 * 2925085 * 2
def baseEnd_2925085 : Nat := 1501974560256793325185285

theorem tailTrace_2925085 : CollatzResearch.WordTrace tailWord_2925085 prefixEnd_2925085 1501974560256793325185285 := by
  unfold tailWord_2925085
  simp only [CollatzResearch.WordTrace]
  refine ⟨106686614607924084590728709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71124409738616056393819139 106686614607924084590728709)
  ·
    refine ⟨20003740238985765860761633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106686614607924084590728709 20003740238985765860761633)
    ·
      refine ⟨15002805179239324395571225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20003740238985765860761633 15002805179239324395571225)
      ·
        refine ⟨11252103884429493296678419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15002805179239324395571225 11252103884429493296678419)
        ·
          refine ⟨16878155826644239945017629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11252103884429493296678419 16878155826644239945017629)
          ·
            refine ⟨6329308434991589979381611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16878155826644239945017629 6329308434991589979381611)
            ·
              refine ⟨9493962652487384969072417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6329308434991589979381611 9493962652487384969072417)
              ·
                refine ⟨7120471989365538726804313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9493962652487384969072417 7120471989365538726804313)
                ·
                  refine ⟨5340353992024154045103235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7120471989365538726804313 5340353992024154045103235)
                  ·
                    refine ⟨8010530988036231067654853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5340353992024154045103235 8010530988036231067654853)
                    ·
                      refine ⟨1501974560256793325185285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8010530988036231067654853 1501974560256793325185285)
                      ·
                        rfl

theorem cell23_2925085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_2925085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925085 prefixEnd_2925085 := by exact prefixLift 2925085
  have htrace : WordTrace (prefixWord ++ tailWord_2925085) baseStart_2925085 baseEnd_2925085 := by
    simpa [prefixWord, tailWord_2925085, baseEnd_2925085] using wordTrace_append hprefix tailTrace_2925085
  have hstable : (prefixWord ++ tailWord_2925085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925085).length < 2 ^ (prefixWord ++ tailWord_2925085).sum := by decide
  have hdescent : baseEnd_2925085 < baseStart_2925085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925185 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 4, 4]
def baseStart_2925185 : Nat := 118140960795 + 2925185 * 2 ^ 59
def prefixEnd_2925185 : Nat := 4983230072969 + 3 ^ 40 * 2925185 * 2
def baseEnd_2925185 : Nat := 500675302774080977978275

theorem tailTrace_2925185 : CollatzResearch.WordTrace tailWord_2925185 prefixEnd_2925185 500675302774080977978275 := by
  unfold tailWord_2925185
  simp only [CollatzResearch.WordTrace]
  refine ⟨106690261907561801669369009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71126841271707867779579339 106690261907561801669369009)
  ·
    refine ⟨80017696430671351252026757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106690261907561801669369009 80017696430671351252026757)
    ·
      refine ⟨15003318080750878359755017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80017696430671351252026757 15003318080750878359755017)
      ·
        refine ⟨11252488560563158769816263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15003318080750878359755017 11252488560563158769816263)
        ·
          refine ⟨16878732840844738154724395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11252488560563158769816263 16878732840844738154724395)
          ·
            refine ⟨25318099261267107232086593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16878732840844738154724395 25318099261267107232086593)
            ·
              refine ⟨18988574445950330424064945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25318099261267107232086593 18988574445950330424064945)
              ·
                refine ⟨14241430834462747818048709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18988574445950330424064945 14241430834462747818048709)
                ·
                  refine ⟨2670268281461765215884133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14241430834462747818048709 2670268281461765215884133)
                  ·
                    refine ⟨500675302774080977978275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2670268281461765215884133 500675302774080977978275)
                    ·
                      rfl

theorem cell23_2925185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_2925185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925185 prefixEnd_2925185 := by exact prefixLift 2925185
  have htrace : WordTrace (prefixWord ++ tailWord_2925185) baseStart_2925185 baseEnd_2925185 := by
    simpa [prefixWord, tailWord_2925185, baseEnd_2925185] using wordTrace_append hprefix tailTrace_2925185
  have hstable : (prefixWord ++ tailWord_2925185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925185).length < 2 ^ (prefixWord ++ tailWord_2925185).sum := by decide
  have hdescent : baseEnd_2925185 < baseStart_2925185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925198 : List Nat := [4, 1, 1, 3, 1, 1, 12]
def baseStart_2925198 : Nat := 118140960795 + 2925198 * 2 ^ 59
def prefixEnd_2925198 : Nat := 4983230072969 + 3 ^ 40 * 2925198 * 2
def baseEnd_2925198 : Nat := 18543612142848782507065

theorem tailTrace_2925198 : CollatzResearch.WordTrace tailWord_2925198 prefixEnd_2925198 18543612142848782507065 := by
  unfold tailWord_2925198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13336342007064338111199031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71127157371009803259728165 13336342007064338111199031)
  ·
    refine ⟨20004513010596507166798547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13336342007064338111199031 20004513010596507166798547)
    ·
      refine ⟨30006769515894760750197821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20004513010596507166798547 30006769515894760750197821)
      ·
        refine ⟨11252538568460535281324183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30006769515894760750197821 11252538568460535281324183)
        ·
          refine ⟨16878807852690802921986275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11252538568460535281324183 16878807852690802921986275)
          ·
            refine ⟨25318211779036204382979413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16878807852690802921986275 25318211779036204382979413)
            ·
              refine ⟨18543612142848782507065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 25318211779036204382979413 18543612142848782507065)
              ·
                rfl

theorem cell23_2925198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 12].length) (baseStart_2925198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925198 prefixEnd_2925198 := by exact prefixLift 2925198
  have htrace : WordTrace (prefixWord ++ tailWord_2925198) baseStart_2925198 baseEnd_2925198 := by
    simpa [prefixWord, tailWord_2925198, baseEnd_2925198] using wordTrace_append hprefix tailTrace_2925198
  have hstable : (prefixWord ++ tailWord_2925198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925198).length < 2 ^ (prefixWord ++ tailWord_2925198).sum := by decide
  have hdescent : baseEnd_2925198 < baseStart_2925198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925202 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_2925202 : Nat := 118140960795 + 2925202 * 2 ^ 59
def prefixEnd_2925202 : Nat := 4983230072969 + 3 ^ 40 * 2925202 * 2
def baseEnd_2925202 : Nat := 500678212497789789140749

theorem tailTrace_2925202 : CollatzResearch.WordTrace tailWord_2925202 prefixEnd_2925202 500678212497789789140749 := by
  unfold tailWord_2925202
  simp only [CollatzResearch.WordTrace]
  refine ⟨26672720487125053393184465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71127254632333475715158573 26672720487125053393184465)
  ·
    refine ⟨20004540365343790044888349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26672720487125053393184465 20004540365343790044888349)
    ·
      refine ⟨7501702637003921266833131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20004540365343790044888349 7501702637003921266833131)
      ·
        refine ⟨11252553955505881900249697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7501702637003921266833131 11252553955505881900249697)
        ·
          refine ⟨8439415466629411425187273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11252553955505881900249697 8439415466629411425187273)
          ·
            refine ⟨6329561599972058568890455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8439415466629411425187273 6329561599972058568890455)
            ·
              refine ⟨9494342399958087853335683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6329561599972058568890455 9494342399958087853335683)
              ·
                refine ⟨14241513599937131780003525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9494342399958087853335683 14241513599937131780003525)
                ·
                  refine ⟨2670283799988212208750661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14241513599937131780003525 2670283799988212208750661)
                  ·
                    refine ⟨500678212497789789140749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2670283799988212208750661 500678212497789789140749)
                    ·
                      rfl

theorem cell23_2925202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_2925202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925202 prefixEnd_2925202 := by exact prefixLift 2925202
  have htrace : WordTrace (prefixWord ++ tailWord_2925202) baseStart_2925202 baseEnd_2925202 := by
    simpa [prefixWord, tailWord_2925202, baseEnd_2925202] using wordTrace_append hprefix tailTrace_2925202
  have hstable : (prefixWord ++ tailWord_2925202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925202).length < 2 ^ (prefixWord ++ tailWord_2925202).sum := by decide
  have hdescent : baseEnd_2925202 < baseStart_2925202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925209 : List Nat := [1, 2, 1, 2, 1, 2, 3, 6, 1, 2, 2]
def baseStart_2925209 : Nat := 118140960795 + 2925209 * 2 ^ 59
def prefixEnd_2925209 : Nat := 4983230072969 + 3 ^ 40 * 2925209 * 2
def baseEnd_2925209 : Nat := 1502038231857950840034715

theorem tailTrace_2925209 : CollatzResearch.WordTrace tailWord_2925209 prefixEnd_2925209 1502038231857950840034715 := by
  unfold tailWord_2925209
  simp only [CollatzResearch.WordTrace]
  refine ⟨106691137259474853768242681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71127424839649902512161787 106691137259474853768242681)
  ·
    refine ⟨80018352944606140326182011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106691137259474853768242681 80018352944606140326182011)
    ·
      refine ⟨120027529416909210489273017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80018352944606140326182011 120027529416909210489273017)
      ·
        refine ⟨90020647062681907866954763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120027529416909210489273017 90020647062681907866954763)
        ·
          refine ⟨135030970594022861800432145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90020647062681907866954763 135030970594022861800432145)
          ·
            refine ⟨101273227945517146350324109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135030970594022861800432145 101273227945517146350324109)
            ·
              refine ⟨37977460479568929881371541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101273227945517146350324109 37977460479568929881371541)
              ·
                refine ⟨1780193459979793588189291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37977460479568929881371541 1780193459979793588189291)
                ·
                  refine ⟨2670290189969690382283937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780193459979793588189291 2670290189969690382283937)
                  ·
                    refine ⟨2002717642477267786712953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2670290189969690382283937 2002717642477267786712953)
                    ·
                      refine ⟨1502038231857950840034715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2002717642477267786712953 1502038231857950840034715)
                      ·
                        rfl

theorem cell23_2925209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 1, 2, 2].length) (baseStart_2925209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925209 prefixEnd_2925209 := by exact prefixLift 2925209
  have htrace : WordTrace (prefixWord ++ tailWord_2925209) baseStart_2925209 baseEnd_2925209 := by
    simpa [prefixWord, tailWord_2925209, baseEnd_2925209] using wordTrace_append hprefix tailTrace_2925209
  have hstable : (prefixWord ++ tailWord_2925209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925209).length < 2 ^ (prefixWord ++ tailWord_2925209).sum := by decide
  have hdescent : baseEnd_2925209 < baseStart_2925209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925225 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 6, 1, 3]
def baseStart_2925225 : Nat := 118140960795 + 2925225 * 2 ^ 59
def prefixEnd_2925225 : Nat := 4983230072969 + 3 ^ 40 * 2925225 * 2
def baseEnd_2925225 : Nat := 1502046447548422777434641

theorem tailTrace_2925225 : CollatzResearch.WordTrace tailWord_2925225 prefixEnd_2925225 1502046447548422777434641 := by
  unfold tailWord_2925225
  simp only [CollatzResearch.WordTrace]
  refine ⟨106691720827416888500825129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71127813884944592333883419 106691720827416888500825129)
  ·
    refine ⟨80018790620562666375618847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106691720827416888500825129 80018790620562666375618847)
    ·
      refine ⟨120028185930843999563428271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80018790620562666375618847 120028185930843999563428271)
      ·
        refine ⟨180042278896265999345142407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120028185930843999563428271 180042278896265999345142407)
        ·
          refine ⟨270063418344398999017713611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180042278896265999345142407 270063418344398999017713611)
          ·
            refine ⟨405095127516598498526570417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270063418344398999017713611 405095127516598498526570417)
            ·
              refine ⟨303821345637448873894927813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405095127516598498526570417 303821345637448873894927813)
              ·
                refine ⟨56966502307021663855298965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303821345637448873894927813 56966502307021663855298965)
                ·
                  refine ⟨2670304795641640493217139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56966502307021663855298965 2670304795641640493217139)
                  ·
                    refine ⟨4005457193462460739825709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2670304795641640493217139 4005457193462460739825709)
                    ·
                      refine ⟨1502046447548422777434641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4005457193462460739825709 1502046447548422777434641)
                      ·
                        rfl

theorem cell23_2925225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 1, 3].length) (baseStart_2925225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925225 prefixEnd_2925225 := by exact prefixLift 2925225
  have htrace : WordTrace (prefixWord ++ tailWord_2925225) baseStart_2925225 baseEnd_2925225 := by
    simpa [prefixWord, tailWord_2925225, baseEnd_2925225] using wordTrace_append hprefix tailTrace_2925225
  have hstable : (prefixWord ++ tailWord_2925225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925225).length < 2 ^ (prefixWord ++ tailWord_2925225).sum := by decide
  have hdescent : baseEnd_2925225 < baseStart_2925225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925226 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2925226 : Nat := 118140960795 + 2925226 * 2 ^ 59
def prefixEnd_2925226 : Nat := 4983230072969 + 3 ^ 40 * 2925226 * 2
def baseEnd_2925226 : Nat := 1502046961029077273522137

theorem tailTrace_2925226 : CollatzResearch.WordTrace tailWord_2925226 prefixEnd_2925226 1502046961029077273522137 := by
  unfold tailWord_2925226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26672939325103316417902883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71127838200275510447741021 26672939325103316417902883)
  ·
    refine ⟨40009408987654974626854325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26672939325103316417902883 40009408987654974626854325)
    ·
      refine ⟨3750882092592653871267593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40009408987654974626854325 3750882092592653871267593)
      ·
        refine ⟨2813161569444490403450695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3750882092592653871267593 2813161569444490403450695)
        ·
          refine ⟨4219742354166735605176043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2813161569444490403450695 4219742354166735605176043)
          ·
            refine ⟨6329613531250103407764065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4219742354166735605176043 6329613531250103407764065)
            ·
              refine ⟨4747210148437577555823049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6329613531250103407764065 4747210148437577555823049)
              ·
                refine ⟨3560407611328183166867287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4747210148437577555823049 3560407611328183166867287)
                ·
                  refine ⟨5340611416992274750300931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560407611328183166867287 5340611416992274750300931)
                  ·
                    refine ⟨8010917125488412125451397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5340611416992274750300931 8010917125488412125451397)
                    ·
                      refine ⟨1502046961029077273522137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8010917125488412125451397 1502046961029077273522137)
                      ·
                        rfl

theorem cell23_2925226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2925226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925226 prefixEnd_2925226 := by exact prefixLift 2925226
  have htrace : WordTrace (prefixWord ++ tailWord_2925226) baseStart_2925226 baseEnd_2925226 := by
    simpa [prefixWord, tailWord_2925226, baseEnd_2925226] using wordTrace_append hprefix tailTrace_2925226
  have hstable : (prefixWord ++ tailWord_2925226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925226).length < 2 ^ (prefixWord ++ tailWord_2925226).sum := by decide
  have hdescent : baseEnd_2925226 < baseStart_2925226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925229 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_2925229 : Nat := 118140960795 + 2925229 * 2 ^ 59
def prefixEnd_2925229 : Nat := 4983230072969 + 3 ^ 40 * 2925229 * 2
def baseEnd_2925229 : Nat := 1502048501471040761784623

theorem tailTrace_2925229 : CollatzResearch.WordTrace tailWord_2925229 prefixEnd_2925229 1502048501471040761784623 := by
  unfold tailWord_2925229
  simp only [CollatzResearch.WordTrace]
  refine ⟨106691866719402397183970741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71127911146268264789313827 106691866719402397183970741)
  ·
    refine ⟨10002362504943974735997257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106691866719402397183970741 10002362504943974735997257)
    ·
      refine ⟨7501771878707981051997943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10002362504943974735997257 7501771878707981051997943)
      ·
        refine ⟨11252657818061971577996915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7501771878707981051997943 11252657818061971577996915)
        ·
          refine ⟨16878986727092957366995373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11252657818061971577996915 16878986727092957366995373)
          ·
            refine ⟨6329620022659859012623265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16878986727092957366995373 6329620022659859012623265)
            ·
              refine ⟨4747215016994894259467449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6329620022659859012623265 4747215016994894259467449)
              ·
                refine ⟨3560411262746170694600587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4747215016994894259467449 3560411262746170694600587)
                ·
                  refine ⟨5340616894119256041900881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560411262746170694600587 5340616894119256041900881)
                  ·
                    refine ⟨4005462670589442031425661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5340616894119256041900881 4005462670589442031425661)
                    ·
                      refine ⟨1502048501471040761784623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4005462670589442031425661 1502048501471040761784623)
                      ·
                        rfl

theorem cell23_2925229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_2925229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925229 prefixEnd_2925229 := by exact prefixLift 2925229
  have htrace : WordTrace (prefixWord ++ tailWord_2925229) baseStart_2925229 baseEnd_2925229 := by
    simpa [prefixWord, tailWord_2925229, baseEnd_2925229] using wordTrace_append hprefix tailTrace_2925229
  have hstable : (prefixWord ++ tailWord_2925229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925229).length < 2 ^ (prefixWord ++ tailWord_2925229).sum := by decide
  have hdescent : baseEnd_2925229 < baseStart_2925229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925249 : List Nat := [1, 2, 6, 2, 2, 1, 9]
def baseStart_2925249 : Nat := 118140960795 + 2925249 * 2 ^ 59
def prefixEnd_2925249 : Nat := 4983230072969 + 3 ^ 40 * 2925249 * 2
def baseEnd_2925249 : Nat := 18543935445483094858451

theorem tailTrace_2925249 : CollatzResearch.WordTrace tailWord_2925249 prefixEnd_2925249 18543935445483094858451 := by
  unfold tailWord_2925249
  simp only [CollatzResearch.WordTrace]
  refine ⟨106692596179329940599698801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71128397452886627066465867 106692596179329940599698801)
  ·
    refine ⟨80019447134497455449774101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106692596179329940599698801 80019447134497455449774101)
    ·
      refine ⟨3750911584429568224208161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80019447134497455449774101 3750911584429568224208161)
      ·
        refine ⟨2813183688322176168156121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3750911584429568224208161 2813183688322176168156121)
        ·
          refine ⟨2109887766241632126117091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2813183688322176168156121 2109887766241632126117091)
          ·
            refine ⟨3164831649362448189175637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109887766241632126117091 3164831649362448189175637)
            ·
              refine ⟨18543935445483094858451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3164831649362448189175637 18543935445483094858451)
              ·
                rfl

theorem cell23_2925249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 9].length) (baseStart_2925249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925249 prefixEnd_2925249 := by exact prefixLift 2925249
  have htrace : WordTrace (prefixWord ++ tailWord_2925249) baseStart_2925249 baseEnd_2925249 := by
    simpa [prefixWord, tailWord_2925249, baseEnd_2925249] using wordTrace_append hprefix tailTrace_2925249
  have hstable : (prefixWord ++ tailWord_2925249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925249).length < 2 ^ (prefixWord ++ tailWord_2925249).sum := by decide
  have hdescent : baseEnd_2925249 < baseStart_2925249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925276 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2925276 : Nat := 118140960795 + 2925276 * 2 ^ 59
def prefixEnd_2925276 : Nat := 4983230072969 + 3 ^ 40 * 2925276 * 2
def baseEnd_2925276 : Nat := 1502072635061802077896907

theorem tailTrace_2925276 : CollatzResearch.WordTrace tailWord_2925276 prefixEnd_2925276 1502072635061802077896907 := by
  unfold tailWord_2925276
  simp only [CollatzResearch.WordTrace]
  refine ⟨53346790475116062105465841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71129053966821416140621121 53346790475116062105465841)
  ·
    refine ⟨40010092856337046579099381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53346790475116062105465841 40010092856337046579099381)
    ·
      refine ⟨3750946205281598116790567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40010092856337046579099381 3750946205281598116790567)
      ·
        refine ⟨5626419307922397175185851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3750946205281598116790567 5626419307922397175185851)
        ·
          refine ⟨8439628961883595762778777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626419307922397175185851 8439628961883595762778777)
          ·
            refine ⟨6329721721412696822084083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8439628961883595762778777 6329721721412696822084083)
            ·
              refine ⟨9494582582119045233126125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6329721721412696822084083 9494582582119045233126125)
              ·
                refine ⟨3560468468294641962422297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9494582582119045233126125 3560468468294641962422297)
                ·
                  refine ⟨2670351351220981471816723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3560468468294641962422297 2670351351220981471816723)
                  ·
                    refine ⟨4005527026831472207725085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2670351351220981471816723 4005527026831472207725085)
                    ·
                      refine ⟨1502072635061802077896907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4005527026831472207725085 1502072635061802077896907)
                      ·
                        rfl

theorem cell23_2925276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2925276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925276 prefixEnd_2925276 := by exact prefixLift 2925276
  have htrace : WordTrace (prefixWord ++ tailWord_2925276) baseStart_2925276 baseEnd_2925276 := by
    simpa [prefixWord, tailWord_2925276, baseEnd_2925276] using wordTrace_append hprefix tailTrace_2925276
  have hstable : (prefixWord ++ tailWord_2925276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925276).length < 2 ^ (prefixWord ++ tailWord_2925276).sum := by decide
  have hdescent : baseEnd_2925276 < baseStart_2925276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925285 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2925285 : Nat := 118140960795 + 2925285 * 2 ^ 59
def prefixEnd_2925285 : Nat := 4983230072969 + 3 ^ 40 * 2925285 * 2
def baseEnd_2925285 : Nat := 1502077256387692542684365

theorem tailTrace_2925285 : CollatzResearch.WordTrace tailWord_2925285 prefixEnd_2925285 1502077256387692542684365 := by
  unfold tailWord_2925285
  simp only [CollatzResearch.WordTrace]
  refine ⟨106693909207199518748009309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71129272804799679165339539 106693909207199518748009309)
  ·
    refine ⟨40010215952699819530503491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106693909207199518748009309 40010215952699819530503491)
    ·
      refine ⟨60015323929049729295755237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40010215952699819530503491 60015323929049729295755237)
      ·
        refine ⟨11252873236696824242954107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60015323929049729295755237 11252873236696824242954107)
        ·
          refine ⟨16879309855045236364431161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11252873236696824242954107 16879309855045236364431161)
          ·
            refine ⟨12659482391283927273323371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16879309855045236364431161 12659482391283927273323371)
            ·
              refine ⟨18989223586925890909985057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12659482391283927273323371 18989223586925890909985057)
              ·
                refine ⟨14241917690194418182488793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18989223586925890909985057 14241917690194418182488793)
                ·
                  refine ⟨10681438267645813636866595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14241917690194418182488793 10681438267645813636866595)
                  ·
                    refine ⟨16022157401468720455299893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10681438267645813636866595 16022157401468720455299893)
                    ·
                      refine ⟨1502077256387692542684365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16022157401468720455299893 1502077256387692542684365)
                      ·
                        rfl

theorem cell23_2925285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2925285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925285 prefixEnd_2925285 := by exact prefixLift 2925285
  have htrace : WordTrace (prefixWord ++ tailWord_2925285) baseStart_2925285 baseEnd_2925285 := by
    simpa [prefixWord, tailWord_2925285, baseEnd_2925285] using wordTrace_append hprefix tailTrace_2925285
  have hstable : (prefixWord ++ tailWord_2925285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925285).length < 2 ^ (prefixWord ++ tailWord_2925285).sum := by decide
  have hdescent : baseEnd_2925285 < baseStart_2925285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925315 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 3]
def baseStart_2925315 : Nat := 118140960795 + 2925315 * 2 ^ 59
def prefixEnd_2925315 : Nat := 4983230072969 + 3 ^ 40 * 2925315 * 2
def baseEnd_2925315 : Nat := 1502092660807327425309227

theorem tailTrace_2925315 : CollatzResearch.WordTrace tailWord_2925315 prefixEnd_2925315 1502092660807327425309227 := by
  unfold tailWord_2925315
  simp only [CollatzResearch.WordTrace]
  refine ⟨106695003397090833871601399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71130002264727222581067599 106695003397090833871601399)
  ·
    refine ⟨160042505095636250807402099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106695003397090833871601399 160042505095636250807402099)
    ·
      refine ⟨240063757643454376211103149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160042505095636250807402099 240063757643454376211103149)
      ·
        refine ⟨90023909116295391079163681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240063757643454376211103149 90023909116295391079163681)
        ·
          refine ⟨67517931837221543309372761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90023909116295391079163681 67517931837221543309372761)
          ·
            refine ⟨50638448877916157482029571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67517931837221543309372761 50638448877916157482029571)
            ·
              refine ⟨75957673316874236223044357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50638448877916157482029571 75957673316874236223044357)
              ·
                refine ⟨14242063746913919291820817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75957673316874236223044357 14242063746913919291820817)
                ·
                  refine ⟨10681547810185439468865613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14242063746913919291820817 10681547810185439468865613)
                  ·
                    refine ⟨4005580428819539800824605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10681547810185439468865613 4005580428819539800824605)
                    ·
                      refine ⟨1502092660807327425309227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4005580428819539800824605 1502092660807327425309227)
                      ·
                        rfl

theorem cell23_2925315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_2925315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925315 prefixEnd_2925315 := by exact prefixLift 2925315
  have htrace : WordTrace (prefixWord ++ tailWord_2925315) baseStart_2925315 baseEnd_2925315 := by
    simpa [prefixWord, tailWord_2925315, baseEnd_2925315] using wordTrace_append hprefix tailTrace_2925315
  have hstable : (prefixWord ++ tailWord_2925315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925315).length < 2 ^ (prefixWord ++ tailWord_2925315).sum := by decide
  have hdescent : baseEnd_2925315 < baseStart_2925315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925316 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_2925316 : Nat := 118140960795 + 2925316 * 2 ^ 59
def prefixEnd_2925316 : Nat := 4983230072969 + 3 ^ 40 * 2925316 * 2
def baseEnd_2925316 : Nat := 1502093174287981921396723

theorem tailTrace_2925316 : CollatzResearch.WordTrace tailWord_2925316 prefixEnd_2925316 1502093174287981921396723 := by
  unfold tailWord_2925316
  simp only [CollatzResearch.WordTrace]
  refine ⟨53347519935043605521193901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71130026580058140694925201 53347519935043605521193901)
  ·
    refine ⟨20005319975641352070447713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53347519935043605521193901 20005319975641352070447713)
    ·
      refine ⟨15003989981731014052835785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20005319975641352070447713 15003989981731014052835785)
      ·
        refine ⟨11252992486298260539626839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15003989981731014052835785 11252992486298260539626839)
        ·
          refine ⟨16879488729447390809440259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11252992486298260539626839 16879488729447390809440259)
          ·
            refine ⟨25319233094171086214160389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16879488729447390809440259 25319233094171086214160389)
            ·
              refine ⟨4747356205157078665155073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25319233094171086214160389 4747356205157078665155073)
              ·
                refine ⟨3560517153867808998866305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4747356205157078665155073 3560517153867808998866305)
                ·
                  refine ⟨2670387865400856749149729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3560517153867808998866305 2670387865400856749149729)
                  ·
                    refine ⟨2002790899050642561862297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2670387865400856749149729 2002790899050642561862297)
                    ·
                      refine ⟨1502093174287981921396723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2002790899050642561862297 1502093174287981921396723)
                      ·
                        rfl

theorem cell23_2925316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_2925316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925316 prefixEnd_2925316 := by exact prefixLift 2925316
  have htrace : WordTrace (prefixWord ++ tailWord_2925316) baseStart_2925316 baseEnd_2925316 := by
    simpa [prefixWord, tailWord_2925316, baseEnd_2925316] using wordTrace_append hprefix tailTrace_2925316
  have hstable : (prefixWord ++ tailWord_2925316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925316).length < 2 ^ (prefixWord ++ tailWord_2925316).sum := by decide
  have hdescent : baseEnd_2925316 < baseStart_2925316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925322 : List Nat := [3, 1, 2, 2, 1, 2, 3, 4, 5]
def baseStart_2925322 : Nat := 118140960795 + 2925322 * 2 ^ 59
def prefixEnd_2925322 : Nat := 4983230072969 + 3 ^ 40 * 2925322 * 2
def baseEnd_2925322 : Nat := 166899583907989877546855

theorem tailTrace_2925322 : CollatzResearch.WordTrace tailWord_2925322 prefixEnd_2925322 166899583907989877546855 := by
  unfold tailWord_2925322
  simp only [CollatzResearch.WordTrace]
  refine ⟨26673814677016368516776555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71130172472043649378070813 26673814677016368516776555)
  ·
    refine ⟨40010722015524552775164833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26673814677016368516776555 40010722015524552775164833)
    ·
      refine ⟨30008041511643414581373625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40010722015524552775164833 30008041511643414581373625)
      ·
        refine ⟨22506031133732560936030219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30008041511643414581373625 22506031133732560936030219)
        ·
          refine ⟨33759046700598841404045329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22506031133732560936030219 33759046700598841404045329)
          ·
            refine ⟨25319285025449131053033997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33759046700598841404045329 25319285025449131053033997)
            ·
              refine ⟨9494731884543424144887749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25319285025449131053033997 9494731884543424144887749)
              ·
                refine ⟨1780262228351892027166453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9494731884543424144887749 1780262228351892027166453)
                ·
                  refine ⟨166899583907989877546855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1780262228351892027166453 166899583907989877546855)
                  ·
                    rfl

theorem cell23_2925322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_2925322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925322 prefixEnd_2925322 := by exact prefixLift 2925322
  have htrace : WordTrace (prefixWord ++ tailWord_2925322) baseStart_2925322 baseEnd_2925322 := by
    simpa [prefixWord, tailWord_2925322, baseEnd_2925322] using wordTrace_append hprefix tailTrace_2925322
  have hstable : (prefixWord ++ tailWord_2925322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925322).length < 2 ^ (prefixWord ++ tailWord_2925322).sum := by decide
  have hdescent : baseEnd_2925322 < baseStart_2925322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925395 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 6]
def baseStart_2925395 : Nat := 118140960795 + 2925395 * 2 ^ 59
def prefixEnd_2925395 : Nat := 4983230072969 + 3 ^ 40 * 2925395 * 2
def baseEnd_2925395 : Nat := 166903748806631901367651

theorem tailTrace_2925395 : CollatzResearch.WordTrace tailWord_2925395 prefixEnd_2925395 166903748806631901367651 := by
  unfold tailWord_2925395
  simp only [CollatzResearch.WordTrace]
  refine ⟨106697921236801007534513639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71131947491200671689675759 106697921236801007534513639)
  ·
    refine ⟨160046881855201511301770459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106697921236801007534513639 160046881855201511301770459)
    ·
      refine ⟨240070322782802266952655689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160046881855201511301770459 240070322782802266952655689)
      ·
        refine ⟨180052742087101700214491767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240070322782802266952655689 180052742087101700214491767)
        ·
          refine ⟨270079113130652550321737651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180052742087101700214491767 270079113130652550321737651)
          ·
            refine ⟨405118669695978825482606477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270079113130652550321737651 405118669695978825482606477)
            ·
              refine ⟨151919501135992059555977429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 405118669695978825482606477 151919501135992059555977429)
              ·
                refine ⟨3560613307874813895843221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151919501135992059555977429 3560613307874813895843221)
                ·
                  refine ⟨166903748806631901367651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3560613307874813895843221 166903748806631901367651)
                  ·
                    rfl

theorem cell23_2925395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 6].length) (baseStart_2925395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925395 prefixEnd_2925395 := by exact prefixLift 2925395
  have htrace : WordTrace (prefixWord ++ tailWord_2925395) baseStart_2925395 baseEnd_2925395 := by
    simpa [prefixWord, tailWord_2925395, baseEnd_2925395] using wordTrace_append hprefix tailTrace_2925395
  have hstable : (prefixWord ++ tailWord_2925395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925395).length < 2 ^ (prefixWord ++ tailWord_2925395).sum := by decide
  have hdescent : baseEnd_2925395 < baseStart_2925395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925416 : List Nat := [2, 1, 4, 2, 1, 2, 3, 3, 1, 4]
def baseStart_2925416 : Nat := 118140960795 + 2925416 * 2 ^ 59
def prefixEnd_2925416 : Nat := 4983230072969 + 3 ^ 40 * 2925416 * 2
def baseEnd_2925416 : Nat := 500714840784477176715421

theorem tailTrace_2925416 : CollatzResearch.WordTrace tailWord_2925416 prefixEnd_2925416 500714840784477176715421 := by
  unfold tailWord_2925416
  simp only [CollatzResearch.WordTrace]
  refine ⟨53349343584862464060514051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71132458113149952080685401 53349343584862464060514051)
  ·
    refine ⟨80024015377293696090771077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53349343584862464060514051 80024015377293696090771077)
    ·
      refine ⟨15004502883242568017019577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80024015377293696090771077 15004502883242568017019577)
      ·
        refine ⟨11253377162431926012764683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15004502883242568017019577 11253377162431926012764683)
        ·
          refine ⟨16880065743647889019147025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11253377162431926012764683 16880065743647889019147025)
          ·
            refine ⟨12660049307735916764360269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16880065743647889019147025 12660049307735916764360269)
            ·
              refine ⟨4747518490400968786635101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12660049307735916764360269 4747518490400968786635101)
              ·
                refine ⟨1780319433900363294988163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4747518490400968786635101 1780319433900363294988163)
                ·
                  refine ⟨2670479150850544942482245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780319433900363294988163 2670479150850544942482245)
                  ·
                    refine ⟨500714840784477176715421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2670479150850544942482245 500714840784477176715421)
                    ·
                      rfl

theorem cell23_2925416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_2925416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925416 prefixEnd_2925416 := by exact prefixLift 2925416
  have htrace : WordTrace (prefixWord ++ tailWord_2925416) baseStart_2925416 baseEnd_2925416 := by
    simpa [prefixWord, tailWord_2925416, baseEnd_2925416] using wordTrace_append hprefix tailTrace_2925416
  have hstable : (prefixWord ++ tailWord_2925416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925416).length < 2 ^ (prefixWord ++ tailWord_2925416).sum := by decide
  have hdescent : baseEnd_2925416 < baseStart_2925416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925432 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 3, 5, 2]
def baseStart_2925432 : Nat := 118140960795 + 2925432 * 2 ^ 59
def prefixEnd_2925432 : Nat := 4983230072969 + 3 ^ 40 * 2925432 * 2
def baseEnd_2925432 : Nat := 1502152738043903467546189

theorem tailTrace_2925432 : CollatzResearch.WordTrace tailWord_2925432 prefixEnd_2925432 1502152738043903467546189 := by
  unfold tailWord_2925432
  simp only [CollatzResearch.WordTrace]
  refine ⟨53349635368833481426805275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71132847158444641902407033 53349635368833481426805275)
  ·
    refine ⟨80024453053250222140207913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53349635368833481426805275 80024453053250222140207913)
    ·
      refine ⟨60018339789937666605155935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80024453053250222140207913 60018339789937666605155935)
      ·
        refine ⟨90027509684906499907733903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60018339789937666605155935 90027509684906499907733903)
        ·
          refine ⟨135041264527359749861600855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90027509684906499907733903 135041264527359749861600855)
          ·
            refine ⟨202561896791039624792401283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135041264527359749861600855 202561896791039624792401283)
            ·
              refine ⟨303842845186559437188601925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202561896791039624792401283 303842845186559437188601925)
              ·
                refine ⟨56970533472479894472862861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303842845186559437188601925 56970533472479894472862861)
                ·
                  refine ⟨21363950052179960427323573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56970533472479894472862861 21363950052179960427323573)
                  ·
                    refine ⟨2002870317391871290061585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21363950052179960427323573 2002870317391871290061585)
                    ·
                      refine ⟨1502152738043903467546189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2002870317391871290061585 1502152738043903467546189)
                      ·
                        rfl

theorem cell23_2925432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 5, 2].length) (baseStart_2925432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925432 prefixEnd_2925432 := by exact prefixLift 2925432
  have htrace : WordTrace (prefixWord ++ tailWord_2925432) baseStart_2925432 baseEnd_2925432 := by
    simpa [prefixWord, tailWord_2925432, baseEnd_2925432] using wordTrace_append hprefix tailTrace_2925432
  have hstable : (prefixWord ++ tailWord_2925432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925432).length < 2 ^ (prefixWord ++ tailWord_2925432).sum := by decide
  have hdescent : baseEnd_2925432 < baseStart_2925432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925439 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 3, 1, 3]
def baseStart_2925439 : Nat := 118140960795 + 2925439 * 2 ^ 59
def prefixEnd_2925439 : Nat := 4983230072969 + 3 ^ 40 * 2925439 * 2
def baseEnd_2925439 : Nat := 1502156332408484940158657

theorem tailTrace_2925439 : CollatzResearch.WordTrace tailWord_2925439 prefixEnd_2925439 1502156332408484940158657 := by
  unfold tailWord_2925439
  simp only [CollatzResearch.WordTrace]
  refine ⟨106699526048641603049115371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71133017365761068699410247 106699526048641603049115371)
  ·
    refine ⟨160049289072962404573673057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106699526048641603049115371 160049289072962404573673057)
    ·
      refine ⟨120036966804721803430254793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160049289072962404573673057 120036966804721803430254793)
      ·
        refine ⟨90027725103541352572691095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120036966804721803430254793 90027725103541352572691095)
        ·
          refine ⟨135041587655312028859036643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90027725103541352572691095 135041587655312028859036643)
          ·
            refine ⟨202562381482968043288554965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135041587655312028859036643 202562381482968043288554965)
            ·
              refine ⟨4747555816007063514575507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 202562381482968043288554965 4747555816007063514575507)
              ·
                refine ⟨7121333724010595271863261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4747555816007063514575507 7121333724010595271863261)
                ·
                  refine ⟨2670500146503973226948723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7121333724010595271863261 2670500146503973226948723)
                  ·
                    refine ⟨4005750219755959840423085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2670500146503973226948723 4005750219755959840423085)
                    ·
                      refine ⟨1502156332408484940158657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4005750219755959840423085 1502156332408484940158657)
                      ·
                        rfl

theorem cell23_2925439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_2925439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925439 prefixEnd_2925439 := by exact prefixLift 2925439
  have htrace : WordTrace (prefixWord ++ tailWord_2925439) baseStart_2925439 baseEnd_2925439 := by
    simpa [prefixWord, tailWord_2925439, baseEnd_2925439] using wordTrace_append hprefix tailTrace_2925439
  have hstable : (prefixWord ++ tailWord_2925439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925439).length < 2 ^ (prefixWord ++ tailWord_2925439).sum := by decide
  have hdescent : baseEnd_2925439 < baseStart_2925439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925472 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 6, 4]
def baseStart_2925472 : Nat := 118140960795 + 2925472 * 2 ^ 59
def prefixEnd_2925472 : Nat := 4983230072969 + 3 ^ 40 * 2925472 * 2
def baseEnd_2925472 : Nat := 500724425756694437015335

theorem tailTrace_2925472 : CollatzResearch.WordTrace tailWord_2925472 prefixEnd_2925472 500724425756694437015335 := by
  unfold tailWord_2925472
  simp only [CollatzResearch.WordTrace]
  refine ⟨53350364828761024842533335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71133819771681366456711113 53350364828761024842533335)
  ·
    refine ⟨80025547243141537263800003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53350364828761024842533335 80025547243141537263800003)
    ·
      refine ⟨120038320864712305895700005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80025547243141537263800003 120038320864712305895700005)
      ·
        refine ⟨22507185162133557355443751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120038320864712305895700005 22507185162133557355443751)
        ·
          refine ⟨33760777743200336033165627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22507185162133557355443751 33760777743200336033165627)
          ·
            refine ⟨50641166614800504049748441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33760777743200336033165627 50641166614800504049748441)
            ·
              refine ⟨37980874961100378037311331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50641166614800504049748441 37980874961100378037311331)
              ·
                refine ⟨56971312441650567055966997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37980874961100378037311331 56971312441650567055966997)
                ·
                  refine ⟨2670530270702370330748453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56971312441650567055966997 2670530270702370330748453)
                  ·
                    refine ⟨500724425756694437015335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2670530270702370330748453 500724425756694437015335)
                    ·
                      rfl

theorem cell23_2925472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6, 4].length) (baseStart_2925472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925472 prefixEnd_2925472 := by exact prefixLift 2925472
  have htrace : WordTrace (prefixWord ++ tailWord_2925472) baseStart_2925472 baseEnd_2925472 := by
    simpa [prefixWord, tailWord_2925472, baseEnd_2925472] using wordTrace_append hprefix tailTrace_2925472
  have hstable : (prefixWord ++ tailWord_2925472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925472).length < 2 ^ (prefixWord ++ tailWord_2925472).sum := by decide
  have hdescent : baseEnd_2925472 < baseStart_2925472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925526 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2925526 : Nat := 118140960795 + 2925526 * 2 ^ 59
def prefixEnd_2925526 : Nat := 4983230072969 + 3 ^ 40 * 2925526 * 2
def baseEnd_2925526 : Nat := 1502201005225426099770757

theorem tailTrace_2925526 : CollatzResearch.WordTrace tailWord_2925526 prefixEnd_2925526 1502201005225426099770757 := by
  unfold tailWord_2925526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668918699957901056720777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71135132799550944605021621 6668918699957901056720777)
  ·
    refine ⟨5001689024968425792540583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6668918699957901056720777 5001689024968425792540583)
    ·
      refine ⟨7502533537452638688810875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5001689024968425792540583 7502533537452638688810875)
      ·
        refine ⟨11253800306178958033216313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7502533537452638688810875 11253800306178958033216313)
        ·
          refine ⟨8440350229634218524912235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11253800306178958033216313 8440350229634218524912235)
          ·
            refine ⟨12660525344451327787368353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440350229634218524912235 12660525344451327787368353)
            ·
              refine ⟨9495394008338495840526265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12660525344451327787368353 9495394008338495840526265)
              ·
                refine ⟨7121545506253871880394699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9495394008338495840526265 7121545506253871880394699)
                ·
                  refine ⟨10682318259380807820592049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7121545506253871880394699 10682318259380807820592049)
                  ·
                    refine ⟨8011738694535605865444037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10682318259380807820592049 8011738694535605865444037)
                    ·
                      refine ⟨1502201005225426099770757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8011738694535605865444037 1502201005225426099770757)
                      ·
                        rfl

theorem cell23_2925526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2925526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925526 prefixEnd_2925526 := by exact prefixLift 2925526
  have htrace : WordTrace (prefixWord ++ tailWord_2925526) baseStart_2925526 baseEnd_2925526 := by
    simpa [prefixWord, tailWord_2925526, baseEnd_2925526] using wordTrace_append hprefix tailTrace_2925526
  have hstable : (prefixWord ++ tailWord_2925526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925526).length < 2 ^ (prefixWord ++ tailWord_2925526).sum := by decide
  have hdescent : baseEnd_2925526 < baseStart_2925526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925529 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 1, 3, 3]
def baseStart_2925529 : Nat := 118140960795 + 2925529 * 2 ^ 59
def prefixEnd_2925529 : Nat := 4983230072969 + 3 ^ 40 * 2925529 * 2
def baseEnd_2925529 : Nat := 1502202545667389588033243

theorem tailTrace_2925529 : CollatzResearch.WordTrace tailWord_2925529 prefixEnd_2925529 1502202545667389588033243 := by
  unfold tailWord_2925529
  simp only [CollatzResearch.WordTrace]
  refine ⟨106702808618315548419891641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71135205745543698946594427 106702808618315548419891641)
  ·
    refine ⟨80027106463736661314918731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106702808618315548419891641 80027106463736661314918731)
    ·
      refine ⟨120040659695604991972378097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80027106463736661314918731 120040659695604991972378097)
      ·
        refine ⟨90030494771703743979283573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120040659695604991972378097 90030494771703743979283573)
        ·
          refine ⟨8440358884847225998057835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90030494771703743979283573 8440358884847225998057835)
          ·
            refine ⟨12660538327270838997086753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440358884847225998057835 12660538327270838997086753)
            ·
              refine ⟨9495403745453129247815065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12660538327270838997086753 9495403745453129247815065)
              ·
                refine ⟨7121552809089846935861299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9495403745453129247815065 7121552809089846935861299)
                ·
                  refine ⟨10682329213634770403791949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7121552809089846935861299 10682329213634770403791949)
                  ·
                    refine ⟨4005873455113038901421981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10682329213634770403791949 4005873455113038901421981)
                    ·
                      refine ⟨1502202545667389588033243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4005873455113038901421981 1502202545667389588033243)
                      ·
                        rfl

theorem cell23_2925529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_2925529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925529 prefixEnd_2925529 := by exact prefixLift 2925529
  have htrace : WordTrace (prefixWord ++ tailWord_2925529) baseStart_2925529 baseEnd_2925529 := by
    simpa [prefixWord, tailWord_2925529, baseEnd_2925529] using wordTrace_append hprefix tailTrace_2925529
  have hstable : (prefixWord ++ tailWord_2925529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925529).length < 2 ^ (prefixWord ++ tailWord_2925529).sum := by decide
  have hdescent : baseEnd_2925529 < baseStart_2925529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925530 : List Nat := [3, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2]
def baseStart_2925530 : Nat := 118140960795 + 2925530 * 2 ^ 59
def prefixEnd_2925530 : Nat := 4983230072969 + 3 ^ 40 * 2925530 * 2
def baseEnd_2925530 : Nat := 1502203059148044084120739

theorem tailTrace_2925530 : CollatzResearch.WordTrace tailWord_2925530 prefixEnd_2925530 1502203059148044084120739 := by
  unfold tailWord_2925530
  simp only [CollatzResearch.WordTrace]
  refine ⟨26675711272827981397669511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71135230060874617060452029 26675711272827981397669511)
  ·
    refine ⟨40013566909241972096504267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26675711272827981397669511 40013566909241972096504267)
    ·
      refine ⟨60020350363862958144756401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40013566909241972096504267 60020350363862958144756401)
      ·
        refine ⟨45015262772897218608567301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60020350363862958144756401 45015262772897218608567301)
        ·
          refine ⟨8440361769918228489106369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45015262772897218608567301 8440361769918228489106369)
          ·
            refine ⟨6330271327438671366829777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8440361769918228489106369 6330271327438671366829777)
            ·
              refine ⟨4747703495579003525122333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6330271327438671366829777 4747703495579003525122333)
              ·
                refine ⟨1780388810842126321920875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4747703495579003525122333 1780388810842126321920875)
                ·
                  refine ⟨2670583216263189482881313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780388810842126321920875 2670583216263189482881313)
                  ·
                    refine ⟨2002937412197392112160985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2670583216263189482881313 2002937412197392112160985)
                    ·
                      refine ⟨1502203059148044084120739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2002937412197392112160985 1502203059148044084120739)
                      ·
                        rfl

theorem cell23_2925530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_2925530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925530 prefixEnd_2925530 := by exact prefixLift 2925530
  have htrace : WordTrace (prefixWord ++ tailWord_2925530) baseStart_2925530 baseEnd_2925530 := by
    simpa [prefixWord, tailWord_2925530, baseEnd_2925530] using wordTrace_append hprefix tailTrace_2925530
  have hstable : (prefixWord ++ tailWord_2925530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925530).length < 2 ^ (prefixWord ++ tailWord_2925530).sum := by decide
  have hdescent : baseEnd_2925530 < baseStart_2925530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925533 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_2925533 : Nat := 118140960795 + 2925533 * 2 ^ 59
def prefixEnd_2925533 : Nat := 4983230072969 + 3 ^ 40 * 2925533 * 2
def baseEnd_2925533 : Nat := 1502204599590007572383225

theorem tailTrace_2925533 : CollatzResearch.WordTrace tailWord_2925533 prefixEnd_2925533 1502204599590007572383225 := by
  unfold tailWord_2925533
  simp only [CollatzResearch.WordTrace]
  refine ⟨106702954510301057103037253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71135303006867371402024835 106702954510301057103037253)
  ·
    refine ⟨20006803970681448206819485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106702954510301057103037253 20006803970681448206819485)
    ·
      refine ⟨7502551489005543077557307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20006803970681448206819485 7502551489005543077557307)
      ·
        refine ⟨11253827233508314616335961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7502551489005543077557307 11253827233508314616335961)
        ·
          refine ⟨8440370425131235962251971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11253827233508314616335961 8440370425131235962251971)
          ·
            refine ⟨12660555637696853943377957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440370425131235962251971 12660555637696853943377957)
            ·
              refine ⟨2373854182068160114383367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12660555637696853943377957 2373854182068160114383367)
              ·
                refine ⟨3560781273102240171575051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373854182068160114383367 3560781273102240171575051)
                ·
                  refine ⟨5341171909653360257362577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560781273102240171575051 5341171909653360257362577)
                  ·
                    refine ⟨4005878932240020193021933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5341171909653360257362577 4005878932240020193021933)
                    ·
                      refine ⟨1502204599590007572383225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4005878932240020193021933 1502204599590007572383225)
                      ·
                        rfl

theorem cell23_2925533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_2925533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925533 prefixEnd_2925533 := by exact prefixLift 2925533
  have htrace : WordTrace (prefixWord ++ tailWord_2925533) baseStart_2925533 baseEnd_2925533 := by
    simpa [prefixWord, tailWord_2925533, baseEnd_2925533] using wordTrace_append hprefix tailTrace_2925533
  have hstable : (prefixWord ++ tailWord_2925533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925533).length < 2 ^ (prefixWord ++ tailWord_2925533).sum := by decide
  have hdescent : baseEnd_2925533 < baseStart_2925533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925546 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_2925546 : Nat := 118140960795 + 2925546 * 2 ^ 59
def prefixEnd_2925546 : Nat := 4983230072969 + 3 ^ 40 * 2925546 * 2
def baseEnd_2925546 : Nat := 1502211274838516021520665

theorem tailTrace_2925546 : CollatzResearch.WordTrace tailWord_2925546 prefixEnd_2925546 1502211274838516021520665 := by
  unfold tailWord_2925546
  simp only [CollatzResearch.WordTrace]
  refine ⟨26675857164813490080815123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71135619106169306882173661 26675857164813490080815123)
  ·
    refine ⟨40013785747220235121222685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26675857164813490080815123 40013785747220235121222685)
    ·
      refine ⟨15005169655207588170458507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40013785747220235121222685 15005169655207588170458507)
      ·
        refine ⟨22507754482811382255687761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15005169655207588170458507 22507754482811382255687761)
        ·
          refine ⟨16880815862108536691765821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22507754482811382255687761 16880815862108536691765821)
          ·
            refine ⟨6330305948290701259412183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16880815862108536691765821 6330305948290701259412183)
            ·
              refine ⟨9495458922436051889118275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330305948290701259412183 9495458922436051889118275)
              ·
                refine ⟨14243188383654077833677413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495458922436051889118275 14243188383654077833677413)
                ·
                  refine ⟨2670597821935139593814515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14243188383654077833677413 2670597821935139593814515)
                  ·
                    refine ⟨4005896732902709390721773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2670597821935139593814515 4005896732902709390721773)
                    ·
                      refine ⟨1502211274838516021520665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4005896732902709390721773 1502211274838516021520665)
                      ·
                        rfl

theorem cell23_2925546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_2925546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925546 prefixEnd_2925546 := by exact prefixLift 2925546
  have htrace : WordTrace (prefixWord ++ tailWord_2925546) baseStart_2925546 baseEnd_2925546 := by
    simpa [prefixWord, tailWord_2925546, baseEnd_2925546] using wordTrace_append hprefix tailTrace_2925546
  have hstable : (prefixWord ++ tailWord_2925546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925546).length < 2 ^ (prefixWord ++ tailWord_2925546).sum := by decide
  have hdescent : baseEnd_2925546 < baseStart_2925546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925570 : List Nat := [3, 4, 1, 3, 2, 1, 2, 7]
def baseStart_2925570 : Nat := 118140960795 + 2925570 * 2 ^ 59
def prefixEnd_2925570 : Nat := 4983230072969 + 3 ^ 40 * 2925570 * 2
def baseEnd_2925570 : Nat := 55637911050897182504465

theorem tailTrace_2925570 : CollatzResearch.WordTrace tailWord_2925570 prefixEnd_2925570 55637911050897182504465 := by
  unfold tailWord_2925570
  simp only [CollatzResearch.WordTrace]
  refine ⟨26676076002791753105533541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71136202674111341614756109 26676076002791753105533541)
  ·
    refine ⟨5001764250523453707287539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26676076002791753105533541 5001764250523453707287539)
    ·
      refine ⟨7502646375785180560931309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5001764250523453707287539 7502646375785180560931309)
      ·
        refine ⟨2813492390919442710349241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7502646375785180560931309 2813492390919442710349241)
        ·
          refine ⟨2110119293189582032761931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2813492390919442710349241 2110119293189582032761931)
          ·
            refine ⟨3165178939784373049142897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110119293189582032761931 3165178939784373049142897)
            ·
              refine ⟨2373884204838279786857173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3165178939784373049142897 2373884204838279786857173)
              ·
                refine ⟨55637911050897182504465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2373884204838279786857173 55637911050897182504465)
                ·
                  rfl

theorem cell23_2925570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 7].length) (baseStart_2925570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925570 prefixEnd_2925570 := by exact prefixLift 2925570
  have htrace : WordTrace (prefixWord ++ tailWord_2925570) baseStart_2925570 baseEnd_2925570 := by
    simpa [prefixWord, tailWord_2925570, baseEnd_2925570] using wordTrace_append hprefix tailTrace_2925570
  have hstable : (prefixWord ++ tailWord_2925570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925570).length < 2 ^ (prefixWord ++ tailWord_2925570).sum := by decide
  have hdescent : baseEnd_2925570 < baseStart_2925570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925589 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_2925589 : Nat := 118140960795 + 2925589 * 2 ^ 59
def prefixEnd_2925589 : Nat := 4983230072969 + 3 ^ 40 * 2925589 * 2
def baseEnd_2925589 : Nat := 1502233354506659353282967

theorem tailTrace_2925589 : CollatzResearch.WordTrace tailWord_2925589 prefixEnd_2925589 1502233354506659353282967 := by
  unfold tailWord_2925589
  simp only [CollatzResearch.WordTrace]
  refine ⟨106704996998098178667075821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71136664665398785778050547 106704996998098178667075821)
  ·
    refine ⟨40014373874286817000153433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106704996998098178667075821 40014373874286817000153433)
    ·
      refine ⟨30010780405715112750115075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40014373874286817000153433 30010780405715112750115075)
      ·
        refine ⟨45016170608572669125172613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30010780405715112750115075 45016170608572669125172613)
        ·
          refine ⟨8440531989107375460969865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45016170608572669125172613 8440531989107375460969865)
          ·
            refine ⟨6330398991830531595727399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8440531989107375460969865 6330398991830531595727399)
            ·
              refine ⟨9495598487745797393591099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330398991830531595727399 9495598487745797393591099)
              ·
                refine ⟨14243397731618696090386649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495598487745797393591099 14243397731618696090386649)
                ·
                  refine ⟨10682548298714022067789987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14243397731618696090386649 10682548298714022067789987)
                  ·
                    refine ⟨16023822448071033101684981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10682548298714022067789987 16023822448071033101684981)
                    ·
                      refine ⟨1502233354506659353282967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16023822448071033101684981 1502233354506659353282967)
                      ·
                        rfl

theorem cell23_2925589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_2925589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925589 prefixEnd_2925589 := by exact prefixLift 2925589
  have htrace : WordTrace (prefixWord ++ tailWord_2925589) baseStart_2925589 baseEnd_2925589 := by
    simpa [prefixWord, tailWord_2925589, baseEnd_2925589] using wordTrace_append hprefix tailTrace_2925589
  have hstable : (prefixWord ++ tailWord_2925589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925589).length < 2 ^ (prefixWord ++ tailWord_2925589).sum := by decide
  have hdescent : baseEnd_2925589 < baseStart_2925589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925632 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_2925632 : Nat := 118140960795 + 2925632 * 2 ^ 59
def prefixEnd_2925632 : Nat := 4983230072969 + 3 ^ 40 * 2925632 * 2
def baseEnd_2925632 : Nat := 1502255434174802685045269

theorem tailTrace_2925632 : CollatzResearch.WordTrace tailWord_2925632 prefixEnd_2925632 1502255434174802685045269 := by
  unfold tailWord_2925632
  simp only [CollatzResearch.WordTrace]
  refine ⟨53353282668471198505445575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71137710224628264673927433 53353282668471198505445575)
  ·
    refine ⟨80029924002706797758168363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53353282668471198505445575 80029924002706797758168363)
    ·
      refine ⟨120044886004060196637252545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80029924002706797758168363 120044886004060196637252545)
      ·
        refine ⟨90033664503045147477939409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120044886004060196637252545 90033664503045147477939409)
        ·
          refine ⟨67525248377283860608454557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90033664503045147477939409 67525248377283860608454557)
          ·
            refine ⟨25321968141481447728170459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67525248377283860608454557 25321968141481447728170459)
            ·
              refine ⟨37982952212222171592255689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25321968141481447728170459 37982952212222171592255689)
              ·
                refine ⟨28487214159166628694191767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37982952212222171592255689 28487214159166628694191767)
                ·
                  refine ⟨42730821238749943041287651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28487214159166628694191767 42730821238749943041287651)
                  ·
                    refine ⟨64096231858124914561931477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42730821238749943041287651 64096231858124914561931477)
                    ·
                      refine ⟨1502255434174802685045269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64096231858124914561931477 1502255434174802685045269)
                      ·
                        rfl

theorem cell23_2925632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_2925632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925632 prefixEnd_2925632 := by exact prefixLift 2925632
  have htrace : WordTrace (prefixWord ++ tailWord_2925632) baseStart_2925632 baseEnd_2925632 := by
    simpa [prefixWord, tailWord_2925632, baseEnd_2925632] using wordTrace_append hprefix tailTrace_2925632
  have hstable : (prefixWord ++ tailWord_2925632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925632).length < 2 ^ (prefixWord ++ tailWord_2925632).sum := by decide
  have hdescent : baseEnd_2925632 < baseStart_2925632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925639 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 2, 5]
def baseStart_2925639 : Nat := 118140960795 + 2925639 * 2 ^ 59
def prefixEnd_2925639 : Nat := 4983230072969 + 3 ^ 40 * 2925639 * 2
def baseEnd_2925639 : Nat := 500753009513128052552579

theorem tailTrace_2925639 : CollatzResearch.WordTrace tailWord_2925639 prefixEnd_2925639 500753009513128052552579 := by
  unfold tailWord_2925639
  simp only [CollatzResearch.WordTrace]
  refine ⟨106706820647917037206395971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71137880431944691470930647 106706820647917037206395971)
  ·
    refine ⟨160060230971875555809593957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106706820647917037206395971 160060230971875555809593957)
    ·
      refine ⟨30011293307226666714298867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160060230971875555809593957 30011293307226666714298867)
      ·
        refine ⟨45016939960840000071448301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30011293307226666714298867 45016939960840000071448301)
        ·
          refine ⟨16881352485315000026793113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45016939960840000071448301 16881352485315000026793113)
          ·
            refine ⟨12661014363986250020094835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16881352485315000026793113 12661014363986250020094835)
            ·
              refine ⟨18991521545979375030142253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12661014363986250020094835 18991521545979375030142253)
              ·
                refine ⟨7121820579742265636303345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18991521545979375030142253 7121820579742265636303345)
                ·
                  refine ⟨5341365434806699227227509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7121820579742265636303345 5341365434806699227227509)
                  ·
                    refine ⟨500753009513128052552579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5341365434806699227227509 500753009513128052552579)
                    ·
                      rfl

theorem cell23_2925639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_2925639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925639 prefixEnd_2925639 := by exact prefixLift 2925639
  have htrace : WordTrace (prefixWord ++ tailWord_2925639) baseStart_2925639 baseEnd_2925639 := by
    simpa [prefixWord, tailWord_2925639, baseEnd_2925639] using wordTrace_append hprefix tailTrace_2925639
  have hstable : (prefixWord ++ tailWord_2925639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925639).length < 2 ^ (prefixWord ++ tailWord_2925639).sum := by decide
  have hdescent : baseEnd_2925639 < baseStart_2925639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925654 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_2925654 : Nat := 118140960795 + 2925654 * 2 ^ 59
def prefixEnd_2925654 : Nat := 4983230072969 + 3 ^ 40 * 2925654 * 2
def baseEnd_2925654 : Nat := 1502266730749201598970169

theorem tailTrace_2925654 : CollatzResearch.WordTrace tailWord_2925654 prefixEnd_2925654 1502266730749201598970169 := by
  unfold tailWord_2925654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6669210483928918423012001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71138245161908463178794677 6669210483928918423012001)
  ·
    refine ⟨5001907862946688817259001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6669210483928918423012001 5001907862946688817259001)
    ·
      refine ⟨3751430897210016612944251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5001907862946688817259001 3751430897210016612944251)
      ·
        refine ⟨5627146345815024919416377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751430897210016612944251 5627146345815024919416377)
        ·
          refine ⟨4220359759361268689562283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5627146345815024919416377 4220359759361268689562283)
          ·
            refine ⟨6330539639041903034343425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220359759361268689562283 6330539639041903034343425)
            ·
              refine ⟨4747904729281427275757569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6330539639041903034343425 4747904729281427275757569)
              ·
                refine ⟨3560928546961070456818177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4747904729281427275757569 3560928546961070456818177)
                ·
                  refine ⟨2670696410220802842613633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3560928546961070456818177 2670696410220802842613633)
                  ·
                    refine ⟨2003022307665602131960225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2670696410220802842613633 2003022307665602131960225)
                    ·
                      refine ⟨1502266730749201598970169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003022307665602131960225 1502266730749201598970169)
                      ·
                        rfl

theorem cell23_2925654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_2925654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925654 prefixEnd_2925654 := by exact prefixLift 2925654
  have htrace : WordTrace (prefixWord ++ tailWord_2925654) baseStart_2925654 baseEnd_2925654 := by
    simpa [prefixWord, tailWord_2925654, baseEnd_2925654] using wordTrace_append hprefix tailTrace_2925654
  have hstable : (prefixWord ++ tailWord_2925654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925654).length < 2 ^ (prefixWord ++ tailWord_2925654).sum := by decide
  have hdescent : baseEnd_2925654 < baseStart_2925654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925666 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2925666 : Nat := 118140960795 + 2925666 * 2 ^ 59
def prefixEnd_2925666 : Nat := 4983230072969 + 3 ^ 40 * 2925666 * 2
def baseEnd_2925666 : Nat := 1502272892517055552020113

theorem tailTrace_2925666 : CollatzResearch.WordTrace tailWord_2925666 prefixEnd_2925666 1502272892517055552020113 := by
  unfold tailWord_2925666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26676951354704805204407213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71138536945879480545085901 26676951354704805204407213)
  ·
    refine ⟨10003856758014301951652705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26676951354704805204407213 10003856758014301951652705)
    ·
      refine ⟨7502892568510726463739529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10003856758014301951652705 7502892568510726463739529)
      ·
        refine ⟨5627169426383044847804647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7502892568510726463739529 5627169426383044847804647)
        ·
          refine ⟨8440754139574567271706971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5627169426383044847804647 8440754139574567271706971)
          ·
            refine ⟨12661131209361850907560457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440754139574567271706971 12661131209361850907560457)
            ·
              refine ⟨9495848407021388180670343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12661131209361850907560457 9495848407021388180670343)
              ·
                refine ⟨14243772610532082271005515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495848407021388180670343 14243772610532082271005515)
                ·
                  refine ⟨21365658915798123406508273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14243772610532082271005515 21365658915798123406508273)
                  ·
                    refine ⟨16024244186848592554881205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21365658915798123406508273 16024244186848592554881205)
                    ·
                      refine ⟨1502272892517055552020113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16024244186848592554881205 1502272892517055552020113)
                      ·
                        rfl

theorem cell23_2925666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2925666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925666 prefixEnd_2925666 := by exact prefixLift 2925666
  have htrace : WordTrace (prefixWord ++ tailWord_2925666) baseStart_2925666 baseEnd_2925666 := by
    simpa [prefixWord, tailWord_2925666, baseEnd_2925666] using wordTrace_append hprefix tailTrace_2925666
  have hstable : (prefixWord ++ tailWord_2925666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925666).length < 2 ^ (prefixWord ++ tailWord_2925666).sum := by decide
  have hdescent : baseEnd_2925666 < baseStart_2925666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925676 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 2, 4, 2]
def baseStart_2925676 : Nat := 118140960795 + 2925676 * 2 ^ 59
def prefixEnd_2925676 : Nat := 4983230072969 + 3 ^ 40 * 2925676 * 2
def baseEnd_2925676 : Nat := 1502278027323600512895067

theorem tailTrace_2925676 : CollatzResearch.WordTrace tailWord_2925676 prefixEnd_2925676 1502278027323600512895067 := by
  unfold tailWord_2925676
  simp only [CollatzResearch.WordTrace]
  refine ⟨53354085074391496262746441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71138780099188661683661921 53354085074391496262746441)
  ·
    refine ⟨40015563805793622197059831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53354085074391496262746441 40015563805793622197059831)
    ·
      refine ⟨60023345708690433295589747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40015563805793622197059831 60023345708690433295589747)
      ·
        refine ⟨90035018563035649943384621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60023345708690433295589747 90035018563035649943384621)
        ·
          refine ⟨33763131961138368728769233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90035018563035649943384621 33763131961138368728769233)
          ·
            refine ⟨25322348970853776546576925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33763131961138368728769233 25322348970853776546576925)
            ·
              refine ⟨9495880864070166204966347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25322348970853776546576925 9495880864070166204966347)
              ·
                refine ⟨14243821296105249307449521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9495880864070166204966347 14243821296105249307449521)
                ·
                  refine ⟨10682865972078936980587141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14243821296105249307449521 10682865972078936980587141)
                  ·
                    refine ⟨2003037369764800683860089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10682865972078936980587141 2003037369764800683860089)
                    ·
                      refine ⟨1502278027323600512895067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003037369764800683860089 1502278027323600512895067)
                      ·
                        rfl

theorem cell23_2925676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 4, 2].length) (baseStart_2925676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925676 prefixEnd_2925676 := by exact prefixLift 2925676
  have htrace : WordTrace (prefixWord ++ tailWord_2925676) baseStart_2925676 baseEnd_2925676 := by
    simpa [prefixWord, tailWord_2925676, baseEnd_2925676] using wordTrace_append hprefix tailTrace_2925676
  have hstable : (prefixWord ++ tailWord_2925676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925676).length < 2 ^ (prefixWord ++ tailWord_2925676).sum := by decide
  have hdescent : baseEnd_2925676 < baseStart_2925676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925679 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 3]
def baseStart_2925679 : Nat := 118140960795 + 2925679 * 2 ^ 59
def prefixEnd_2925679 : Nat := 4983230072969 + 3 ^ 40 * 2925679 * 2
def baseEnd_2925679 : Nat := 1502279567765564001157553

theorem tailTrace_2925679 : CollatzResearch.WordTrace tailWord_2925679 prefixEnd_2925679 1502279567765564001157553 := by
  unfold tailWord_2925679
  simp only [CollatzResearch.WordTrace]
  refine ⟨106708279567772124037852091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71138853045181416025234727 106708279567772124037852091)
  ·
    refine ⟨160062419351658186056778137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106708279567772124037852091 160062419351658186056778137)
    ·
      refine ⟨120046814513743639542583603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160062419351658186056778137 120046814513743639542583603)
      ·
        refine ⟨180070221770615459313875405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120046814513743639542583603 180070221770615459313875405)
        ·
          refine ⟨67526333163980797242703277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180070221770615459313875405 67526333163980797242703277)
          ·
            refine ⟨25322374936492798966013729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67526333163980797242703277 25322374936492798966013729)
            ·
              refine ⟨18991781202369599224510297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25322374936492798966013729 18991781202369599224510297)
              ·
                refine ⟨14243835901777199418382723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18991781202369599224510297 14243835901777199418382723)
                ·
                  refine ⟨21365753852665799127574085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14243835901777199418382723 21365753852665799127574085)
                  ·
                    refine ⟨4006078847374837336420141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21365753852665799127574085 4006078847374837336420141)
                    ·
                      refine ⟨1502279567765564001157553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4006078847374837336420141 1502279567765564001157553)
                      ·
                        rfl

theorem cell23_2925679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 3].length) (baseStart_2925679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925679 prefixEnd_2925679 := by exact prefixLift 2925679
  have htrace : WordTrace (prefixWord ++ tailWord_2925679) baseStart_2925679 baseEnd_2925679 := by
    simpa [prefixWord, tailWord_2925679, baseEnd_2925679] using wordTrace_append hprefix tailTrace_2925679
  have hstable : (prefixWord ++ tailWord_2925679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925679).length < 2 ^ (prefixWord ++ tailWord_2925679).sum := by decide
  have hdescent : baseEnd_2925679 < baseStart_2925679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925696 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 3]
def baseStart_2925696 : Nat := 118140960795 + 2925696 * 2 ^ 59
def prefixEnd_2925696 : Nat := 4983230072969 + 3 ^ 40 * 2925696 * 2
def baseEnd_2925696 : Nat := 1502288296936690434644975

theorem tailTrace_2925696 : CollatzResearch.WordTrace tailWord_2925696 prefixEnd_2925696 1502288296936690434644975 := by
  unfold tailWord_2925696
  simp only [CollatzResearch.WordTrace]
  refine ⟨53354449804355267970610471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71139266405807023960813961 53354449804355267970610471)
  ·
    refine ⟨80031674706532901955915707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53354449804355267970610471 80031674706532901955915707)
    ·
      refine ⟨120047512059799352933873561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80031674706532901955915707 120047512059799352933873561)
      ·
        refine ⟨90035634044849514700405171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120047512059799352933873561 90035634044849514700405171)
        ·
          refine ⟨135053451067274272050607757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90035634044849514700405171 135053451067274272050607757)
          ·
            refine ⟨50645044150227852018977909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135053451067274272050607757 50645044150227852018977909)
            ·
              refine ⟨4747972889083861126779179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50645044150227852018977909 4747972889083861126779179)
              ·
                refine ⟨7121959333625791690168769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4747972889083861126779179 7121959333625791690168769)
                ·
                  refine ⟨5341469500219343767626577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7121959333625791690168769 5341469500219343767626577)
                  ·
                    refine ⟨4006102125164507825719933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5341469500219343767626577 4006102125164507825719933)
                    ·
                      refine ⟨1502288296936690434644975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4006102125164507825719933 1502288296936690434644975)
                      ·
                        rfl

theorem cell23_2925696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_2925696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925696 prefixEnd_2925696 := by exact prefixLift 2925696
  have htrace : WordTrace (prefixWord ++ tailWord_2925696) baseStart_2925696 baseEnd_2925696 := by
    simpa [prefixWord, tailWord_2925696, baseEnd_2925696] using wordTrace_append hprefix tailTrace_2925696
  have hstable : (prefixWord ++ tailWord_2925696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925696).length < 2 ^ (prefixWord ++ tailWord_2925696).sum := by decide
  have hdescent : baseEnd_2925696 < baseStart_2925696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925719 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2925719 : Nat := 118140960795 + 2925719 * 2 ^ 59
def prefixEnd_2925719 : Nat := 4983230072969 + 3 ^ 40 * 2925719 * 2
def baseEnd_2925719 : Nat := 1502300106991743844657369

theorem tailTrace_2925719 : CollatzResearch.WordTrace tailWord_2925719 prefixEnd_2925719 1502300106991743844657369 := by
  unfold tailWord_2925719
  simp only [CollatzResearch.WordTrace]
  refine ⟨106709738487627210869308211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71139825658418140579538807 106709738487627210869308211)
  ·
    refine ⟨160064607731440816303962317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106709738487627210869308211 160064607731440816303962317)
    ·
      refine ⟨60024227899290306113985869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160064607731440816303962317 60024227899290306113985869)
      ·
        refine ⟨22509085462233864792744701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60024227899290306113985869 22509085462233864792744701)
        ·
          refine ⟨8440907048337699297279263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22509085462233864792744701 8440907048337699297279263)
          ·
            refine ⟨12661360572506548945918895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440907048337699297279263 12661360572506548945918895)
            ·
              refine ⟨18992040858759823418878343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12661360572506548945918895 18992040858759823418878343)
              ·
                refine ⟨28488061288139735128317515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18992040858759823418878343 28488061288139735128317515)
                ·
                  refine ⟨42732091932209602692476273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28488061288139735128317515 42732091932209602692476273)
                  ·
                    refine ⟨32049068949157202019357205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42732091932209602692476273 32049068949157202019357205)
                    ·
                      refine ⟨1502300106991743844657369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32049068949157202019357205 1502300106991743844657369)
                      ·
                        rfl

theorem cell23_2925719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2925719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925719 prefixEnd_2925719 := by exact prefixLift 2925719
  have htrace : WordTrace (prefixWord ++ tailWord_2925719) baseStart_2925719 baseEnd_2925719 := by
    simpa [prefixWord, tailWord_2925719, baseEnd_2925719] using wordTrace_append hprefix tailTrace_2925719
  have hstable : (prefixWord ++ tailWord_2925719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925719).length < 2 ^ (prefixWord ++ tailWord_2925719).sum := by decide
  have hdescent : baseEnd_2925719 < baseStart_2925719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925746 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_2925746 : Nat := 118140960795 + 2925746 * 2 ^ 59
def prefixEnd_2925746 : Nat := 4983230072969 + 3 ^ 40 * 2925746 * 2
def baseEnd_2925746 : Nat := 500771323656471746339915

theorem tailTrace_2925746 : CollatzResearch.WordTrace tailWord_2925746 prefixEnd_2925746 500771323656471746339915 := by
  unfold tailWord_2925746
  simp only [CollatzResearch.WordTrace]
  refine ⟨26677680814632348620135273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71140482172352929653694061 26677680814632348620135273)
  ·
    refine ⟨20008260610974261465101455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26677680814632348620135273 20008260610974261465101455)
    ·
      refine ⟨30012390916461392197652183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20008260610974261465101455 30012390916461392197652183)
      ·
        refine ⟨45018586374692088296478275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30012390916461392197652183 45018586374692088296478275)
        ·
          refine ⟨67527879562038132444717413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45018586374692088296478275 67527879562038132444717413)
          ·
            refine ⟨12661477417882149833384515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67527879562038132444717413 12661477417882149833384515)
            ·
              refine ⟨18992216126823224750076773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12661477417882149833384515 18992216126823224750076773)
              ·
                refine ⟨3561040523779354640639395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18992216126823224750076773 3561040523779354640639395)
                ·
                  refine ⟨5341560785669031960959093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561040523779354640639395 5341560785669031960959093)
                  ·
                    refine ⟨500771323656471746339915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5341560785669031960959093 500771323656471746339915)
                    ·
                      rfl

theorem cell23_2925746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_2925746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925746 prefixEnd_2925746 := by exact prefixLift 2925746
  have htrace : WordTrace (prefixWord ++ tailWord_2925746) baseStart_2925746 baseEnd_2925746 := by
    simpa [prefixWord, tailWord_2925746, baseEnd_2925746] using wordTrace_append hprefix tailTrace_2925746
  have hstable : (prefixWord ++ tailWord_2925746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925746).length < 2 ^ (prefixWord ++ tailWord_2925746).sum := by decide
  have hdescent : baseEnd_2925746 < baseStart_2925746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925759 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 1, 6]
def baseStart_2925759 : Nat := 118140960795 + 2925759 * 2 ^ 59
def prefixEnd_2925759 : Nat := 4983230072969 + 3 ^ 40 * 2925759 * 2
def baseEnd_2925759 : Nat := 500773548739307896052395

theorem tailTrace_2925759 : CollatzResearch.WordTrace tailWord_2925759 prefixEnd_2925759 500773548739307896052395 := by
  unfold tailWord_2925759
  simp only [CollatzResearch.WordTrace]
  refine ⟨106711197407482297700764331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71140798271654865133842887 106711197407482297700764331)
  ·
    refine ⟨160066796111223446551146497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106711197407482297700764331 160066796111223446551146497)
    ·
      refine ⟨120050097083417584913359873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160066796111223446551146497 120050097083417584913359873)
      ·
        refine ⟨90037572812563188685019905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120050097083417584913359873 90037572812563188685019905)
        ·
          refine ⟨67528179609422391513764929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90037572812563188685019905 67528179609422391513764929)
          ·
            refine ⟨50646134707066793635323697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67528179609422391513764929 50646134707066793635323697)
            ·
              refine ⟨37984601030300095226492773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50646134707066793635323697 37984601030300095226492773)
              ·
                refine ⟨7122112693181267854967395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37984601030300095226492773 7122112693181267854967395)
                ·
                  refine ⟨10683169039771901782451093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7122112693181267854967395 10683169039771901782451093)
                  ·
                    refine ⟨500773548739307896052395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10683169039771901782451093 500773548739307896052395)
                    ·
                      rfl

theorem cell23_2925759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_2925759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925759 prefixEnd_2925759 := by exact prefixLift 2925759
  have htrace : WordTrace (prefixWord ++ tailWord_2925759) baseStart_2925759 baseEnd_2925759 := by
    simpa [prefixWord, tailWord_2925759, baseEnd_2925759] using wordTrace_append hprefix tailTrace_2925759
  have hstable : (prefixWord ++ tailWord_2925759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925759).length < 2 ^ (prefixWord ++ tailWord_2925759).sum := by decide
  have hdescent : baseEnd_2925759 < baseStart_2925759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925769 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 1, 8, 3]
def baseStart_2925769 : Nat := 118140960795 + 2925769 * 2 ^ 59
def prefixEnd_2925769 : Nat := 4983230072969 + 3 ^ 40 * 2925769 * 2
def baseEnd_2925769 : Nat := 1502325781024468649032139

theorem tailTrace_2925769 : CollatzResearch.WordTrace tailWord_2925769 prefixEnd_2925769 1502325781024468649032139 := by
  unfold tailWord_2925769
  simp only [CollatzResearch.WordTrace]
  refine ⟨106711562137446069408628361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71141041424964046272418907 106711562137446069408628361)
  ·
    refine ⟨80033671603084552056471271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106711562137446069408628361 80033671603084552056471271)
    ·
      refine ⟨120050507404626828084706907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80033671603084552056471271 120050507404626828084706907)
      ·
        refine ⟨180075761106940242127060361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120050507404626828084706907 180075761106940242127060361)
        ·
          refine ⟨135056820830205181595295271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180075761106940242127060361 135056820830205181595295271)
          ·
            refine ⟨202585231245307772392942907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135056820830205181595295271 202585231245307772392942907)
            ·
              refine ⟨303877846867961658589414361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202585231245307772392942907 303877846867961658589414361)
              ·
                refine ⟨227908385150971243942060771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303877846867961658589414361 227908385150971243942060771)
                ·
                  refine ⟨341862577726456865913091157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227908385150971243942060771 341862577726456865913091157)
                  ·
                    refine ⟨4006202082731916397419037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 341862577726456865913091157 4006202082731916397419037)
                    ·
                      refine ⟨1502325781024468649032139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4006202082731916397419037 1502325781024468649032139)
                      ·
                        rfl

theorem cell23_2925769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8, 3].length) (baseStart_2925769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925769 prefixEnd_2925769 := by exact prefixLift 2925769
  have htrace : WordTrace (prefixWord ++ tailWord_2925769) baseStart_2925769 baseEnd_2925769 := by
    simpa [prefixWord, tailWord_2925769, baseEnd_2925769] using wordTrace_append hprefix tailTrace_2925769
  have hstable : (prefixWord ++ tailWord_2925769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925769).length < 2 ^ (prefixWord ++ tailWord_2925769).sum := by decide
  have hdescent : baseEnd_2925769 < baseStart_2925769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925779 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 4]
def baseStart_2925779 : Nat := 118140960795 + 2925779 * 2 ^ 59
def prefixEnd_2925779 : Nat := 4983230072969 + 3 ^ 40 * 2925779 * 2
def baseEnd_2925779 : Nat := 1502330915831013609907093

theorem tailTrace_2925779 : CollatzResearch.WordTrace tailWord_2925779 prefixEnd_2925779 1502330915831013609907093 := by
  unfold tailWord_2925779
  simp only [CollatzResearch.WordTrace]
  refine ⟨106711926867409841116492391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71141284578273227410994927 106711926867409841116492391)
  ·
    refine ⟨160067890301114761674738587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106711926867409841116492391 160067890301114761674738587)
    ·
      refine ⟨240101835451672142512107881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160067890301114761674738587 240101835451672142512107881)
      ·
        refine ⟨180076376588754106884080911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240101835451672142512107881 180076376588754106884080911)
        ·
          refine ⟨270114564883131160326121367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180076376588754106884080911 270114564883131160326121367)
          ·
            refine ⟨405171847324696740489182051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270114564883131160326121367 405171847324696740489182051)
            ·
              refine ⟨607757770987045110733773077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405171847324696740489182051 607757770987045110733773077)
              ·
                refine ⟨28488645515017739565645613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 607757770987045110733773077 28488645515017739565645613)
                ·
                  refine ⟨10683242068131652337117105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28488645515017739565645613 10683242068131652337117105)
                  ·
                    refine ⟨8012431551098739252837829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10683242068131652337117105 8012431551098739252837829)
                    ·
                      refine ⟨1502330915831013609907093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8012431551098739252837829 1502330915831013609907093)
                      ·
                        rfl

theorem cell23_2925779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_2925779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925779 prefixEnd_2925779 := by exact prefixLift 2925779
  have htrace : WordTrace (prefixWord ++ tailWord_2925779) baseStart_2925779 baseEnd_2925779 := by
    simpa [prefixWord, tailWord_2925779, baseEnd_2925779] using wordTrace_append hprefix tailTrace_2925779
  have hstable : (prefixWord ++ tailWord_2925779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925779).length < 2 ^ (prefixWord ++ tailWord_2925779).sum := by decide
  have hdescent : baseEnd_2925779 < baseStart_2925779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925786 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3]
def baseStart_2925786 : Nat := 118140960795 + 2925786 * 2 ^ 59
def prefixEnd_2925786 : Nat := 4983230072969 + 3 ^ 40 * 2925786 * 2
def baseEnd_2925786 : Nat := 1502334510195595082519561

theorem tailTrace_2925786 : CollatzResearch.WordTrace tailWord_2925786 prefixEnd_2925786 1502334510195595082519561 := by
  unfold tailWord_2925786
  simp only [CollatzResearch.WordTrace]
  refine ⟨26678045544596120327999303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71141454785589654207998141 26678045544596120327999303)
  ·
    refine ⟨40017068316894180491998955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26678045544596120327999303 40017068316894180491998955)
    ·
      refine ⟨60025602475341270737998433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40017068316894180491998955 60025602475341270737998433)
      ·
        refine ⟨45019201856505953053498825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60025602475341270737998433 45019201856505953053498825)
        ·
          refine ⟨33764401392379464790124119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45019201856505953053498825 33764401392379464790124119)
          ·
            refine ⟨50646602088569197185186179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33764401392379464790124119 50646602088569197185186179)
            ·
              refine ⟨75969903132853795777779269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50646602088569197185186179 75969903132853795777779269)
              ·
                refine ⟨14244356837410086708333613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75969903132853795777779269 14244356837410086708333613)
                ·
                  refine ⟨5341633814028782515625105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14244356837410086708333613 5341633814028782515625105)
                  ·
                    refine ⟨4006225360521586886718829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5341633814028782515625105 4006225360521586886718829)
                    ·
                      refine ⟨1502334510195595082519561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4006225360521586886718829 1502334510195595082519561)
                      ·
                        rfl

theorem cell23_2925786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_2925786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925786 prefixEnd_2925786 := by exact prefixLift 2925786
  have htrace : WordTrace (prefixWord ++ tailWord_2925786) baseStart_2925786 baseEnd_2925786 := by
    simpa [prefixWord, tailWord_2925786, baseEnd_2925786] using wordTrace_append hprefix tailTrace_2925786
  have hstable : (prefixWord ++ tailWord_2925786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925786).length < 2 ^ (prefixWord ++ tailWord_2925786).sum := by decide
  have hdescent : baseEnd_2925786 < baseStart_2925786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925793 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 2, 4]
def baseStart_2925793 : Nat := 118140960795 + 2925793 * 2 ^ 59
def prefixEnd_2925793 : Nat := 4983230072969 + 3 ^ 40 * 2925793 * 2
def baseEnd_2925793 : Nat := 500779368186725518377343

theorem tailTrace_2925793 : CollatzResearch.WordTrace tailWord_2925793 prefixEnd_2925793 500779368186725518377343 := by
  unfold tailWord_2925793
  simp only [CollatzResearch.WordTrace]
  refine ⟨106712437489359121507502033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71141624992906081005001355 106712437489359121507502033)
  ·
    refine ⟨80034328117019341130626525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106712437489359121507502033 80034328117019341130626525)
    ·
      refine ⟨30012873043882252923984947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80034328117019341130626525 30012873043882252923984947)
      ·
        refine ⟨45019309565823379385977421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30012873043882252923984947 45019309565823379385977421)
        ·
          refine ⟨16882241087183767269741533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45019309565823379385977421 16882241087183767269741533)
          ·
            refine ⟨6330840407693912726153075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16882241087183767269741533 6330840407693912726153075)
            ·
              refine ⟨9496260611540869089229613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330840407693912726153075 9496260611540869089229613)
              ·
                refine ⟨3561097729327825908461105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9496260611540869089229613 3561097729327825908461105)
                ·
                  refine ⟨2670823296995869431345829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3561097729327825908461105 2670823296995869431345829)
                  ·
                    refine ⟨500779368186725518377343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2670823296995869431345829 500779368186725518377343)
                    ·
                      rfl

theorem cell23_2925793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_2925793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925793 prefixEnd_2925793 := by exact prefixLift 2925793
  have htrace : WordTrace (prefixWord ++ tailWord_2925793) baseStart_2925793 baseEnd_2925793 := by
    simpa [prefixWord, tailWord_2925793, baseEnd_2925793] using wordTrace_append hprefix tailTrace_2925793
  have hstable : (prefixWord ++ tailWord_2925793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925793).length < 2 ^ (prefixWord ++ tailWord_2925793).sum := by decide
  have hdescent : baseEnd_2925793 < baseStart_2925793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925803 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 1, 2, 3]
def baseStart_2925803 : Nat := 118140960795 + 2925803 * 2 ^ 59
def prefixEnd_2925803 : Nat := 4983230072969 + 3 ^ 40 * 2925803 * 2
def baseEnd_2925803 : Nat := 1502343239366721516006983

theorem tailTrace_2925803 : CollatzResearch.WordTrace tailWord_2925803 prefixEnd_2925803 1502343239366721516006983 := by
  unfold tailWord_2925803
  simp only [CollatzResearch.WordTrace]
  refine ⟨106712802219322893215366063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71141868146215262143577375 106712802219322893215366063)
  ·
    refine ⟨160069203328984339823049095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106712802219322893215366063 160069203328984339823049095)
    ·
      refine ⟨240103804993476509734573643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160069203328984339823049095 240103804993476509734573643)
      ·
        refine ⟨360155707490214764601860465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240103804993476509734573643 360155707490214764601860465)
        ·
          refine ⟨270116780617661073451395349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360155707490214764601860465 270116780617661073451395349)
          ·
            refine ⟨12661724091452862818034157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 270116780617661073451395349 12661724091452862818034157)
            ·
              refine ⟨4748146534294823556762809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12661724091452862818034157 4748146534294823556762809)
              ·
                refine ⟨3561109900721117667572107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4748146534294823556762809 3561109900721117667572107)
                ·
                  refine ⟨5341664851081676501358161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561109900721117667572107 5341664851081676501358161)
                  ·
                    refine ⟨4006248638311257376018621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5341664851081676501358161 4006248638311257376018621)
                    ·
                      refine ⟨1502343239366721516006983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4006248638311257376018621 1502343239366721516006983)
                      ·
                        rfl

theorem cell23_2925803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 2, 3].length) (baseStart_2925803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925803 prefixEnd_2925803 := by exact prefixLift 2925803
  have htrace : WordTrace (prefixWord ++ tailWord_2925803) baseStart_2925803 baseEnd_2925803 := by
    simpa [prefixWord, tailWord_2925803, baseEnd_2925803] using wordTrace_append hprefix tailTrace_2925803
  have hstable : (prefixWord ++ tailWord_2925803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925803).length < 2 ^ (prefixWord ++ tailWord_2925803).sum := by decide
  have hdescent : baseEnd_2925803 < baseStart_2925803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925820 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 1, 1, 5]
def baseStart_2925820 : Nat := 118140960795 + 2925820 * 2 ^ 59
def prefixEnd_2925820 : Nat := 4983230072969 + 3 ^ 40 * 2925820 * 2
def baseEnd_2925820 : Nat := 1502351968537847949494405

theorem tailTrace_2925820 : CollatzResearch.WordTrace tailWord_2925820 prefixEnd_2925820 1502351968537847949494405 := by
  unfold tailWord_2925820
  simp only [CollatzResearch.WordTrace]
  refine ⟨53356711130130652559367457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71142281506840870079156609 53356711130130652559367457)
  ·
    refine ⟨40017533347597989419525593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53356711130130652559367457 40017533347597989419525593)
    ·
      refine ⟨30013150010698492064644195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40017533347597989419525593 30013150010698492064644195)
      ·
        refine ⟨45019725016047738096966293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30013150010698492064644195 45019725016047738096966293)
        ·
          refine ⟨2110299610127237723295295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45019725016047738096966293 2110299610127237723295295)
          ·
            refine ⟨3165449415190856584942943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110299610127237723295295 3165449415190856584942943)
            ·
              refine ⟨4748174122786284877414415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3165449415190856584942943 4748174122786284877414415)
              ·
                refine ⟨7122261184179427316121623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4748174122786284877414415 7122261184179427316121623)
                ·
                  refine ⟨10683391776269140974182435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7122261184179427316121623 10683391776269140974182435)
                  ·
                    refine ⟨16025087664403711461273653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10683391776269140974182435 16025087664403711461273653)
                    ·
                      refine ⟨1502351968537847949494405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16025087664403711461273653 1502351968537847949494405)
                      ·
                        rfl

theorem cell23_2925820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_2925820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925820 prefixEnd_2925820 := by exact prefixLift 2925820
  have htrace : WordTrace (prefixWord ++ tailWord_2925820) baseStart_2925820 baseEnd_2925820 := by
    simpa [prefixWord, tailWord_2925820, baseEnd_2925820] using wordTrace_append hprefix tailTrace_2925820
  have hstable : (prefixWord ++ tailWord_2925820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925820).length < 2 ^ (prefixWord ++ tailWord_2925820).sum := by decide
  have hdescent : baseEnd_2925820 < baseStart_2925820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925850 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3]
def baseStart_2925850 : Nat := 118140960795 + 2925850 * 2 ^ 59
def prefixEnd_2925850 : Nat := 4983230072969 + 3 ^ 40 * 2925850 * 2
def baseEnd_2925850 : Nat := 1502367372957482832119267

theorem tailTrace_2925850 : CollatzResearch.WordTrace tailWord_2925850 prefixEnd_2925850 1502367372957482832119267 := by
  unfold tailWord_2925850
  simp only [CollatzResearch.WordTrace]
  refine ⟨26678629112538155060581751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71143010966768413494884669 26678629112538155060581751)
  ·
    refine ⟨40017943668807232590872627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26678629112538155060581751 40017943668807232590872627)
    ·
      refine ⟨60026915503210848886308941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40017943668807232590872627 60026915503210848886308941)
      ·
        refine ⟨22510093313704068332365853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60026915503210848886308941 22510093313704068332365853)
        ·
          refine ⟨8441284992639025624637195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22510093313704068332365853 8441284992639025624637195)
          ·
            refine ⟨12661927488958538436955793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8441284992639025624637195 12661927488958538436955793)
            ·
              refine ⟨9496445616718903827716845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12661927488958538436955793 9496445616718903827716845)
              ·
                refine ⟨3561167106269588935393817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9496445616718903827716845 3561167106269588935393817)
                ·
                  refine ⟨2670875329702191701545363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3561167106269588935393817 2670875329702191701545363)
                  ·
                    refine ⟨4006312994553287552318045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2670875329702191701545363 4006312994553287552318045)
                    ·
                      refine ⟨1502367372957482832119267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4006312994553287552318045 1502367372957482832119267)
                      ·
                        rfl

theorem cell23_2925850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_2925850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925850 prefixEnd_2925850 := by exact prefixLift 2925850
  have htrace : WordTrace (prefixWord ++ tailWord_2925850) baseStart_2925850 baseEnd_2925850 := by
    simpa [prefixWord, tailWord_2925850, baseEnd_2925850] using wordTrace_append hprefix tailTrace_2925850
  have hstable : (prefixWord ++ tailWord_2925850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925850).length < 2 ^ (prefixWord ++ tailWord_2925850).sum := by decide
  have hdescent : baseEnd_2925850 < baseStart_2925850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925860 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 1, 3, 2]
def baseStart_2925860 : Nat := 118140960795 + 2925860 * 2 ^ 59
def prefixEnd_2925860 : Nat := 4983230072969 + 3 ^ 40 * 2925860 * 2
def baseEnd_2925860 : Nat := 1502372507764027792994221

theorem tailTrace_2925860 : CollatzResearch.WordTrace tailWord_2925860 prefixEnd_2925860 1502372507764027792994221 := by
  unfold tailWord_2925860
  simp only [CollatzResearch.WordTrace]
  refine ⟨53357440590058195975095517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71143254120077594633460689 53357440590058195975095517)
  ·
    refine ⟨20009040221271823490660819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53357440590058195975095517 20009040221271823490660819)
    ·
      refine ⟨30013560331907735235991229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20009040221271823490660819 30013560331907735235991229)
      ·
        refine ⟨11255085124465400713496711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30013560331907735235991229 11255085124465400713496711)
        ·
          refine ⟨16882627686698101070245067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11255085124465400713496711 16882627686698101070245067)
          ·
            refine ⟨25323941530047151605367601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16882627686698101070245067 25323941530047151605367601)
            ·
              refine ⟨18992956147535363704025701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25323941530047151605367601 18992956147535363704025701)
              ·
                refine ⟨3561179277662880694504819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18992956147535363704025701 3561179277662880694504819)
                ·
                  refine ⟨5341768916494321041757229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561179277662880694504819 5341768916494321041757229)
                  ·
                    refine ⟨2003163343685370390658961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5341768916494321041757229 2003163343685370390658961)
                    ·
                      refine ⟨1502372507764027792994221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003163343685370390658961 1502372507764027792994221)
                      ·
                        rfl

theorem cell23_2925860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_2925860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925860 prefixEnd_2925860 := by exact prefixLift 2925860
  have htrace : WordTrace (prefixWord ++ tailWord_2925860) baseStart_2925860 baseEnd_2925860 := by
    simpa [prefixWord, tailWord_2925860, baseEnd_2925860] using wordTrace_append hprefix tailTrace_2925860
  have hstable : (prefixWord ++ tailWord_2925860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925860).length < 2 ^ (prefixWord ++ tailWord_2925860).sum := by decide
  have hdescent : baseEnd_2925860 < baseStart_2925860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925877 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_2925877 : Nat := 118140960795 + 2925877 * 2 ^ 59
def prefixEnd_2925877 : Nat := 4983230072969 + 3 ^ 40 * 2925877 * 2
def baseEnd_2925877 : Nat := 1502381236935154226481643

theorem tailTrace_2925877 : CollatzResearch.WordTrace tailWord_2925877 prefixEnd_2925877 1502381236935154226481643 := by
  unfold tailWord_2925877
  simp only [CollatzResearch.WordTrace]
  refine ⟨106715501221054803853559885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71143667480703202569039923 106715501221054803853559885)
  ·
    refine ⟨40018312957895551445084957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106715501221054803853559885 40018312957895551445084957)
    ·
      refine ⟨15006867359210831791906859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40018312957895551445084957 15006867359210831791906859)
      ·
        refine ⟨22510301038816247687860289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15006867359210831791906859 22510301038816247687860289)
        ·
          refine ⟨16882725779112185765895217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22510301038816247687860289 16882725779112185765895217)
          ·
            refine ⟨12662044334334139324421413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16882725779112185765895217 12662044334334139324421413)
            ·
              refine ⟨2374133312687651123329015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12662044334334139324421413 2374133312687651123329015)
              ·
                refine ⟨3561199969031476684993523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374133312687651123329015 3561199969031476684993523)
                ·
                  refine ⟨5341799953547215027490285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561199969031476684993523 5341799953547215027490285)
                  ·
                    refine ⟨2003174982580205635308857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5341799953547215027490285 2003174982580205635308857)
                    ·
                      refine ⟨1502381236935154226481643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003174982580205635308857 1502381236935154226481643)
                      ·
                        rfl

theorem cell23_2925877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_2925877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925877 prefixEnd_2925877 := by exact prefixLift 2925877
  have htrace : WordTrace (prefixWord ++ tailWord_2925877) baseStart_2925877 baseEnd_2925877 := by
    simpa [prefixWord, tailWord_2925877, baseEnd_2925877] using wordTrace_append hprefix tailTrace_2925877
  have hstable : (prefixWord ++ tailWord_2925877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925877).length < 2 ^ (prefixWord ++ tailWord_2925877).sum := by decide
  have hdescent : baseEnd_2925877 < baseStart_2925877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925901 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_2925901 : Nat := 118140960795 + 2925901 * 2 ^ 59
def prefixEnd_2925901 : Nat := 4983230072969 + 3 ^ 40 * 2925901 * 2
def baseEnd_2925901 : Nat := 1502393560470862132581533

theorem tailTrace_2925901 : CollatzResearch.WordTrace tailWord_2925901 prefixEnd_2925901 1502393560470862132581533 := by
  unfold tailWord_2925901
  simp only [CollatzResearch.WordTrace]
  refine ⟨106716376572967855952433557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71144251048645237301622371 106716376572967855952433557)
  ·
    refine ⟨5002330151857868247770323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106716376572967855952433557 5002330151857868247770323)
    ·
      refine ⟨7503495227786802371655485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5002330151857868247770323 7503495227786802371655485)
      ·
        refine ⟨2813810710420050889370807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7503495227786802371655485 2813810710420050889370807)
        ·
          refine ⟨4220716065630076334056211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2813810710420050889370807 4220716065630076334056211)
          ·
            refine ⟨6331074098445114501084317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220716065630076334056211 6331074098445114501084317)
            ·
              refine ⟨2374152786916917937906619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6331074098445114501084317 2374152786916917937906619)
              ·
                refine ⟨3561229180375376906859929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374152786916917937906619 3561229180375376906859929)
                ·
                  refine ⟨2670921885281532680144947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3561229180375376906859929 2670921885281532680144947)
                  ·
                    refine ⟨4006382827922299020217421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2670921885281532680144947 4006382827922299020217421)
                    ·
                      refine ⟨1502393560470862132581533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4006382827922299020217421 1502393560470862132581533)
                      ·
                        rfl

theorem cell23_2925901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_2925901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925901 prefixEnd_2925901 := by exact prefixLift 2925901
  have htrace : WordTrace (prefixWord ++ tailWord_2925901) baseStart_2925901 baseEnd_2925901 := by
    simpa [prefixWord, tailWord_2925901, baseEnd_2925901] using wordTrace_append hprefix tailTrace_2925901
  have hstable : (prefixWord ++ tailWord_2925901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925901).length < 2 ^ (prefixWord ++ tailWord_2925901).sum := by decide
  have hdescent : baseEnd_2925901 < baseStart_2925901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925907 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 2, 2, 2]
def baseStart_2925907 : Nat := 118140960795 + 2925907 * 2 ^ 59
def prefixEnd_2925907 : Nat := 4983230072969 + 3 ^ 40 * 2925907 * 2
def baseEnd_2925907 : Nat := 1502396641354789109106505

theorem tailTrace_2925907 : CollatzResearch.WordTrace tailWord_2925907 prefixEnd_2925907 1502396641354789109106505 := by
  unfold tailWord_2925907
  simp only [CollatzResearch.WordTrace]
  refine ⟨106716595410946118977151975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71144396940630745984767983 106716595410946118977151975)
  ·
    refine ⟨160074893116419178465727963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106716595410946118977151975 160074893116419178465727963)
    ·
      refine ⟨240112339674628767698591945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160074893116419178465727963 240112339674628767698591945)
      ·
        refine ⟨180084254755971575773943959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240112339674628767698591945 180084254755971575773943959)
        ·
          refine ⟨270126382133957363660915939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180084254755971575773943959 270126382133957363660915939)
          ·
            refine ⟨405189573200936045491373909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270126382133957363660915939 405189573200936045491373909)
            ·
              refine ⟨2374157655474234641551019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 405189573200936045491373909 2374157655474234641551019)
              ·
                refine ⟨3561236483211351962326529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374157655474234641551019 3561236483211351962326529)
                ·
                  refine ⟨2670927362408513971744897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3561236483211351962326529 2670927362408513971744897)
                  ·
                    refine ⟨2003195521806385478808673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2670927362408513971744897 2003195521806385478808673)
                    ·
                      refine ⟨1502396641354789109106505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003195521806385478808673 1502396641354789109106505)
                      ·
                        rfl

theorem cell23_2925907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 2, 2, 2].length) (baseStart_2925907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925907 prefixEnd_2925907 := by exact prefixLift 2925907
  have htrace : WordTrace (prefixWord ++ tailWord_2925907) baseStart_2925907 baseEnd_2925907 := by
    simpa [prefixWord, tailWord_2925907, baseEnd_2925907] using wordTrace_append hprefix tailTrace_2925907
  have hstable : (prefixWord ++ tailWord_2925907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925907).length < 2 ^ (prefixWord ++ tailWord_2925907).sum := by decide
  have hdescent : baseEnd_2925907 < baseStart_2925907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925936 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 5]
def baseStart_2925936 : Nat := 118140960795 + 2925936 * 2 ^ 59
def prefixEnd_2925936 : Nat := 4983230072969 + 3 ^ 40 * 2925936 * 2
def baseEnd_2925936 : Nat := 1502411532293769495643871

theorem tailTrace_2925936 : CollatzResearch.WordTrace tailWord_2925936 prefixEnd_2925936 1502411532293769495643871 := by
  unfold tailWord_2925936
  simp only [CollatzResearch.WordTrace]
  refine ⟨53358826563920528464978831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71145102085227371286638441 53358826563920528464978831)
  ·
    refine ⟨80038239845880792697468247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53358826563920528464978831 80038239845880792697468247)
    ·
      refine ⟨120057359768821189046202371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80038239845880792697468247 120057359768821189046202371)
      ·
        refine ⟨180086039653231783569303557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120057359768821189046202371 180086039653231783569303557)
        ·
          refine ⟨33766132434980959419244417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180086039653231783569303557 33766132434980959419244417)
          ·
            refine ⟨25324599326235719564433313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33766132434980959419244417 25324599326235719564433313)
            ·
              refine ⟨18993449494676789673324985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25324599326235719564433313 18993449494676789673324985)
              ·
                refine ⟨14245087121007592254993739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18993449494676789673324985 14245087121007592254993739)
                ·
                  refine ⟨21367630681511388382490609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14245087121007592254993739 21367630681511388382490609)
                  ·
                    refine ⟨16025723011133541286867957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21367630681511388382490609 16025723011133541286867957)
                    ·
                      refine ⟨1502411532293769495643871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16025723011133541286867957 1502411532293769495643871)
                      ·
                        rfl

theorem cell23_2925936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_2925936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925936 prefixEnd_2925936 := by exact prefixLift 2925936
  have htrace : WordTrace (prefixWord ++ tailWord_2925936) baseStart_2925936 baseEnd_2925936 := by
    simpa [prefixWord, tailWord_2925936, baseEnd_2925936] using wordTrace_append hprefix tailTrace_2925936
  have hstable : (prefixWord ++ tailWord_2925936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925936).length < 2 ^ (prefixWord ++ tailWord_2925936).sum := by decide
  have hdescent : baseEnd_2925936 < baseStart_2925936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925963 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 1, 6, 2]
def baseStart_2925963 : Nat := 118140960795 + 2925963 * 2 ^ 59
def prefixEnd_2925963 : Nat := 4983230072969 + 3 ^ 40 * 2925963 * 2
def baseEnd_2925963 : Nat := 1502425396271440890006247

theorem tailTrace_2925963 : CollatzResearch.WordTrace tailWord_2925963 prefixEnd_2925963 1502425396271440890006247 := by
  unfold tailWord_2925963
  simp only [CollatzResearch.WordTrace]
  refine ⟨106718637898743240541190543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71145758599162160360793695 106718637898743240541190543)
  ·
    refine ⟨160077956848114860811785815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106718637898743240541190543 160077956848114860811785815)
    ·
      refine ⟨240116935272172291217678723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160077956848114860811785815 240116935272172291217678723)
      ·
        refine ⟨360175402908258436826518085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240116935272172291217678723 360175402908258436826518085)
        ·
          refine ⟨67532888045298456904972141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 360175402908258436826518085 67532888045298456904972141)
          ·
            refine ⟨25324833016986921339364553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67532888045298456904972141 25324833016986921339364553)
            ·
              refine ⟨18993624762740191004523415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25324833016986921339364553 18993624762740191004523415)
              ·
                refine ⟨28490437144110286506785123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18993624762740191004523415 28490437144110286506785123)
                ·
                  refine ⟨42735655716165429760177685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28490437144110286506785123 42735655716165429760177685)
                  ·
                    refine ⟨2003233861695254520008329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42735655716165429760177685 2003233861695254520008329)
                    ·
                      refine ⟨1502425396271440890006247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003233861695254520008329 1502425396271440890006247)
                      ·
                        rfl

theorem cell23_2925963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 6, 2].length) (baseStart_2925963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925963 prefixEnd_2925963 := by exact prefixLift 2925963
  have htrace : WordTrace (prefixWord ++ tailWord_2925963) baseStart_2925963 baseEnd_2925963 := by
    simpa [prefixWord, tailWord_2925963, baseEnd_2925963] using wordTrace_append hprefix tailTrace_2925963
  have hstable : (prefixWord ++ tailWord_2925963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925963).length < 2 ^ (prefixWord ++ tailWord_2925963).sum := by decide
  have hdescent : baseEnd_2925963 < baseStart_2925963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2925973 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 3, 4]
def baseStart_2925973 : Nat := 118140960795 + 2925973 * 2 ^ 59
def prefixEnd_2925973 : Nat := 4983230072969 + 3 ^ 40 * 2925973 * 2
def baseEnd_2925973 : Nat := 500810177025995283627067

theorem tailTrace_2925973 : CollatzResearch.WordTrace tailWord_2925973 prefixEnd_2925973 500810177025995283627067 := by
  unfold tailWord_2925973
  simp only [CollatzResearch.WordTrace]
  refine ⟨106719002628707012249054573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71146001752471341499369715 106719002628707012249054573)
  ·
    refine ⟨40019625985765129593395465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106719002628707012249054573 40019625985765129593395465)
    ·
      refine ⟨30014719489323847195046599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40019625985765129593395465 30014719489323847195046599)
      ·
        refine ⟨45022079233985770792569899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30014719489323847195046599 45022079233985770792569899)
        ·
          refine ⟨67533118850978656188854849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45022079233985770792569899 67533118850978656188854849)
          ·
            refine ⟨50649839138233992141641137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67533118850978656188854849 50649839138233992141641137)
            ·
              refine ⟨37987379353675494106230853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50649839138233992141641137 37987379353675494106230853)
              ·
                refine ⟨7122633628814155144918285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37987379353675494106230853 7122633628814155144918285)
                ·
                  refine ⟨2670987610805308179344357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7122633628814155144918285 2670987610805308179344357)
                  ·
                    refine ⟨500810177025995283627067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2670987610805308179344357 500810177025995283627067)
                    ·
                      rfl

theorem cell23_2925973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_2925973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2925973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2925973 prefixEnd_2925973 := by exact prefixLift 2925973
  have htrace : WordTrace (prefixWord ++ tailWord_2925973) baseStart_2925973 baseEnd_2925973 := by
    simpa [prefixWord, tailWord_2925973, baseEnd_2925973] using wordTrace_append hprefix tailTrace_2925973
  have hstable : (prefixWord ++ tailWord_2925973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2925973).length < 2 ^ (prefixWord ++ tailWord_2925973).sum := by decide
  have hdescent : baseEnd_2925973 < baseStart_2925973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2925973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926020 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 6]
def baseStart_2926020 : Nat := 118140960795 + 2926020 * 2 ^ 59
def prefixEnd_2926020 : Nat := 4983230072969 + 3 ^ 40 * 2926020 * 2
def baseEnd_2926020 : Nat := 166939407185416351888165

theorem tailTrace_2926020 : CollatzResearch.WordTrace tailWord_2926020 prefixEnd_2926020 166939407185416351888165 := by
  unfold tailWord_2926020
  simp only [CollatzResearch.WordTrace]
  refine ⟨53360358429768369638007757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71147144573024492850677009 53360358429768369638007757)
  ·
    refine ⟨20010134411163138614252909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53360358429768369638007757 20010134411163138614252909)
    ·
      refine ⟨7503800404186176980344841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20010134411163138614252909 7503800404186176980344841)
      ·
        refine ⟨5627850303139632735258631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7503800404186176980344841 5627850303139632735258631)
        ·
          refine ⟨8441775454709449102887947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5627850303139632735258631 8441775454709449102887947)
          ·
            refine ⟨12662663182064173654331921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8441775454709449102887947 12662663182064173654331921)
            ·
              refine ⟨9496997386548130240748941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12662663182064173654331921 9496997386548130240748941)
              ·
                refine ⟨3561374019955548840280853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9496997386548130240748941 3561374019955548840280853)
                ·
                  refine ⟨166939407185416351888165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3561374019955548840280853 166939407185416351888165)
                  ·
                    rfl

theorem cell23_2926020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_2926020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926020 prefixEnd_2926020 := by exact prefixLift 2926020
  have htrace : WordTrace (prefixWord ++ tailWord_2926020) baseStart_2926020 baseEnd_2926020 := by
    simpa [prefixWord, tailWord_2926020, baseEnd_2926020] using wordTrace_append hprefix tailTrace_2926020
  have hstable : (prefixWord ++ tailWord_2926020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926020).length < 2 ^ (prefixWord ++ tailWord_2926020).sum := by decide
  have hdescent : baseEnd_2926020 < baseStart_2926020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926030 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_2926030 : Nat := 118140960795 + 2926030 * 2 ^ 59
def prefixEnd_2926030 : Nat := 4983230072969 + 3 ^ 40 * 2926030 * 2
def baseEnd_2926030 : Nat := 1502459799475292127868439

theorem tailTrace_2926030 : CollatzResearch.WordTrace tailWord_2926030 prefixEnd_2926030 1502459799475292127868439 := by
  unfold tailWord_2926030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13340135198687563872984943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71147387726333673989253029 13340135198687563872984943)
  ·
    refine ⟨20010202798031345809477415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13340135198687563872984943 20010202798031345809477415)
    ·
      refine ⟨30015304197047018714216123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20010202798031345809477415 30015304197047018714216123)
      ·
        refine ⟨45022956295570528071324185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30015304197047018714216123 45022956295570528071324185)
        ·
          refine ⟨33767217221677896053493139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45022956295570528071324185 33767217221677896053493139)
          ·
            refine ⟨50650825832516844080239709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33767217221677896053493139 50650825832516844080239709)
            ·
              refine ⟨18994059687193816530089891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50650825832516844080239709 18994059687193816530089891)
              ·
                refine ⟨28491089530790724795134837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18994059687193816530089891 28491089530790724795134837)
                ·
                  refine ⟨2671039643511630449543891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28491089530790724795134837 2671039643511630449543891)
                  ·
                    refine ⟨4006559465267445674315837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2671039643511630449543891 4006559465267445674315837)
                    ·
                      refine ⟨1502459799475292127868439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4006559465267445674315837 1502459799475292127868439)
                      ·
                        rfl

theorem cell23_2926030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_2926030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926030 prefixEnd_2926030 := by exact prefixLift 2926030
  have htrace : WordTrace (prefixWord ++ tailWord_2926030) baseStart_2926030 baseEnd_2926030 := by
    simpa [prefixWord, tailWord_2926030, baseEnd_2926030] using wordTrace_append hprefix tailTrace_2926030
  have hstable : (prefixWord ++ tailWord_2926030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926030).length < 2 ^ (prefixWord ++ tailWord_2926030).sum := by decide
  have hdescent : baseEnd_2926030 < baseStart_2926030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926083 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 4]
def baseStart_2926083 : Nat := 118140960795 + 2926083 * 2 ^ 59
def prefixEnd_2926083 : Nat := 4983230072969 + 3 ^ 40 * 2926083 * 2
def baseEnd_2926083 : Nat := 1502487013949980420505695

theorem tailTrace_2926083 : CollatzResearch.WordTrace tailWord_2926083 prefixEnd_2926083 1502487013949980420505695 := by
  unfold tailWord_2926083
  simp only [CollatzResearch.WordTrace]
  refine ⟨106723014658308501035558903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71148676438872334023705935 106723014658308501035558903)
  ·
    refine ⟨160084521987462751553338355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106723014658308501035558903 160084521987462751553338355)
    ·
      refine ⟨240126782981194127330007533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160084521987462751553338355 240126782981194127330007533)
      ·
        refine ⟨90047543617947797748752825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240126782981194127330007533 90047543617947797748752825)
        ·
          refine ⟨67535657713460848311564619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90047543617947797748752825 67535657713460848311564619)
          ·
            refine ⟨101303486570191272467346929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67535657713460848311564619 101303486570191272467346929)
            ·
              refine ⟨75977614927643454350510197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101303486570191272467346929 75977614927643454350510197)
              ·
                refine ⟨7122901399466573845360331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75977614927643454350510197 7122901399466573845360331)
                ·
                  refine ⟨10684352099199860768040497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7122901399466573845360331 10684352099199860768040497)
                  ·
                    refine ⟨8013264074399895576030373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10684352099199860768040497 8013264074399895576030373)
                    ·
                      refine ⟨1502487013949980420505695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8013264074399895576030373 1502487013949980420505695)
                      ·
                        rfl

theorem cell23_2926083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_2926083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926083 prefixEnd_2926083 := by exact prefixLift 2926083
  have htrace : WordTrace (prefixWord ++ tailWord_2926083) baseStart_2926083 baseEnd_2926083 := by
    simpa [prefixWord, tailWord_2926083, baseEnd_2926083] using wordTrace_append hprefix tailTrace_2926083
  have hstable : (prefixWord ++ tailWord_2926083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926083).length < 2 ^ (prefixWord ++ tailWord_2926083).sum := by decide
  have hdescent : baseEnd_2926083 < baseStart_2926083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926087 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2926087 : Nat := 118140960795 + 2926087 * 2 ^ 59
def prefixEnd_2926087 : Nat := 4983230072969 + 3 ^ 40 * 2926087 * 2
def baseEnd_2926087 : Nat := 1502489067872598404855677

theorem tailTrace_2926087 : CollatzResearch.WordTrace tailWord_2926087 prefixEnd_2926087 1502489067872598404855677 := by
  unfold tailWord_2926087
  simp only [CollatzResearch.WordTrace]
  refine ⟨106723160550294009718704515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71148773700196006479136343 106723160550294009718704515)
  ·
    refine ⟨160084740825441014578056773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106723160550294009718704515 160084740825441014578056773)
    ·
      refine ⟨30015888904770190233385645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160084740825441014578056773 30015888904770190233385645)
      ·
        refine ⟨11255958339288821337519617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30015888904770190233385645 11255958339288821337519617)
        ·
          refine ⟨8441968754466616003139713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11255958339288821337519617 8441968754466616003139713)
          ·
            refine ⟨6331476565849962002354785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8441968754466616003139713 6331476565849962002354785)
            ·
              refine ⟨4748607424387471501766089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6331476565849962002354785 4748607424387471501766089)
              ·
                refine ⟨3561455568290603626324567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4748607424387471501766089 3561455568290603626324567)
                ·
                  refine ⟨5342183352435905439486851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561455568290603626324567 5342183352435905439486851)
                  ·
                    refine ⟨8013275028653858159230277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5342183352435905439486851 8013275028653858159230277)
                    ·
                      refine ⟨1502489067872598404855677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8013275028653858159230277 1502489067872598404855677)
                      ·
                        rfl

theorem cell23_2926087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2926087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926087 prefixEnd_2926087 := by exact prefixLift 2926087
  have htrace : WordTrace (prefixWord ++ tailWord_2926087) baseStart_2926087 baseEnd_2926087 := by
    simpa [prefixWord, tailWord_2926087, baseEnd_2926087] using wordTrace_append hprefix tailTrace_2926087
  have hstable : (prefixWord ++ tailWord_2926087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926087).length < 2 ^ (prefixWord ++ tailWord_2926087).sum := by decide
  have hdescent : baseEnd_2926087 < baseStart_2926087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926130 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2]
def baseStart_2926130 : Nat := 118140960795 + 2926130 * 2 ^ 59
def prefixEnd_2926130 : Nat := 4983230072969 + 3 ^ 40 * 2926130 * 2
def baseEnd_2926130 : Nat := 1502511147540741736617979

theorem tailTrace_2926130 : CollatzResearch.WordTrace tailWord_2926130 prefixEnd_2926130 1502511147540741736617979 := by
  unfold tailWord_2926130
  simp only [CollatzResearch.WordTrace]
  refine ⟨26681182222284557015629961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71149819259425485375013229 26681182222284557015629961)
  ·
    refine ⟨20010886666713417761722471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26681182222284557015629961 20010886666713417761722471)
    ·
      refine ⟨30016330000070126642583707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20010886666713417761722471 30016330000070126642583707)
      ·
        refine ⟨45024495000105189963875561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30016330000070126642583707 45024495000105189963875561)
        ·
          refine ⟨33768371250078892472906671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45024495000105189963875561 33768371250078892472906671)
          ·
            refine ⟨50652556875118338709360007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33768371250078892472906671 50652556875118338709360007)
            ·
              refine ⟨75978835312677508064040011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50652556875118338709360007 75978835312677508064040011)
              ·
                refine ⟨113968252969016262096060017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75978835312677508064040011 113968252969016262096060017)
                ·
                  refine ⟨85476189726762196572045013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113968252969016262096060017 85476189726762196572045013)
                  ·
                    refine ⟨2003348196720988982157305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 85476189726762196572045013 2003348196720988982157305)
                    ·
                      refine ⟨1502511147540741736617979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003348196720988982157305 1502511147540741736617979)
                      ·
                        rfl

theorem cell23_2926130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_2926130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926130 prefixEnd_2926130 := by exact prefixLift 2926130
  have htrace : WordTrace (prefixWord ++ tailWord_2926130) baseStart_2926130 baseEnd_2926130 := by
    simpa [prefixWord, tailWord_2926130, baseEnd_2926130] using wordTrace_append hprefix tailTrace_2926130
  have hstable : (prefixWord ++ tailWord_2926130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926130).length < 2 ^ (prefixWord ++ tailWord_2926130).sum := by decide
  have hdescent : baseEnd_2926130 < baseStart_2926130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926141 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 1, 2, 3]
def baseStart_2926141 : Nat := 118140960795 + 2926141 * 2 ^ 59
def prefixEnd_2926141 : Nat := 4983230072969 + 3 ^ 40 * 2926141 * 2
def baseEnd_2926141 : Nat := 1502516795827941193580429

theorem tailTrace_2926141 : CollatzResearch.WordTrace tailWord_2926141 prefixEnd_2926141 1502516795827941193580429 := by
  unfold tailWord_2926141
  simp only [CollatzResearch.WordTrace]
  refine ⟨106725130092098376941170277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71150086728065584627446851 106725130092098376941170277)
  ·
    refine ⟨20010961892268445676469427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106725130092098376941170277 20010961892268445676469427)
    ·
      refine ⟨30016442838402668514704141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20010961892268445676469427 30016442838402668514704141)
      ·
        refine ⟨11256166064401000693014053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30016442838402668514704141 11256166064401000693014053)
        ·
          refine ⟨2110531137075187629940135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11256166064401000693014053 2110531137075187629940135)
          ·
            refine ⟨3165796705612781444910203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110531137075187629940135 3165796705612781444910203)
            ·
              refine ⟨4748695058419172167365305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3165796705612781444910203 4748695058419172167365305)
              ·
                refine ⟨3561521293814379125523979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4748695058419172167365305 3561521293814379125523979)
                ·
                  refine ⟨5342281940721568688285969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561521293814379125523979 5342281940721568688285969)
                  ·
                    refine ⟨4006711455541176516214477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5342281940721568688285969 4006711455541176516214477)
                    ·
                      refine ⟨1502516795827941193580429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4006711455541176516214477 1502516795827941193580429)
                      ·
                        rfl

theorem cell23_2926141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_2926141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926141 prefixEnd_2926141 := by exact prefixLift 2926141
  have htrace : WordTrace (prefixWord ++ tailWord_2926141) baseStart_2926141 baseEnd_2926141 := by
    simpa [prefixWord, tailWord_2926141, baseEnd_2926141] using wordTrace_append hprefix tailTrace_2926141
  have hstable : (prefixWord ++ tailWord_2926141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926141).length < 2 ^ (prefixWord ++ tailWord_2926141).sum := by decide
  have hdescent : baseEnd_2926141 < baseStart_2926141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926180 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_2926180 : Nat := 118140960795 + 2926180 * 2 ^ 59
def prefixEnd_2926180 : Nat := 4983230072969 + 3 ^ 40 * 2926180 * 2
def baseEnd_2926180 : Nat := 1502536821573466540992749

theorem tailTrace_2926180 : CollatzResearch.WordTrace tailWord_2926180 prefixEnd_2926180 1502536821573466540992749 := by
  unfold tailWord_2926180
  simp only [CollatzResearch.WordTrace]
  refine ⟨53363276269478543300919997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71151035025971391067893329 53363276269478543300919997)
  ·
    refine ⟨20011228601054453737844999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53363276269478543300919997 20011228601054453737844999)
    ·
      refine ⟨30016842901581680606767499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20011228601054453737844999 30016842901581680606767499)
      ·
        refine ⟨45025264352372520910151249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30016842901581680606767499 45025264352372520910151249)
        ·
          refine ⟨33768948264279390682613437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45025264352372520910151249 33768948264279390682613437)
          ·
            refine ⟨12663355599104771505980039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33768948264279390682613437 12663355599104771505980039)
            ·
              refine ⟨18995033398657157258970059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12663355599104771505980039 18995033398657157258970059)
              ·
                refine ⟨28492550097985735888455089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18995033398657157258970059 28492550097985735888455089)
                ·
                  refine ⟨21369412573489301916341317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28492550097985735888455089 21369412573489301916341317)
                  ·
                    refine ⟨4006764857529244109313997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21369412573489301916341317 4006764857529244109313997)
                    ·
                      refine ⟨1502536821573466540992749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4006764857529244109313997 1502536821573466540992749)
                      ·
                        rfl

theorem cell23_2926180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_2926180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926180 prefixEnd_2926180 := by exact prefixLift 2926180
  have htrace : WordTrace (prefixWord ++ tailWord_2926180) baseStart_2926180 baseEnd_2926180 := by
    simpa [prefixWord, tailWord_2926180, baseEnd_2926180] using wordTrace_append hprefix tailTrace_2926180
  have hstable : (prefixWord ++ tailWord_2926180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926180).length < 2 ^ (prefixWord ++ tailWord_2926180).sum := by decide
  have hdescent : baseEnd_2926180 < baseStart_2926180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926194 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 1, 4, 2]
def baseStart_2926194 : Nat := 118140960795 + 2926194 * 2 ^ 59
def prefixEnd_2926194 : Nat := 4983230072969 + 3 ^ 40 * 2926194 * 2
def baseEnd_2926194 : Nat := 1502544010302629486217685

theorem tailTrace_2926194 : CollatzResearch.WordTrace tailWord_2926194 prefixEnd_2926194 1502544010302629486217685 := by
  unfold tailWord_2926194
  simp only [CollatzResearch.WordTrace]
  refine ⟨26681765790226591748212409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71151375440604244661899757 26681765790226591748212409)
  ·
    refine ⟨20011324342669943811159307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26681765790226591748212409 20011324342669943811159307)
    ·
      refine ⟨30016986514004915716738961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20011324342669943811159307 30016986514004915716738961)
      ·
        refine ⟨22512739885503686787554221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30016986514004915716738961 22512739885503686787554221)
        ·
          refine ⟨8442277457063882545332833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22512739885503686787554221 8442277457063882545332833)
          ·
            refine ⟨6331708092797911908999625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8442277457063882545332833 6331708092797911908999625)
            ·
              refine ⟨4748781069598433931749719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6331708092797911908999625 4748781069598433931749719)
              ·
                refine ⟨7123171604397650897624579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4748781069598433931749719 7123171604397650897624579)
                ·
                  refine ⟨10684757406596476346436869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7123171604397650897624579 10684757406596476346436869)
                  ·
                    refine ⟨2003392013736839314956913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10684757406596476346436869 2003392013736839314956913)
                    ·
                      refine ⟨1502544010302629486217685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003392013736839314956913 1502544010302629486217685)
                      ·
                        rfl

theorem cell23_2926194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_2926194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926194 prefixEnd_2926194 := by exact prefixLift 2926194
  have htrace : WordTrace (prefixWord ++ tailWord_2926194) baseStart_2926194 baseEnd_2926194 := by
    simpa [prefixWord, tailWord_2926194, baseEnd_2926194] using wordTrace_append hprefix tailTrace_2926194
  have hstable : (prefixWord ++ tailWord_2926194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926194).length < 2 ^ (prefixWord ++ tailWord_2926194).sum := by decide
  have hdescent : baseEnd_2926194 < baseStart_2926194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926284 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2926284 : Nat := 118140960795 + 2926284 * 2 ^ 59
def prefixEnd_2926284 : Nat := 4983230072969 + 3 ^ 40 * 2926284 * 2
def baseEnd_2926284 : Nat := 1502590223561534134092271

theorem tailTrace_2926284 : CollatzResearch.WordTrace tailWord_2926284 prefixEnd_2926284 1502590223561534134092271 := by
  unfold tailWord_2926284
  simp only [CollatzResearch.WordTrace]
  refine ⟨53365172865290156181812953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71153563820386874909083937 53365172865290156181812953)
  ·
    refine ⟨40023879648967617136359715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53365172865290156181812953 40023879648967617136359715)
    ·
      refine ⟨60035819473451425704539573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40023879648967617136359715 60035819473451425704539573)
      ·
        refine ⟨5628358075636071159800585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60035819473451425704539573 5628358075636071159800585)
        ·
          refine ⟨4221268556727053369850439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5628358075636071159800585 4221268556727053369850439)
          ·
            refine ⟨6331902835090580054775659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221268556727053369850439 6331902835090580054775659)
            ·
              refine ⟨9497854252635870082163489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6331902835090580054775659 9497854252635870082163489)
              ·
                refine ⟨7123390689476902561622617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9497854252635870082163489 7123390689476902561622617)
                ·
                  refine ⟨5342543017107676921216963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7123390689476902561622617 5342543017107676921216963)
                  ·
                    refine ⟨8013814525661515381825445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5342543017107676921216963 8013814525661515381825445)
                    ·
                      refine ⟨1502590223561534134092271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8013814525661515381825445 1502590223561534134092271)
                      ·
                        rfl

theorem cell23_2926284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2926284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926284 prefixEnd_2926284 := by exact prefixLift 2926284
  have htrace : WordTrace (prefixWord ++ tailWord_2926284) baseStart_2926284 baseEnd_2926284 := by
    simpa [prefixWord, tailWord_2926284, baseEnd_2926284] using wordTrace_append hprefix tailTrace_2926284
  have hstable : (prefixWord ++ tailWord_2926284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926284).length < 2 ^ (prefixWord ++ tailWord_2926284).sum := by decide
  have hdescent : baseEnd_2926284 < baseStart_2926284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926327 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 1, 5, 2]
def baseStart_2926327 : Nat := 118140960795 + 2926327 * 2 ^ 59
def prefixEnd_2926327 : Nat := 4983230072969 + 3 ^ 40 * 2926327 * 2
def baseEnd_2926327 : Nat := 1502612303229677465854573

theorem tailTrace_2926327 : CollatzResearch.WordTrace tailWord_2926327 prefixEnd_2926327 1502612303229677465854573 := by
  unfold tailWord_2926327
  simp only [CollatzResearch.WordTrace]
  refine ⟨106731914069424530707441235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71154609379616353804960823 106731914069424530707441235)
  ·
    refine ⟨160097871104136796061161853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106731914069424530707441235 160097871104136796061161853)
    ·
      refine ⟨60036701664051298522935695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160097871104136796061161853 60036701664051298522935695)
      ·
        refine ⟨90055052496076947784403543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60036701664051298522935695 90055052496076947784403543)
        ·
          refine ⟨135082578744115421676605315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90055052496076947784403543 135082578744115421676605315)
          ·
            refine ⟨202623868116173132514907973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135082578744115421676605315 202623868116173132514907973)
            ·
              refine ⟨37991975271782462346545245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202623868116173132514907973 37991975271782462346545245)
              ·
                refine ⟨14246990726918423379954467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37991975271782462346545245 14246990726918423379954467)
                ·
                  refine ⟨21370486090377635069931701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14246990726918423379954467 21370486090377635069931701)
                  ·
                    refine ⟨2003483070972903287806097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21370486090377635069931701 2003483070972903287806097)
                    ·
                      refine ⟨1502612303229677465854573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003483070972903287806097 1502612303229677465854573)
                      ·
                        rfl

theorem cell23_2926327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 5, 2].length) (baseStart_2926327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926327 prefixEnd_2926327 := by exact prefixLift 2926327
  have htrace : WordTrace (prefixWord ++ tailWord_2926327) baseStart_2926327 baseEnd_2926327 := by
    simpa [prefixWord, tailWord_2926327, baseEnd_2926327] using wordTrace_append hprefix tailTrace_2926327
  have hstable : (prefixWord ++ tailWord_2926327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926327).length < 2 ^ (prefixWord ++ tailWord_2926327).sum := by decide
  have hdescent : baseEnd_2926327 < baseStart_2926327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926337 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 1, 5]
def baseStart_2926337 : Nat := 118140960795 + 2926337 * 2 ^ 59
def prefixEnd_2926337 : Nat := 4983230072969 + 3 ^ 40 * 2926337 * 2
def baseEnd_2926337 : Nat := 500872479345407475576509

theorem tailTrace_2926337 : CollatzResearch.WordTrace tailWord_2926337 prefixEnd_2926337 500872479345407475576509 := by
  unfold tailWord_2926337
  simp only [CollatzResearch.WordTrace]
  refine ⟨106732278799388302415305265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71154852532925534943536843 106732278799388302415305265)
  ·
    refine ⟨80049209099541226811478949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106732278799388302415305265 80049209099541226811478949)
    ·
      refine ⟨15009226706163980027152303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80049209099541226811478949 15009226706163980027152303)
      ·
        refine ⟨22513840059245970040728455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15009226706163980027152303 22513840059245970040728455)
        ·
          refine ⟨33770760088868955061092683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22513840059245970040728455 33770760088868955061092683)
          ·
            refine ⟨50656140133303432591639025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33770760088868955061092683 50656140133303432591639025)
            ·
              refine ⟨37992105099977574443729269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50656140133303432591639025 37992105099977574443729269)
              ·
                refine ⟨3561759853122897604099619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37992105099977574443729269 3561759853122897604099619)
                ·
                  refine ⟨5342639779684346406149429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561759853122897604099619 5342639779684346406149429)
                  ·
                    refine ⟨500872479345407475576509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5342639779684346406149429 500872479345407475576509)
                    ·
                      rfl

theorem cell23_2926337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_2926337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926337 prefixEnd_2926337 := by exact prefixLift 2926337
  have htrace : WordTrace (prefixWord ++ tailWord_2926337) baseStart_2926337 baseEnd_2926337 := by
    simpa [prefixWord, tailWord_2926337, baseEnd_2926337] using wordTrace_append hprefix tailTrace_2926337
  have hstable : (prefixWord ++ tailWord_2926337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926337).length < 2 ^ (prefixWord ++ tailWord_2926337).sum := by decide
  have hdescent : baseEnd_2926337 < baseStart_2926337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926344 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 2, 3, 2]
def baseStart_2926344 : Nat := 118140960795 + 2926344 * 2 ^ 59
def prefixEnd_2926344 : Nat := 4983230072969 + 3 ^ 40 * 2926344 * 2
def baseEnd_2926344 : Nat := 1502621032400803899341995

theorem tailTrace_2926344 : CollatzResearch.WordTrace tailWord_2926344 prefixEnd_2926344 1502621032400803899341995 := by
  unfold tailWord_2926344
  simp only [CollatzResearch.WordTrace]
  refine ⟨53366267055181471305405043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71155022740241961740540057 53366267055181471305405043)
  ·
    refine ⟨80049400582772206958107565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53366267055181471305405043 80049400582772206958107565)
    ·
      refine ⟨30018525218539577609290337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80049400582772206958107565 30018525218539577609290337)
      ·
        refine ⟨22513893913904683206967753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30018525218539577609290337 22513893913904683206967753)
        ·
          refine ⟨16885420435428512405225815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22513893913904683206967753 16885420435428512405225815)
          ·
            refine ⟨25328130653142768607838723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16885420435428512405225815 25328130653142768607838723)
            ·
              refine ⟨37992195979714152911758085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25328130653142768607838723 37992195979714152911758085)
              ·
                refine ⟨7123536746196403670954641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37992195979714152911758085 7123536746196403670954641)
                ·
                  refine ⟨5342652559647302753215981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7123536746196403670954641 5342652559647302753215981)
                  ·
                    refine ⟨2003494709867738532455993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5342652559647302753215981 2003494709867738532455993)
                    ·
                      refine ⟨1502621032400803899341995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003494709867738532455993 1502621032400803899341995)
                      ·
                        rfl

theorem cell23_2926344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_2926344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926344 prefixEnd_2926344 := by exact prefixLift 2926344
  have htrace : WordTrace (prefixWord ++ tailWord_2926344) baseStart_2926344 baseEnd_2926344 := by
    simpa [prefixWord, tailWord_2926344, baseEnd_2926344] using wordTrace_append hprefix tailTrace_2926344
  have hstable : (prefixWord ++ tailWord_2926344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926344).length < 2 ^ (prefixWord ++ tailWord_2926344).sum := by decide
  have hdescent : baseEnd_2926344 < baseStart_2926344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926354 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2926354 : Nat := 118140960795 + 2926354 * 2 ^ 59
def prefixEnd_2926354 : Nat := 4983230072969 + 3 ^ 40 * 2926354 * 2
def baseEnd_2926354 : Nat := 500875389069116286738983

theorem tailTrace_2926354 : CollatzResearch.WordTrace tailWord_2926354 prefixEnd_2926354 500875389069116286738983 := by
  unfold tailWord_2926354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26683224710081678579668529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71155265893551142879116077 26683224710081678579668529)
  ·
    refine ⟨20012418532561258934751397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26683224710081678579668529 20012418532561258934751397)
    ·
      refine ⟨3752328474855236050265887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20012418532561258934751397 3752328474855236050265887)
      ·
        refine ⟨5628492712282854075398831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3752328474855236050265887 5628492712282854075398831)
        ·
          refine ⟨8442739068424281113098247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5628492712282854075398831 8442739068424281113098247)
          ·
            refine ⟨12664108602636421669647371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8442739068424281113098247 12664108602636421669647371)
            ·
              refine ⟨18996162903954632504471057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12664108602636421669647371 18996162903954632504471057)
              ·
                refine ⟨14247122177965974378353293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18996162903954632504471057 14247122177965974378353293)
                ·
                  refine ⟨5342670816737240391882485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14247122177965974378353293 5342670816737240391882485)
                  ·
                    refine ⟨500875389069116286738983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5342670816737240391882485 500875389069116286738983)
                    ·
                      rfl

theorem cell23_2926354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2926354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926354 prefixEnd_2926354 := by exact prefixLift 2926354
  have htrace : WordTrace (prefixWord ++ tailWord_2926354) baseStart_2926354 baseEnd_2926354 := by
    simpa [prefixWord, tailWord_2926354, baseEnd_2926354] using wordTrace_append hprefix tailTrace_2926354
  have hstable : (prefixWord ++ tailWord_2926354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926354).length < 2 ^ (prefixWord ++ tailWord_2926354).sum := by decide
  have hdescent : baseEnd_2926354 < baseStart_2926354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926357 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_2926357 : Nat := 118140960795 + 2926357 * 2 ^ 59
def prefixEnd_2926357 : Nat := 4983230072969 + 3 ^ 40 * 2926357 * 2
def baseEnd_2926357 : Nat := 1502627707649312348479435

theorem tailTrace_2926357 : CollatzResearch.WordTrace tailWord_2926357 prefixEnd_2926357 1502627707649312348479435 := by
  unfold tailWord_2926357
  simp only [CollatzResearch.WordTrace]
  refine ⟨106733008259315845831033325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71155338839543897220688883 106733008259315845831033325)
  ·
    refine ⟨40024878097243442186637497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106733008259315845831033325 40024878097243442186637497)
    ·
      refine ⟨30018658572932581639978123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40024878097243442186637497 30018658572932581639978123)
      ·
        refine ⟨45027987859398872459967185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30018658572932581639978123 45027987859398872459967185)
        ·
          refine ⟨33770990894549154344975389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45027987859398872459967185 33770990894549154344975389)
          ·
            refine ⟨12664121585455932879365771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33770990894549154344975389 12664121585455932879365771)
            ·
              refine ⟨18996182378183899319048657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12664121585455932879365771 18996182378183899319048657)
              ·
                refine ⟨14247136783637924489286493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18996182378183899319048657 14247136783637924489286493)
                ·
                  refine ⟨5342676293864221683482435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14247136783637924489286493 5342676293864221683482435)
                  ·
                    refine ⟨8014014440796332525223653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5342676293864221683482435 8014014440796332525223653)
                    ·
                      refine ⟨1502627707649312348479435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8014014440796332525223653 1502627707649312348479435)
                      ·
                        rfl

theorem cell23_2926357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_2926357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926357 prefixEnd_2926357 := by exact prefixLift 2926357
  have htrace : WordTrace (prefixWord ++ tailWord_2926357) baseStart_2926357 baseEnd_2926357 := by
    simpa [prefixWord, tailWord_2926357, baseEnd_2926357] using wordTrace_append hprefix tailTrace_2926357
  have hstable : (prefixWord ++ tailWord_2926357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926357).length < 2 ^ (prefixWord ++ tailWord_2926357).sum := by decide
  have hdescent : baseEnd_2926357 < baseStart_2926357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926367 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 1, 6]
def baseStart_2926367 : Nat := 118140960795 + 2926367 * 2 ^ 59
def prefixEnd_2926367 : Nat := 4983230072969 + 3 ^ 40 * 2926367 * 2
def baseEnd_2926367 : Nat := 500877614151952436451463

theorem tailTrace_2926367 : CollatzResearch.WordTrace tailWord_2926367 prefixEnd_2926367 500877614151952436451463 := by
  unfold tailWord_2926367
  simp only [CollatzResearch.WordTrace]
  refine ⟨106733372989279617538897355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71155581992853078359264903 106733372989279617538897355)
  ·
    refine ⟨160100059483919426308346033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106733372989279617538897355 160100059483919426308346033)
    ·
      refine ⟨120075044612939569731259525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160100059483919426308346033 120075044612939569731259525)
      ·
        refine ⟨22514070864926169324611161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120075044612939569731259525 22514070864926169324611161)
        ·
          refine ⟨16885553148694626993458371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22514070864926169324611161 16885553148694626993458371)
          ·
            refine ⟨25328329723041940490187557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16885553148694626993458371 25328329723041940490187557)
            ·
              refine ⟨4749061823070363841910167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25328329723041940490187557 4749061823070363841910167)
              ·
                refine ⟨7123592734605545762865251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4749061823070363841910167 7123592734605545762865251)
                ·
                  refine ⟨10685389101908318644297877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7123592734605545762865251 10685389101908318644297877)
                  ·
                    refine ⟨500877614151952436451463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10685389101908318644297877 500877614151952436451463)
                    ·
                      rfl

theorem cell23_2926367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 6].length) (baseStart_2926367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926367 prefixEnd_2926367 := by exact prefixLift 2926367
  have htrace : WordTrace (prefixWord ++ tailWord_2926367) baseStart_2926367 baseEnd_2926367 := by
    simpa [prefixWord, tailWord_2926367, baseEnd_2926367] using wordTrace_append hprefix tailTrace_2926367
  have hstable : (prefixWord ++ tailWord_2926367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926367).length < 2 ^ (prefixWord ++ tailWord_2926367).sum := by decide
  have hdescent : baseEnd_2926367 < baseStart_2926367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926388 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_2926388 : Nat := 118140960795 + 2926388 * 2 ^ 59
def prefixEnd_2926388 : Nat := 4983230072969 + 3 ^ 40 * 2926388 * 2
def baseEnd_2926388 : Nat := 500881208516533909063931

theorem tailTrace_2926388 : CollatzResearch.WordTrace tailWord_2926388 prefixEnd_2926388 500881208516533909063931 := by
  unfold tailWord_2926388
  simp only [CollatzResearch.WordTrace]
  refine ⟨53367069461101769062705909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71156092614802358750274545 53367069461101769062705909)
  ·
    refine ⟨5003162761978290849628679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53367069461101769062705909 5003162761978290849628679)
    ·
      refine ⟨7504744142967436274443019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5003162761978290849628679 7504744142967436274443019)
      ·
        refine ⟨11257116214451154411664529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7504744142967436274443019 11257116214451154411664529)
        ·
          refine ⟨8442837160838365808748397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11257116214451154411664529 8442837160838365808748397)
          ·
            refine ⟨3166063935314387178280649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8442837160838365808748397 3166063935314387178280649)
            ·
              refine ⟨2374547951485790383710487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3166063935314387178280649 2374547951485790383710487)
              ·
                refine ⟨3561821927228685575565731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374547951485790383710487 3561821927228685575565731)
                ·
                  refine ⟨5342732890843028363348597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561821927228685575565731 5342732890843028363348597)
                  ·
                    refine ⟨500881208516533909063931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5342732890843028363348597 500881208516533909063931)
                    ·
                      rfl

theorem cell23_2926388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_2926388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926388 prefixEnd_2926388 := by exact prefixLift 2926388
  have htrace : WordTrace (prefixWord ++ tailWord_2926388) baseStart_2926388 baseEnd_2926388 := by
    simpa [prefixWord, tailWord_2926388, baseEnd_2926388] using wordTrace_append hprefix tailTrace_2926388
  have hstable : (prefixWord ++ tailWord_2926388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926388).length < 2 ^ (prefixWord ++ tailWord_2926388).sum := by decide
  have hdescent : baseEnd_2926388 < baseStart_2926388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926397 : List Nat := [1, 4, 1, 4, 1, 2, 10]
def baseStart_2926397 : Nat := 118140960795 + 2926397 * 2 ^ 59
def prefixEnd_2926397 : Nat := 4983230072969 + 3 ^ 40 * 2926397 * 2
def baseEnd_2926397 : Nat := 18551212924388792493571

theorem tailTrace_2926397 : CollatzResearch.WordTrace tailWord_2926397 prefixEnd_2926397 18551212924388792493571 := by
  unfold tailWord_2926397
  simp only [CollatzResearch.WordTrace]
  refine ⟨106734467179170932662489445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71156311452780621774992963 106734467179170932662489445)
  ·
    refine ⟨20012712596094549874216771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106734467179170932662489445 20012712596094549874216771)
    ·
      refine ⟨30019068894141824811325157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20012712596094549874216771 30019068894141824811325157)
      ·
        refine ⟨5628575417651592152123467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30019068894141824811325157 5628575417651592152123467)
        ·
          refine ⟨8442863126477388228185201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5628575417651592152123467 8442863126477388228185201)
          ·
            refine ⟨6332147344858041171138901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8442863126477388228185201 6332147344858041171138901)
            ·
              refine ⟨18551212924388792493571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6332147344858041171138901 18551212924388792493571)
              ·
                rfl

theorem cell23_2926397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 10].length) (baseStart_2926397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926397 prefixEnd_2926397 := by exact prefixLift 2926397
  have htrace : WordTrace (prefixWord ++ tailWord_2926397) baseStart_2926397 baseEnd_2926397 := by
    simpa [prefixWord, tailWord_2926397, baseEnd_2926397] using wordTrace_append hprefix tailTrace_2926397
  have hstable : (prefixWord ++ tailWord_2926397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926397).length < 2 ^ (prefixWord ++ tailWord_2926397).sum := by decide
  have hdescent : baseEnd_2926397 < baseStart_2926397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926400 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_2926400 : Nat := 118140960795 + 2926400 * 2 ^ 59
def prefixEnd_2926400 : Nat := 4983230072969 + 3 ^ 40 * 2926400 * 2
def baseEnd_2926400 : Nat := 1502649787317455680241737

theorem tailTrace_2926400 : CollatzResearch.WordTrace tailWord_2926400 prefixEnd_2926400 1502649787317455680241737 := by
  unfold tailWord_2926400
  simp only [CollatzResearch.WordTrace]
  refine ⟨53367288299080032087424327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71156384398773376116565769 53367288299080032087424327)
  ·
    refine ⟨80050932448620048131136491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53367288299080032087424327 80050932448620048131136491)
    ·
      refine ⟨120076398672930072196704737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80050932448620048131136491 120076398672930072196704737)
      ·
        refine ⟨90057299004697554147528553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120076398672930072196704737 90057299004697554147528553)
        ·
          refine ⟨67542974253523165610646415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90057299004697554147528553 67542974253523165610646415)
          ·
            refine ⟨101314461380284748415969623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67542974253523165610646415 101314461380284748415969623)
            ·
              refine ⟨151971692070427122623954435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101314461380284748415969623 151971692070427122623954435)
              ·
                refine ⟨227957538105640683935931653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151971692070427122623954435 227957538105640683935931653)
                ·
                  refine ⟨42742038394807628237987185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227957538105640683935931653 42742038394807628237987185)
                  ·
                    refine ⟨32056528796105721178490389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42742038394807628237987185 32056528796105721178490389)
                    ·
                      refine ⟨1502649787317455680241737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32056528796105721178490389 1502649787317455680241737)
                      ·
                        rfl

theorem cell23_2926400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_2926400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926400 prefixEnd_2926400 := by exact prefixLift 2926400
  have htrace : WordTrace (prefixWord ++ tailWord_2926400) baseStart_2926400 baseEnd_2926400 := by
    simpa [prefixWord, tailWord_2926400, baseEnd_2926400] using wordTrace_append hprefix tailTrace_2926400
  have hstable : (prefixWord ++ tailWord_2926400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926400).length < 2 ^ (prefixWord ++ tailWord_2926400).sum := by decide
  have hdescent : baseEnd_2926400 < baseStart_2926400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926407 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_2926407 : Nat := 118140960795 + 2926407 * 2 ^ 59
def prefixEnd_2926407 : Nat := 4983230072969 + 3 ^ 40 * 2926407 * 2
def baseEnd_2926407 : Nat := 1502653381682037152854205

theorem tailTrace_2926407 : CollatzResearch.WordTrace tailWord_2926407 prefixEnd_2926407 1502653381682037152854205 := by
  unfold tailWord_2926407
  simp only [CollatzResearch.WordTrace]
  refine ⟨106734831909134704370353475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71156554606089802913568983 106734831909134704370353475)
  ·
    refine ⟨160102247863702056555530213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106734831909134704370353475 160102247863702056555530213)
    ·
      refine ⟨30019171474444135604161915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160102247863702056555530213 30019171474444135604161915)
      ·
        refine ⟨45028757211666203406242873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30019171474444135604161915 45028757211666203406242873)
        ·
          refine ⟨33771567908749652554682155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45028757211666203406242873 33771567908749652554682155)
          ·
            refine ⟨50657351863124478832023233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33771567908749652554682155 50657351863124478832023233)
            ·
              refine ⟨37993013897343359124017425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50657351863124478832023233 37993013897343359124017425)
              ·
                refine ⟨28494760423007519343013069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37993013897343359124017425 28494760423007519343013069)
                ·
                  refine ⟨10685535158627819753629901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28494760423007519343013069 10685535158627819753629901)
                  ·
                    refine ⟨4007075684485432407611213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10685535158627819753629901 4007075684485432407611213)
                    ·
                      refine ⟨1502653381682037152854205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4007075684485432407611213 1502653381682037152854205)
                      ·
                        rfl

theorem cell23_2926407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_2926407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926407 prefixEnd_2926407 := by exact prefixLift 2926407
  have htrace : WordTrace (prefixWord ++ tailWord_2926407) baseStart_2926407 baseEnd_2926407 := by
    simpa [prefixWord, tailWord_2926407, baseEnd_2926407] using wordTrace_append hprefix tailTrace_2926407
  have hstable : (prefixWord ++ tailWord_2926407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926407).length < 2 ^ (prefixWord ++ tailWord_2926407).sum := by decide
  have hdescent : baseEnd_2926407 < baseStart_2926407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926408 : List Nat := [2, 1, 3, 1, 1, 4, 2, 4, 1, 2, 2]
def baseStart_2926408 : Nat := 118140960795 + 2926408 * 2 ^ 59
def prefixEnd_2926408 : Nat := 4983230072969 + 3 ^ 40 * 2926408 * 2
def baseEnd_2926408 : Nat := 1502653895162691648941701

theorem tailTrace_2926408 : CollatzResearch.WordTrace tailWord_2926408 prefixEnd_2926408 1502653895162691648941701 := by
  unfold tailWord_2926408
  simp only [CollatzResearch.WordTrace]
  refine ⟨53367434191065540770569939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71156578921420721027426585 53367434191065540770569939)
  ·
    refine ⟨80051151286598311155854909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53367434191065540770569939 80051151286598311155854909)
    ·
      refine ⟨30019181732474366683445591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80051151286598311155854909 30019181732474366683445591)
      ·
        refine ⟨45028772598711550025168387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30019181732474366683445591 45028772598711550025168387)
        ·
          refine ⟨67543158898067325037752581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45028772598711550025168387 67543158898067325037752581)
          ·
            refine ⟨12664342293387623444578609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67543158898067325037752581 12664342293387623444578609)
            ·
              refine ⟨9498256720040717583433957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12664342293387623444578609 9498256720040717583433957)
              ·
                refine ⟨1780923135007634546893867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9498256720040717583433957 1780923135007634546893867)
                ·
                  refine ⟨2671384702511451820340801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780923135007634546893867 2671384702511451820340801)
                  ·
                    refine ⟨2003538526883588865255601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2671384702511451820340801 2003538526883588865255601)
                    ·
                      refine ⟨1502653895162691648941701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003538526883588865255601 1502653895162691648941701)
                      ·
                        rfl

theorem cell23_2926408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_2926408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926408 prefixEnd_2926408 := by exact prefixLift 2926408
  have htrace : WordTrace (prefixWord ++ tailWord_2926408) baseStart_2926408 baseEnd_2926408 := by
    simpa [prefixWord, tailWord_2926408, baseEnd_2926408] using wordTrace_append hprefix tailTrace_2926408
  have hstable : (prefixWord ++ tailWord_2926408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926408).length < 2 ^ (prefixWord ++ tailWord_2926408).sum := by decide
  have hdescent : baseEnd_2926408 < baseStart_2926408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926428 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2926428 : Nat := 118140960795 + 2926428 * 2 ^ 59
def prefixEnd_2926428 : Nat := 4983230072969 + 3 ^ 40 * 2926428 * 2
def baseEnd_2926428 : Nat := 1502664164775781570691609

theorem tailTrace_2926428 : CollatzResearch.WordTrace tailWord_2926428 prefixEnd_2926428 1502664164775781570691609 := by
  unfold tailWord_2926428
  simp only [CollatzResearch.WordTrace]
  refine ⟨53367798921029312478433969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71157065228039083304578625 53367798921029312478433969)
  ·
    refine ⟨40025849190771984358825477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53367798921029312478433969 40025849190771984358825477)
    ·
      refine ⟨7504846723269747067279777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40025849190771984358825477 7504846723269747067279777)
      ·
        refine ⟨5628635042452310300459833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7504846723269747067279777 5628635042452310300459833)
        ·
          refine ⟨4221476281839232725344875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5628635042452310300459833 4221476281839232725344875)
          ·
            refine ⟨6332214422758849088017313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221476281839232725344875 6332214422758849088017313)
            ·
              refine ⟨4749160817069136816012985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6332214422758849088017313 4749160817069136816012985)
              ·
                refine ⟨3561870612801852612009739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4749160817069136816012985 3561870612801852612009739)
                ·
                  refine ⟨5342805919202778918014609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561870612801852612009739 5342805919202778918014609)
                  ·
                    refine ⟨4007104439402084188510957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5342805919202778918014609 4007104439402084188510957)
                    ·
                      refine ⟨1502664164775781570691609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4007104439402084188510957 1502664164775781570691609)
                      ·
                        rfl

theorem cell23_2926428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2926428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926428 prefixEnd_2926428 := by exact prefixLift 2926428
  have htrace : WordTrace (prefixWord ++ tailWord_2926428) baseStart_2926428 baseEnd_2926428 := by
    simpa [prefixWord, tailWord_2926428, baseEnd_2926428] using wordTrace_append hprefix tailTrace_2926428
  have hstable : (prefixWord ++ tailWord_2926428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926428).length < 2 ^ (prefixWord ++ tailWord_2926428).sum := by decide
  have hdescent : baseEnd_2926428 < baseStart_2926428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926484 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2926484 : Nat := 118140960795 + 2926484 * 2 ^ 59
def prefixEnd_2926484 : Nat := 4983230072969 + 3 ^ 40 * 2926484 * 2
def baseEnd_2926484 : Nat := 1502692919692433351591351

theorem tailTrace_2926484 : CollatzResearch.WordTrace tailWord_2926484 prefixEnd_2926484 1502692919692433351591351 := by
  unfold tailWord_2926484
  simp only [CollatzResearch.WordTrace]
  refine ⟨53368820164927873260453253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71158426886570497680604337 53368820164927873260453253)
  ·
    refine ⟨10006653780923976236334985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53368820164927873260453253 10006653780923976236334985)
    ·
      refine ⟨7504990335692982177251239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10006653780923976236334985 7504990335692982177251239)
      ·
        refine ⟨11257485503539473265876859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7504990335692982177251239 11257485503539473265876859)
        ·
          refine ⟨16886228255309209898815289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11257485503539473265876859 16886228255309209898815289)
          ·
            refine ⟨12664671191481907424111467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16886228255309209898815289 12664671191481907424111467)
            ·
              refine ⟨18997006787222861136167201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12664671191481907424111467 18997006787222861136167201)
              ·
                refine ⟨14247755090417145852125401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18997006787222861136167201 14247755090417145852125401)
                ·
                  refine ⟨10685816317812859389094051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14247755090417145852125401 10685816317812859389094051)
                  ·
                    refine ⟨16028724476719289083641077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10685816317812859389094051 16028724476719289083641077)
                    ·
                      refine ⟨1502692919692433351591351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16028724476719289083641077 1502692919692433351591351)
                      ·
                        rfl

theorem cell23_2926484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2926484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926484 prefixEnd_2926484 := by exact prefixLift 2926484
  have htrace : WordTrace (prefixWord ++ tailWord_2926484) baseStart_2926484 baseEnd_2926484 := by
    simpa [prefixWord, tailWord_2926484, baseEnd_2926484] using wordTrace_append hprefix tailTrace_2926484
  have hstable : (prefixWord ++ tailWord_2926484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926484).length < 2 ^ (prefixWord ++ tailWord_2926484).sum := by decide
  have hdescent : baseEnd_2926484 < baseStart_2926484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926498 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_2926498 : Nat := 118140960795 + 2926498 * 2 ^ 59
def prefixEnd_2926498 : Nat := 4983230072969 + 3 ^ 40 * 2926498 * 2
def baseEnd_2926498 : Nat := 1502700108421596296816287

theorem tailTrace_2926498 : CollatzResearch.WordTrace tailWord_2926498 prefixEnd_2926498 1502700108421596296816287 := by
  unfold tailWord_2926498
  simp only [CollatzResearch.WordTrace]
  refine ⟨26684537737951256727979037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71158767301203351274610765 26684537737951256727979037)
  ·
    refine ⟨10006701651731721272992139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26684537737951256727979037 10006701651731721272992139)
    ·
      refine ⟨15010052477597581909488209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10006701651731721272992139 15010052477597581909488209)
      ·
        refine ⟨11257539358198186432116157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15010052477597581909488209 11257539358198186432116157)
        ·
          refine ⟨4221577259324319912043559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11257539358198186432116157 4221577259324319912043559)
          ·
            refine ⟨6332365888986479868065339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221577259324319912043559 6332365888986479868065339)
            ·
              refine ⟨9498548833479719802098009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6332365888986479868065339 9498548833479719802098009)
              ·
                refine ⟨7123911625109789851573507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9498548833479719802098009 7123911625109789851573507)
                ·
                  refine ⟨10685867437664684777360261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7123911625109789851573507 10685867437664684777360261)
                  ·
                    refine ⟨2003600144562128395755049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10685867437664684777360261 2003600144562128395755049)
                    ·
                      refine ⟨1502700108421596296816287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003600144562128395755049 1502700108421596296816287)
                      ·
                        rfl

theorem cell23_2926498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_2926498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926498 prefixEnd_2926498 := by exact prefixLift 2926498
  have htrace : WordTrace (prefixWord ++ tailWord_2926498) baseStart_2926498 baseEnd_2926498 := by
    simpa [prefixWord, tailWord_2926498, baseEnd_2926498] using wordTrace_append hprefix tailTrace_2926498
  have hstable : (prefixWord ++ tailWord_2926498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926498).length < 2 ^ (prefixWord ++ tailWord_2926498).sum := by decide
  have hdescent : baseEnd_2926498 < baseStart_2926498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926527 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 5]
def baseStart_2926527 : Nat := 118140960795 + 2926527 * 2 ^ 59
def prefixEnd_2926527 : Nat := 4983230072969 + 3 ^ 40 * 2926527 * 2
def baseEnd_2926527 : Nat := 1502714999360576683353653

theorem tailTrace_2926527 : CollatzResearch.WordTrace tailWord_2926527 prefixEnd_2926527 1502714999360576683353653 := by
  unfold tailWord_2926527
  simp only [CollatzResearch.WordTrace]
  refine ⟨106739208668699964864721835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71159472445799976576481223 106739208668699964864721835)
  ·
    refine ⟨160108813003049947297082753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106739208668699964864721835 160108813003049947297082753)
    ·
      refine ⟨120081609752287460472812065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160108813003049947297082753 120081609752287460472812065)
      ·
        refine ⟨90061207314215595354609049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120081609752287460472812065 90061207314215595354609049)
        ·
          refine ⟨67545905485661696515956787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90061207314215595354609049 67545905485661696515956787)
          ·
            refine ⟨101318858228492544773935181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67545905485661696515956787 101318858228492544773935181)
            ·
              refine ⟨37994571835684704290225693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101318858228492544773935181 37994571835684704290225693)
              ·
                refine ⟨14247964438381764108834635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37994571835684704290225693 14247964438381764108834635)
                ·
                  refine ⟨21371946657572646163251953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14247964438381764108834635 21371946657572646163251953)
                  ·
                    refine ⟨16028959993179484622438965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21371946657572646163251953 16028959993179484622438965)
                    ·
                      refine ⟨1502714999360576683353653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16028959993179484622438965 1502714999360576683353653)
                      ·
                        rfl

theorem cell23_2926527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_2926527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926527 prefixEnd_2926527 := by exact prefixLift 2926527
  have htrace : WordTrace (prefixWord ++ tailWord_2926527) baseStart_2926527 baseEnd_2926527 := by
    simpa [prefixWord, tailWord_2926527, baseEnd_2926527] using wordTrace_append hprefix tailTrace_2926527
  have hstable : (prefixWord ++ tailWord_2926527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926527).length < 2 ^ (prefixWord ++ tailWord_2926527).sum := by decide
  have hdescent : baseEnd_2926527 < baseStart_2926527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926537 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 4]
def baseStart_2926537 : Nat := 118140960795 + 2926537 * 2 ^ 59
def prefixEnd_2926537 : Nat := 4983230072969 + 3 ^ 40 * 2926537 * 2
def baseEnd_2926537 : Nat := 1502720134167121644228607

theorem tailTrace_2926537 : CollatzResearch.WordTrace tailWord_2926537 prefixEnd_2926537 1502720134167121644228607 := by
  unfold tailWord_2926537
  simp only [CollatzResearch.WordTrace]
  refine ⟨106739573398663736572585865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71159715599109157715057243 106739573398663736572585865)
  ·
    refine ⟨80054680048997802429439399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106739573398663736572585865 80054680048997802429439399)
    ·
      refine ⟨120082020073496703644159099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80054680048997802429439399 120082020073496703644159099)
      ·
        refine ⟨180123030110245055466238649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120082020073496703644159099 180123030110245055466238649)
        ·
          refine ⟨135092272582683791599678987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180123030110245055466238649 135092272582683791599678987)
          ·
            refine ⟨202638408874025687399518481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135092272582683791599678987 202638408874025687399518481)
            ·
              refine ⟨151978806655519265549638861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202638408874025687399518481 151978806655519265549638861)
              ·
                refine ⟨56992052495819724581114573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151978806655519265549638861 56992052495819724581114573)
                ·
                  refine ⟨21372019685932396717917965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56992052495819724581114573 21372019685932396717917965)
                  ·
                    refine ⟨8014507382224648769219237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21372019685932396717917965 8014507382224648769219237)
                    ·
                      refine ⟨1502720134167121644228607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8014507382224648769219237 1502720134167121644228607)
                      ·
                        rfl

theorem cell23_2926537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_2926537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926537 prefixEnd_2926537 := by exact prefixLift 2926537
  have htrace : WordTrace (prefixWord ++ tailWord_2926537) baseStart_2926537 baseEnd_2926537 := by
    simpa [prefixWord, tailWord_2926537, baseEnd_2926537] using wordTrace_append hprefix tailTrace_2926537
  have hstable : (prefixWord ++ tailWord_2926537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926537).length < 2 ^ (prefixWord ++ tailWord_2926537).sum := by decide
  have hdescent : baseEnd_2926537 < baseStart_2926537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926564 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_2926564 : Nat := 118140960795 + 2926564 * 2 ^ 59
def prefixEnd_2926564 : Nat := 4983230072969 + 3 ^ 40 * 2926564 * 2
def baseEnd_2926564 : Nat := 500911332714931012863661

theorem tailTrace_2926564 : CollatzResearch.WordTrace tailWord_2926564 prefixEnd_2926564 500911332714931012863661 := by
  unfold tailWord_2926564
  simp only [CollatzResearch.WordTrace]
  refine ⟨53370279084782960091909373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71160372113043946789212497 53370279084782960091909373)
  ·
    refine ⟨20013854656793610034466015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53370279084782960091909373 20013854656793610034466015)
    ·
      refine ⟨30020781985190415051699023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20013854656793610034466015 30020781985190415051699023)
      ·
        refine ⟨45031172977785622577548535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30020781985190415051699023 45031172977785622577548535)
        ·
          refine ⟨67546759466678433866322803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45031172977785622577548535 67546759466678433866322803)
          ·
            refine ⟨101320139200017650799484205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67546759466678433866322803 101320139200017650799484205)
            ·
              refine ⟨37995052200006619049806577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101320139200017650799484205 37995052200006619049806577)
              ·
                refine ⟨28496289150004964287354933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37995052200006619049806577 28496289150004964287354933)
                ·
                  refine ⟨2671527107812965401939525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28496289150004964287354933 2671527107812965401939525)
                  ·
                    refine ⟨500911332714931012863661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2671527107812965401939525 500911332714931012863661)
                    ·
                      rfl

theorem cell23_2926564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_2926564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926564 prefixEnd_2926564 := by exact prefixLift 2926564
  have htrace : WordTrace (prefixWord ++ tailWord_2926564) baseStart_2926564 baseEnd_2926564 := by
    simpa [prefixWord, tailWord_2926564, baseEnd_2926564] using wordTrace_append hprefix tailTrace_2926564
  have hstable : (prefixWord ++ tailWord_2926564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926564).length < 2 ^ (prefixWord ++ tailWord_2926564).sum := by decide
  have hdescent : baseEnd_2926564 < baseStart_2926564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926604 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 2, 5, 3]
def baseStart_2926604 : Nat := 118140960795 + 2926604 * 2 ^ 59
def prefixEnd_2926604 : Nat := 4983230072969 + 3 ^ 40 * 2926604 * 2
def baseEnd_2926604 : Nat := 1502754537370972882090799

theorem tailTrace_2926604 : CollatzResearch.WordTrace tailWord_2926604 prefixEnd_2926604 1502754537370972882090799 := by
  unfold tailWord_2926604
  simp only [CollatzResearch.WordTrace]
  refine ⟨53371008544710503507637433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71161344726280671343516577 53371008544710503507637433)
  ·
    refine ⟨40028256408532877630728075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53371008544710503507637433 40028256408532877630728075)
    ·
      refine ⟨60042384612799316446092113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40028256408532877630728075 60042384612799316446092113)
      ·
        refine ⟨45031788459599487334569085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60042384612799316446092113 45031788459599487334569085)
        ·
          refine ⟨16886920672349807750463407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45031788459599487334569085 16886920672349807750463407)
          ·
            refine ⟨25330381008524711625695111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16886920672349807750463407 25330381008524711625695111)
            ·
              refine ⟨37995571512787067438542667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25330381008524711625695111 37995571512787067438542667)
              ·
                refine ⟨56993357269180601157814001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37995571512787067438542667 56993357269180601157814001)
                ·
                  refine ⟨42745017951885450868360501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56993357269180601157814001 42745017951885450868360501)
                  ·
                    refine ⟨4007345432989261018908797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42745017951885450868360501 4007345432989261018908797)
                    ·
                      refine ⟨1502754537370972882090799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4007345432989261018908797 1502754537370972882090799)
                      ·
                        rfl

theorem cell23_2926604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_2926604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926604 prefixEnd_2926604 := by exact prefixLift 2926604
  have htrace : WordTrace (prefixWord ++ tailWord_2926604) baseStart_2926604 baseEnd_2926604 := by
    simpa [prefixWord, tailWord_2926604, baseEnd_2926604] using wordTrace_append hprefix tailTrace_2926604
  have hstable : (prefixWord ++ tailWord_2926604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926604).length < 2 ^ (prefixWord ++ tailWord_2926604).sum := by decide
  have hdescent : baseEnd_2926604 < baseStart_2926604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926632 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 3, 4]
def baseStart_2926632 : Nat := 118140960795 + 2926632 * 2 ^ 59
def prefixEnd_2926632 : Nat := 4983230072969 + 3 ^ 40 * 2926632 * 2
def baseEnd_2926632 : Nat := 500922971609766257513557

theorem tailTrace_2926632 : CollatzResearch.WordTrace tailWord_2926632 prefixEnd_2926632 500922971609766257513557 := by
  unfold tailWord_2926632
  simp only [CollatzResearch.WordTrace]
  refine ⟨53371519166659783898647075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71162025555546378531529433 53371519166659783898647075)
  ·
    refine ⟨80057278749989675847970613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53371519166659783898647075 80057278749989675847970613)
    ·
      refine ⟨7505369882811532110747245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80057278749989675847970613 7505369882811532110747245)
      ·
        refine ⟨2814513706054324541530217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7505369882811532110747245 2814513706054324541530217)
        ·
          refine ⟨2110885279540743406147663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2814513706054324541530217 2110885279540743406147663)
          ·
            refine ⟨3166327919311115109221495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110885279540743406147663 3166327919311115109221495)
            ·
              refine ⟨4749491878966672663832243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166327919311115109221495 4749491878966672663832243)
              ·
                refine ⟨7124237818450008995748365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4749491878966672663832243 7124237818450008995748365)
                ·
                  refine ⟨2671589181918753373405637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7124237818450008995748365 2671589181918753373405637)
                  ·
                    refine ⟨500922971609766257513557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2671589181918753373405637 500922971609766257513557)
                    ·
                      rfl

theorem cell23_2926632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_2926632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926632 prefixEnd_2926632 := by exact prefixLift 2926632
  have htrace : WordTrace (prefixWord ++ tailWord_2926632) baseStart_2926632 baseEnd_2926632 := by
    simpa [prefixWord, tailWord_2926632, baseEnd_2926632] using wordTrace_append hprefix tailTrace_2926632
  have hstable : (prefixWord ++ tailWord_2926632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926632).length < 2 ^ (prefixWord ++ tailWord_2926632).sum := by decide
  have hdescent : baseEnd_2926632 < baseStart_2926632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926684 : List Nat := [2, 2, 4, 1, 1, 13]
def baseStart_2926684 : Nat := 118140960795 + 2926684 * 2 ^ 59
def prefixEnd_2926684 : Nat := 4983230072969 + 3 ^ 40 * 2926684 * 2
def baseEnd_2926684 : Nat := 6184344098038405634117

theorem tailTrace_2926684 : CollatzResearch.WordTrace tailWord_2926684 prefixEnd_2926684 6184344098038405634117 := by
  unfold tailWord_2926684
  simp only [CollatzResearch.WordTrace]
  refine ⟨53372467464565590339093553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71163289952754120452124737 53372467464565590339093553)
  ·
    refine ⟨40029350598424192754320165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53372467464565590339093553 40029350598424192754320165)
    ·
      refine ⟨7505503237204536141435031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40029350598424192754320165 7505503237204536141435031)
      ·
        refine ⟨11258254855806804212152547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7505503237204536141435031 11258254855806804212152547)
        ·
          refine ⟨16887382283710206318228821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11258254855806804212152547 16887382283710206318228821)
          ·
            refine ⟨6184344098038405634117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 16887382283710206318228821 6184344098038405634117)
            ·
              rfl

theorem cell23_2926684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 13].length) (baseStart_2926684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926684 prefixEnd_2926684 := by exact prefixLift 2926684
  have htrace : WordTrace (prefixWord ++ tailWord_2926684) baseStart_2926684 baseEnd_2926684 := by
    simpa [prefixWord, tailWord_2926684, baseEnd_2926684] using wordTrace_append hprefix tailTrace_2926684
  have hstable : (prefixWord ++ tailWord_2926684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926684).length < 2 ^ (prefixWord ++ tailWord_2926684).sum := by decide
  have hdescent : baseEnd_2926684 < baseStart_2926684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926688 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 2, 4]
def baseStart_2926688 : Nat := 118140960795 + 2926688 * 2 ^ 59
def prefixEnd_2926688 : Nat := 4983230072969 + 3 ^ 40 * 2926688 * 2
def baseEnd_2926688 : Nat := 500932556581983517813471

theorem tailTrace_2926688 : CollatzResearch.WordTrace tailWord_2926688 prefixEnd_2926688 500932556581983517813471 := by
  unfold tailWord_2926688
  simp only [CollatzResearch.WordTrace]
  refine ⟨53372540410558344680666359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71163387214077792907555145 53372540410558344680666359)
  ·
    refine ⟨80058810615837517020999539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53372540410558344680666359 80058810615837517020999539)
    ·
      refine ⟨120088215923756275531499309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80058810615837517020999539 120088215923756275531499309)
      ·
        refine ⟨45033080971408603324312241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120088215923756275531499309 45033080971408603324312241)
        ·
          refine ⟨33774810728556452493234181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45033080971408603324312241 33774810728556452493234181)
          ·
            refine ⟨6332777011604334842481409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33774810728556452493234181 6332777011604334842481409)
            ·
              refine ⟨4749582758703251131861057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6332777011604334842481409 4749582758703251131861057)
              ·
                refine ⟨3562187069027438348895793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4749582758703251131861057 3562187069027438348895793)
                ·
                  refine ⟨2671640301770578761671845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3562187069027438348895793 2671640301770578761671845)
                  ·
                    refine ⟨500932556581983517813471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2671640301770578761671845 500932556581983517813471)
                    ·
                      rfl

theorem cell23_2926688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2, 4].length) (baseStart_2926688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926688 prefixEnd_2926688 := by exact prefixLift 2926688
  have htrace : WordTrace (prefixWord ++ tailWord_2926688) baseStart_2926688 baseEnd_2926688 := by
    simpa [prefixWord, tailWord_2926688, baseEnd_2926688] using wordTrace_append hprefix tailTrace_2926688
  have hstable : (prefixWord ++ tailWord_2926688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926688).length < 2 ^ (prefixWord ++ tailWord_2926688).sum := by decide
  have hdescent : baseEnd_2926688 < baseStart_2926688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926711 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 3]
def baseStart_2926711 : Nat := 118140960795 + 2926711 * 2 ^ 59
def prefixEnd_2926711 : Nat := 4983230072969 + 3 ^ 40 * 2926711 * 2
def baseEnd_2926711 : Nat := 1502809479801003963452807

theorem tailTrace_2926711 : CollatzResearch.WordTrace tailWord_2926711 prefixEnd_2926711 1502809479801003963452807 := by
  unfold tailWord_2926711
  simp only [CollatzResearch.WordTrace]
  refine ⟨106745919700033364289419987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71163946466688909526279991 106745919700033364289419987)
  ·
    refine ⟨160118879550050046434129981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106745919700033364289419987 160118879550050046434129981)
    ·
      refine ⟨60044579831268767412798743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160118879550050046434129981 60044579831268767412798743)
      ·
        refine ⟨90066869746903151119198115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60044579831268767412798743 90066869746903151119198115)
        ·
          refine ⟨135100304620354726678797173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90066869746903151119198115 135100304620354726678797173)
          ·
            refine ⟨12665653558158255626137235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135100304620354726678797173 12665653558158255626137235)
            ·
              refine ⟨18998480337237383439205853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12665653558158255626137235 18998480337237383439205853)
              ·
                refine ⟨7124430126464018789702195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18998480337237383439205853 7124430126464018789702195)
                ·
                  refine ⟨10686645189696028184553293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7124430126464018789702195 10686645189696028184553293)
                  ·
                    refine ⟨4007491946136010569207485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10686645189696028184553293 4007491946136010569207485)
                    ·
                      refine ⟨1502809479801003963452807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4007491946136010569207485 1502809479801003963452807)
                      ·
                        rfl

theorem cell23_2926711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_2926711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926711 prefixEnd_2926711 := by exact prefixLift 2926711
  have htrace : WordTrace (prefixWord ++ tailWord_2926711) baseStart_2926711 baseEnd_2926711 := by
    simpa [prefixWord, tailWord_2926711, baseEnd_2926711] using wordTrace_append hprefix tailTrace_2926711
  have hstable : (prefixWord ++ tailWord_2926711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926711).length < 2 ^ (prefixWord ++ tailWord_2926711).sum := by decide
  have hdescent : baseEnd_2926711 < baseStart_2926711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926728 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2926728 : Nat := 118140960795 + 2926728 * 2 ^ 59
def prefixEnd_2926728 : Nat := 4983230072969 + 3 ^ 40 * 2926728 * 2
def baseEnd_2926728 : Nat := 1502818208972130396940229

theorem tailTrace_2926728 : CollatzResearch.WordTrace tailWord_2926728 prefixEnd_2926728 1502818208972130396940229 := by
  unfold tailWord_2926728
  simp only [CollatzResearch.WordTrace]
  refine ⟨53373269870485888096394419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71164359827314517461859225 53373269870485888096394419)
  ·
    refine ⟨80059904805728832144591629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53373269870485888096394419 80059904805728832144591629)
    ·
      refine ⟨30022464302148312054221861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80059904805728832144591629 30022464302148312054221861)
      ·
        refine ⟨5629212056652808510166599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30022464302148312054221861 5629212056652808510166599)
        ·
          refine ⟨8443818084979212765249899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5629212056652808510166599 8443818084979212765249899)
          ·
            refine ⟨12665727127468819147874849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8443818084979212765249899 12665727127468819147874849)
            ·
              refine ⟨9499295345601614360906137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12665727127468819147874849 9499295345601614360906137)
              ·
                refine ⟨7124471509201210770679603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9499295345601614360906137 7124471509201210770679603)
                ·
                  refine ⟨10686707263801816156019405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7124471509201210770679603 10686707263801816156019405)
                  ·
                    refine ⟨4007515223925681058507277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10686707263801816156019405 4007515223925681058507277)
                    ·
                      refine ⟨1502818208972130396940229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4007515223925681058507277 1502818208972130396940229)
                      ·
                        rfl

theorem cell23_2926728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2926728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926728 prefixEnd_2926728 := by exact prefixLift 2926728
  have htrace : WordTrace (prefixWord ++ tailWord_2926728) baseStart_2926728 baseEnd_2926728 := by
    simpa [prefixWord, tailWord_2926728, baseEnd_2926728] using wordTrace_append hprefix tailTrace_2926728
  have hstable : (prefixWord ++ tailWord_2926728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926728).length < 2 ^ (prefixWord ++ tailWord_2926728).sum := by decide
  have hdescent : baseEnd_2926728 < baseStart_2926728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926762 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2926762 : Nat := 118140960795 + 2926762 * 2 ^ 59
def prefixEnd_2926762 : Nat := 4983230072969 + 3 ^ 40 * 2926762 * 2
def baseEnd_2926762 : Nat := 1502835667314383263915073

theorem tailTrace_2926762 : CollatzResearch.WordTrace tailWord_2926762 prefixEnd_2926762 1502835667314383263915073 := by
  unfold tailWord_2926762
  simp only [CollatzResearch.WordTrace]
  refine ⟨26686944955712149999881635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71165186548565733333017693 26686944955712149999881635)
  ·
    refine ⟨40030417433568224999822453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26686944955712149999881635 40030417433568224999822453)
    ·
      refine ⟨3752851634397021093733355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40030417433568224999822453 3752851634397021093733355)
      ·
        refine ⟨5629277451595531640600033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3752851634397021093733355 5629277451595531640600033)
        ·
          refine ⟨4221958088696648730450025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5629277451595531640600033 4221958088696648730450025)
          ·
            refine ⟨3166468566522486547837519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4221958088696648730450025 3166468566522486547837519)
            ·
              refine ⟨4749702849783729821756279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166468566522486547837519 4749702849783729821756279)
              ·
                refine ⟨7124554274675594732634419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4749702849783729821756279 7124554274675594732634419)
                ·
                  refine ⟨10686831412013392098951629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7124554274675594732634419 10686831412013392098951629)
                  ·
                    refine ⟨4007561779505022037106861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10686831412013392098951629 4007561779505022037106861)
                    ·
                      refine ⟨1502835667314383263915073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4007561779505022037106861 1502835667314383263915073)
                      ·
                        rfl

theorem cell23_2926762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2926762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926762 prefixEnd_2926762 := by exact prefixLift 2926762
  have htrace : WordTrace (prefixWord ++ tailWord_2926762) baseStart_2926762 baseEnd_2926762 := by
    simpa [prefixWord, tailWord_2926762, baseEnd_2926762] using wordTrace_append hprefix tailTrace_2926762
  have hstable : (prefixWord ++ tailWord_2926762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926762).length < 2 ^ (prefixWord ++ tailWord_2926762).sum := by decide
  have hdescent : baseEnd_2926762 < baseStart_2926762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926768 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 8, 2, 2]
def baseStart_2926768 : Nat := 118140960795 + 2926768 * 2 ^ 59
def prefixEnd_2926768 : Nat := 4983230072969 + 3 ^ 40 * 2926768 * 2
def baseEnd_2926768 : Nat := 1502838748198310240440045

theorem tailTrace_2926768 : CollatzResearch.WordTrace tailWord_2926768 prefixEnd_2926768 1502838748198310240440045 := by
  unfold tailWord_2926768
  simp only [CollatzResearch.WordTrace]
  refine ⟨53373999330413431512122479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71165332440551242016163305 53373999330413431512122479)
  ·
    refine ⟨80060998995620147268183719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53373999330413431512122479 80060998995620147268183719)
    ·
      refine ⟨120091498493430220902275579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80060998995620147268183719 120091498493430220902275579)
      ·
        refine ⟨180137247740145331353413369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120091498493430220902275579 180137247740145331353413369)
        ·
          refine ⟨135102935805108998515060027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180137247740145331353413369 135102935805108998515060027)
          ·
            refine ⟨202654403707663497772590041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135102935805108998515060027 202654403707663497772590041)
            ·
              refine ⟨151990802780747623329442531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202654403707663497772590041 151990802780747623329442531)
              ·
                refine ⟨227986204171121434994163797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151990802780747623329442531 227986204171121434994163797)
                ·
                  refine ⟨2671713330130329316337857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 227986204171121434994163797 2671713330130329316337857)
                  ·
                    refine ⟨2003784997597746987253393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2671713330130329316337857 2003784997597746987253393)
                    ·
                      refine ⟨1502838748198310240440045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003784997597746987253393 1502838748198310240440045)
                      ·
                        rfl

theorem cell23_2926768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8, 2, 2].length) (baseStart_2926768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926768 prefixEnd_2926768 := by exact prefixLift 2926768
  have htrace : WordTrace (prefixWord ++ tailWord_2926768) baseStart_2926768 baseEnd_2926768 := by
    simpa [prefixWord, tailWord_2926768, baseEnd_2926768] using wordTrace_append hprefix tailTrace_2926768
  have hstable : (prefixWord ++ tailWord_2926768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926768).length < 2 ^ (prefixWord ++ tailWord_2926768).sum := by decide
  have hdescent : baseEnd_2926768 < baseStart_2926768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926788 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2926788 : Nat := 118140960795 + 2926788 * 2 ^ 59
def prefixEnd_2926788 : Nat := 4983230072969 + 3 ^ 40 * 2926788 * 2
def baseEnd_2926788 : Nat := 1502849017811400162189953

theorem tailTrace_2926788 : CollatzResearch.WordTrace tailWord_2926788 prefixEnd_2926788 1502849017811400162189953 := by
  unfold tailWord_2926788
  simp only [CollatzResearch.WordTrace]
  refine ⟨53374364060377203219986509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71165818747169604293315345 53374364060377203219986509)
  ·
    refine ⟨20015386522641451207494941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53374364060377203219986509 20015386522641451207494941)
    ·
      refine ⟨7505769945990544202810603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20015386522641451207494941 7505769945990544202810603)
      ·
        refine ⟨11258654918985816304215905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7505769945990544202810603 11258654918985816304215905)
        ·
          refine ⟨8443991189239362228161929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11258654918985816304215905 8443991189239362228161929)
          ·
            refine ⟨6332993391929521671121447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8443991189239362228161929 6332993391929521671121447)
            ·
              refine ⟨9499490087894282506682171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6332993391929521671121447 9499490087894282506682171)
              ·
                refine ⟨14249235131841423760023257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9499490087894282506682171 14249235131841423760023257)
                ·
                  refine ⟨10686926348881067820017443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14249235131841423760023257 10686926348881067820017443)
                  ·
                    refine ⟨16030389523321601730026165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10686926348881067820017443 16030389523321601730026165)
                    ·
                      refine ⟨1502849017811400162189953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16030389523321601730026165 1502849017811400162189953)
                      ·
                        rfl

theorem cell23_2926788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2926788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926788 prefixEnd_2926788 := by exact prefixLift 2926788
  have htrace : WordTrace (prefixWord ++ tailWord_2926788) baseStart_2926788 baseEnd_2926788 := by
    simpa [prefixWord, tailWord_2926788, baseEnd_2926788] using wordTrace_append hprefix tailTrace_2926788
  have hstable : (prefixWord ++ tailWord_2926788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926788).length < 2 ^ (prefixWord ++ tailWord_2926788).sum := by decide
  have hdescent : baseEnd_2926788 < baseStart_2926788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926801 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 4, 3, 3]
def baseStart_2926801 : Nat := 118140960795 + 2926801 * 2 ^ 59
def prefixEnd_2926801 : Nat := 4983230072969 + 3 ^ 40 * 2926801 * 2
def baseEnd_2926801 : Nat := 1502855693059908611327393

theorem tailTrace_2926801 : CollatzResearch.WordTrace tailWord_2926801 prefixEnd_2926801 1502855693059908611327393 := by
  unfold tailWord_2926801
  simp only [CollatzResearch.WordTrace]
  refine ⟨106749202269707309660196257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71166134846471539773464171 106749202269707309660196257)
  ·
    refine ⟨80061901702280482245147193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106749202269707309660196257 80061901702280482245147193)
    ·
      refine ⟨60046426276710361683860395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80061901702280482245147193 60046426276710361683860395)
      ·
        refine ⟨90069639415065542525790593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60046426276710361683860395 90069639415065542525790593)
        ·
          refine ⟨67552229561299156894342945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90069639415065542525790593 67552229561299156894342945)
          ·
            refine ⟨50664172170974367670757209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67552229561299156894342945 50664172170974367670757209)
            ·
              refine ⟨37998129128230775753067907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50664172170974367670757209 37998129128230775753067907)
              ·
                refine ⟨56997193692346163629601861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37998129128230775753067907 56997193692346163629601861)
                ·
                  refine ⟨10686973817314905680550349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56997193692346163629601861 10686973817314905680550349)
                  ·
                    refine ⟨4007615181493089630206381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10686973817314905680550349 4007615181493089630206381)
                    ·
                      refine ⟨1502855693059908611327393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4007615181493089630206381 1502855693059908611327393)
                      ·
                        rfl

theorem cell23_2926801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_2926801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926801 prefixEnd_2926801 := by exact prefixLift 2926801
  have htrace : WordTrace (prefixWord ++ tailWord_2926801) baseStart_2926801 baseEnd_2926801 := by
    simpa [prefixWord, tailWord_2926801, baseEnd_2926801] using wordTrace_append hprefix tailTrace_2926801
  have hstable : (prefixWord ++ tailWord_2926801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926801).length < 2 ^ (prefixWord ++ tailWord_2926801).sum := by decide
  have hdescent : baseEnd_2926801 < baseStart_2926801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926808 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 7]
def baseStart_2926808 : Nat := 118140960795 + 2926808 * 2 ^ 59
def prefixEnd_2926808 : Nat := 4983230072969 + 3 ^ 40 * 2926808 * 2
def baseEnd_2926808 : Nat := 166984365269387787104429

theorem tailTrace_2926808 : CollatzResearch.WordTrace tailWord_2926808 prefixEnd_2926808 166984365269387787104429 := by
  unfold tailWord_2926808
  simp only [CollatzResearch.WordTrace]
  refine ⟨53374728790340974927850539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71166305053787966570467385 53374728790340974927850539)
  ·
    refine ⟨80062093185511462391775809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53374728790340974927850539 80062093185511462391775809)
    ·
      refine ⟨60046569889133596793831857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80062093185511462391775809 60046569889133596793831857)
      ·
        refine ⟨45034927416850197595373893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60046569889133596793831857 45034927416850197595373893)
        ·
          refine ⟨8444048890659412049132605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45034927416850197595373893 8444048890659412049132605)
          ·
            refine ⟨3166518333997279518424727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8444048890659412049132605 3166518333997279518424727)
            ·
              refine ⟨4749777500995919277637091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166518333997279518424727 4749777500995919277637091)
              ·
                refine ⟨7124666251493878916455637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4749777500995919277637091 7124666251493878916455637)
                ·
                  refine ⟨166984365269387787104429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7124666251493878916455637 166984365269387787104429)
                  ·
                    rfl

theorem cell23_2926808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 7].length) (baseStart_2926808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926808 prefixEnd_2926808 := by exact prefixLift 2926808
  have htrace : WordTrace (prefixWord ++ tailWord_2926808) baseStart_2926808 baseEnd_2926808 := by
    simpa [prefixWord, tailWord_2926808, baseEnd_2926808] using wordTrace_append hprefix tailTrace_2926808
  have hstable : (prefixWord ++ tailWord_2926808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926808).length < 2 ^ (prefixWord ++ tailWord_2926808).sum := by decide
  have hdescent : baseEnd_2926808 < baseStart_2926808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926819 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2926819 : Nat := 118140960795 + 2926819 * 2 ^ 59
def prefixEnd_2926819 : Nat := 4983230072969 + 3 ^ 40 * 2926819 * 2
def baseEnd_2926819 : Nat := 1502864935711689540902311

theorem tailTrace_2926819 : CollatzResearch.WordTrace tailWord_2926819 prefixEnd_2926819 1502864935711689540902311 := by
  unfold tailWord_2926819
  simp only [CollatzResearch.WordTrace]
  refine ⟨106749858783642098734351511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71166572522428065822901007 106749858783642098734351511)
  ·
    refine ⟨160124788175463148101527267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106749858783642098734351511 160124788175463148101527267)
    ·
      refine ⟨240187182263194722152290901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160124788175463148101527267 240187182263194722152290901)
      ·
        refine ⟨2814693542146813150222159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 240187182263194722152290901 2814693542146813150222159)
        ·
          refine ⟨4222040313220219725333239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2814693542146813150222159 4222040313220219725333239)
          ·
            refine ⟨6333060469830329587999859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222040313220219725333239 6333060469830329587999859)
            ·
              refine ⟨9499590704745494381999789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6333060469830329587999859 9499590704745494381999789)
              ·
                refine ⟨3562346514279560393249921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9499590704745494381999789 3562346514279560393249921)
                ·
                  refine ⟨2671759885709670294937441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3562346514279560393249921 2671759885709670294937441)
                  ·
                    refine ⟨2003819914282252721203081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2671759885709670294937441 2003819914282252721203081)
                    ·
                      refine ⟨1502864935711689540902311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003819914282252721203081 1502864935711689540902311)
                      ·
                        rfl

theorem cell23_2926819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2926819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926819 prefixEnd_2926819 := by exact prefixLift 2926819
  have htrace : WordTrace (prefixWord ++ tailWord_2926819) baseStart_2926819 baseEnd_2926819 := by
    simpa [prefixWord, tailWord_2926819, baseEnd_2926819] using wordTrace_append hprefix tailTrace_2926819
  have hstable : (prefixWord ++ tailWord_2926819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926819).length < 2 ^ (prefixWord ++ tailWord_2926819).sum := by decide
  have hdescent : baseEnd_2926819 < baseStart_2926819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926838 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_2926838 : Nat := 118140960795 + 2926838 * 2 ^ 59
def prefixEnd_2926838 : Nat := 4983230072969 + 3 ^ 40 * 2926838 * 2
def baseEnd_2926838 : Nat := 500958230614708322188241

theorem tailTrace_2926838 : CollatzResearch.WordTrace tailWord_2926838 prefixEnd_2926838 500958230614708322188241 := by
  unfold tailWord_2926838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6671909485660829061205823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71167034513715509986195445 6671909485660829061205823)
  ·
    refine ⟨10007864228491243591808735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6671909485660829061205823 10007864228491243591808735)
    ·
      refine ⟨15011796342736865387713103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10007864228491243591808735 15011796342736865387713103)
      ·
        refine ⟨22517694514105298081569655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15011796342736865387713103 22517694514105298081569655)
        ·
          refine ⟨33776541771157947122354483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22517694514105298081569655 33776541771157947122354483)
          ·
            refine ⟨50664812656736920683531725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33776541771157947122354483 50664812656736920683531725)
            ·
              refine ⟨18999304746276345256324397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50664812656736920683531725 18999304746276345256324397)
              ·
                refine ⟨7124739279853629471121649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18999304746276345256324397 7124739279853629471121649)
                ·
                  refine ⟨5343554459890222103341237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7124739279853629471121649 5343554459890222103341237)
                  ·
                    refine ⟨500958230614708322188241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5343554459890222103341237 500958230614708322188241)
                    ·
                      rfl

theorem cell23_2926838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_2926838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926838 prefixEnd_2926838 := by exact prefixLift 2926838
  have htrace : WordTrace (prefixWord ++ tailWord_2926838) baseStart_2926838 baseEnd_2926838 := by
    simpa [prefixWord, tailWord_2926838, baseEnd_2926838] using wordTrace_append hprefix tailTrace_2926838
  have hstable : (prefixWord ++ tailWord_2926838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926838).length < 2 ^ (prefixWord ++ tailWord_2926838).sum := by decide
  have hdescent : baseEnd_2926838 < baseStart_2926838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926858 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_2926858 : Nat := 118140960795 + 2926858 * 2 ^ 59
def prefixEnd_2926858 : Nat := 4983230072969 + 3 ^ 40 * 2926858 * 2
def baseEnd_2926858 : Nat := 1502884961457214888314631

theorem tailTrace_2926858 : CollatzResearch.WordTrace tailWord_2926858 prefixEnd_2926858 1502884961457214888314631 := by
  unfold tailWord_2926858
  simp only [CollatzResearch.WordTrace]
  refine ⟨26687820307625202098755307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71167520820333872263347485 26687820307625202098755307)
  ·
    refine ⟨40031730461437803148132961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26687820307625202098755307 40031730461437803148132961)
    ·
      refine ⟨30023797846078352361099721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40031730461437803148132961 30023797846078352361099721)
      ·
        refine ⟨22517848384558764270824791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30023797846078352361099721 22517848384558764270824791)
        ·
          refine ⟨33776772576838146406237187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22517848384558764270824791 33776772576838146406237187)
          ·
            refine ⟨50665158865257219609355781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33776772576838146406237187 50665158865257219609355781)
            ·
              refine ⟨9499717287235728676754209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50665158865257219609355781 9499717287235728676754209)
              ·
                refine ⟨7124787965426796507565657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9499717287235728676754209 7124787965426796507565657)
                ·
                  refine ⟨5343590974070097380674243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7124787965426796507565657 5343590974070097380674243)
                  ·
                    refine ⟨8015386461105146071011365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5343590974070097380674243 8015386461105146071011365)
                    ·
                      refine ⟨1502884961457214888314631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8015386461105146071011365 1502884961457214888314631)
                      ·
                        rfl

theorem cell23_2926858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_2926858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926858 prefixEnd_2926858 := by exact prefixLift 2926858
  have htrace : WordTrace (prefixWord ++ tailWord_2926858) baseStart_2926858 baseEnd_2926858 := by
    simpa [prefixWord, tailWord_2926858, baseEnd_2926858] using wordTrace_append hprefix tailTrace_2926858
  have hstable : (prefixWord ++ tailWord_2926858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926858).length < 2 ^ (prefixWord ++ tailWord_2926858).sum := by decide
  have hdescent : baseEnd_2926858 < baseStart_2926858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926885 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 3, 4]
def baseStart_2926885 : Nat := 118140960795 + 2926885 * 2 ^ 59
def prefixEnd_2926885 : Nat := 4983230072969 + 3 ^ 40 * 2926885 * 2
def baseEnd_2926885 : Nat := 500966275144962094225669

theorem tailTrace_2926885 : CollatzResearch.WordTrace tailWord_2926885 prefixEnd_2926885 500966275144962094225669 := by
  unfold tailWord_2926885
  simp only [CollatzResearch.WordTrace]
  refine ⟨106752266001402992006254109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71168177334268661337502739 106752266001402992006254109)
  ·
    refine ⟨40032099750526122002345291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106752266001402992006254109 40032099750526122002345291)
    ·
      refine ⟨60048149625789183003517937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40032099750526122002345291 60048149625789183003517937)
      ·
        refine ⟨45036112219341887252638453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60048149625789183003517937 45036112219341887252638453)
        ·
          refine ⟨4222135520563301929934855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45036112219341887252638453 4222135520563301929934855)
          ·
            refine ⟨6333203280844952894902283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222135520563301929934855 6333203280844952894902283)
            ·
              refine ⟨9499804921267429342353425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6333203280844952894902283 9499804921267429342353425)
              ·
                refine ⟨7124853690950572006765069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9499804921267429342353425 7124853690950572006765069)
                ·
                  refine ⟨2671820134106464502536901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7124853690950572006765069 2671820134106464502536901)
                  ·
                    refine ⟨500966275144962094225669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2671820134106464502536901 500966275144962094225669)
                    ·
                      rfl

theorem cell23_2926885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_2926885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926885 prefixEnd_2926885 := by exact prefixLift 2926885
  have htrace : WordTrace (prefixWord ++ tailWord_2926885) baseStart_2926885 baseEnd_2926885 := by
    simpa [prefixWord, tailWord_2926885, baseEnd_2926885] using wordTrace_append hprefix tailTrace_2926885
  have hstable : (prefixWord ++ tailWord_2926885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926885).length < 2 ^ (prefixWord ++ tailWord_2926885).sum := by decide
  have hdescent : baseEnd_2926885 < baseStart_2926885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926931 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 4]
def baseStart_2926931 : Nat := 118140960795 + 2926931 * 2 ^ 59
def prefixEnd_2926931 : Nat := 4983230072969 + 3 ^ 40 * 2926931 * 2
def baseEnd_2926931 : Nat := 1502922445544993102701795

theorem tailTrace_2926931 : CollatzResearch.WordTrace tailWord_2926931 prefixEnd_2926931 1502922445544993102701795 := by
  unfold tailWord_2926931
  simp only [CollatzResearch.WordTrace]
  refine ⟨106753943759236341862428647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71169295839490894574952431 106753943759236341862428647)
  ·
    refine ⟨160130915638854512793642971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106753943759236341862428647 160130915638854512793642971)
    ·
      refine ⟨240196373458281769190464457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160130915638854512793642971 240196373458281769190464457)
      ·
        refine ⟨180147280093711326892848343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240196373458281769190464457 180147280093711326892848343)
        ·
          refine ⟨270220920140566990339272515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180147280093711326892848343 270220920140566990339272515)
          ·
            refine ⟨405331380210850485508908773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270220920140566990339272515 405331380210850485508908773)
            ·
              refine ⟨75999633789534466032920395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 405331380210850485508908773 75999633789534466032920395)
              ·
                refine ⟨113999450684301699049380593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75999633789534466032920395 113999450684301699049380593)
                ·
                  refine ⟨85499588013226274287035445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113999450684301699049380593 85499588013226274287035445)
                  ·
                    refine ⟨8015586376239963214409573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85499588013226274287035445 8015586376239963214409573)
                    ·
                      refine ⟨1502922445544993102701795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8015586376239963214409573 1502922445544993102701795)
                      ·
                        rfl

theorem cell23_2926931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_2926931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926931 prefixEnd_2926931 := by exact prefixLift 2926931
  have htrace : WordTrace (prefixWord ++ tailWord_2926931) baseStart_2926931 baseEnd_2926931 := by
    simpa [prefixWord, tailWord_2926931, baseEnd_2926931] using wordTrace_append hprefix tailTrace_2926931
  have hstable : (prefixWord ++ tailWord_2926931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926931).length < 2 ^ (prefixWord ++ tailWord_2926931).sum := by decide
  have hdescent : baseEnd_2926931 < baseStart_2926931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926971 : List Nat := [1, 1, 1, 1, 1, 7, 11]
def baseStart_2926971 : Nat := 118140960795 + 2926971 * 2 ^ 59
def prefixEnd_2926971 : Nat := 4983230072969 + 3 ^ 40 * 2926971 * 2
def baseEnd_2926971 : Nat := 18554851663841641311131

theorem tailTrace_2926971 : CollatzResearch.WordTrace tailWord_2926971 prefixEnd_2926971 18554851663841641311131 := by
  unfold tailWord_2926971
  simp only [CollatzResearch.WordTrace]
  refine ⟨106755402679091428693884767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71170268452727619129256511 106755402679091428693884767)
  ·
    refine ⟨160133104018637143040827151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106755402679091428693884767 160133104018637143040827151)
    ·
      refine ⟨240199656027955714561240727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160133104018637143040827151 240199656027955714561240727)
      ·
        refine ⟨360299484041933571841861091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240199656027955714561240727 360299484041933571841861091)
        ·
          refine ⟨540449226062900357762791637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360299484041933571841861091 540449226062900357762791637)
          ·
            refine ⟨12666778735849227135065429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 540449226062900357762791637 12666778735849227135065429)
            ·
              refine ⟨18554851663841641311131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12666778735849227135065429 18554851663841641311131)
              ·
                rfl

theorem cell23_2926971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 11].length) (baseStart_2926971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926971 prefixEnd_2926971 := by exact prefixLift 2926971
  have htrace : WordTrace (prefixWord ++ tailWord_2926971) baseStart_2926971 baseEnd_2926971 := by
    simpa [prefixWord, tailWord_2926971, baseEnd_2926971] using wordTrace_append hprefix tailTrace_2926971
  have hstable : (prefixWord ++ tailWord_2926971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926971).length < 2 ^ (prefixWord ++ tailWord_2926971).sum := by decide
  have hdescent : baseEnd_2926971 < baseStart_2926971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926988 : List Nat := [2, 2, 1, 2, 1, 5, 2, 8]
def baseStart_2926988 : Nat := 118140960795 + 2926988 * 2 ^ 59
def prefixEnd_2926988 : Nat := 4983230072969 + 3 ^ 40 * 2926988 * 2
def baseEnd_2926988 : Nat := 55664878294159236284779

theorem tailTrace_2926988 : CollatzResearch.WordTrace tailWord_2926988 prefixEnd_2926988 55664878294159236284779 := by
  unfold tailWord_2926988
  simp only [CollatzResearch.WordTrace]
  refine ⟨53378011360014920298626809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71170681813353227064835745 53378011360014920298626809)
  ·
    refine ⟨40033508520011190223970107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53378011360014920298626809 40033508520011190223970107)
    ·
      refine ⟨60050262780016785335955161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40033508520011190223970107 60050262780016785335955161)
      ·
        refine ⟨45037697085012589001966371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60050262780016785335955161 45037697085012589001966371)
        ·
          refine ⟨67556545627518883502949557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45037697085012589001966371 67556545627518883502949557)
          ·
            refine ⟨6333426152579895328401521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67556545627518883502949557 6333426152579895328401521)
            ·
              refine ⟨4750069614434921496301141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6333426152579895328401521 4750069614434921496301141)
              ·
                refine ⟨55664878294159236284779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4750069614434921496301141 55664878294159236284779)
                ·
                  rfl

theorem cell23_2926988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 8].length) (baseStart_2926988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2926988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2926988 prefixEnd_2926988 := by exact prefixLift 2926988
  have htrace : WordTrace (prefixWord ++ tailWord_2926988) baseStart_2926988 baseEnd_2926988 := by
    simpa [prefixWord, tailWord_2926988, baseEnd_2926988] using wordTrace_append hprefix tailTrace_2926988
  have hstable : (prefixWord ++ tailWord_2926988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926988).length < 2 ^ (prefixWord ++ tailWord_2926988).sum := by decide
  have hdescent : baseEnd_2926988 < baseStart_2926988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927002 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3]
def baseStart_2927002 : Nat := 118140960795 + 2927002 * 2 ^ 59
def prefixEnd_2927002 : Nat := 4983230072969 + 3 ^ 40 * 2927002 * 2
def baseEnd_2927002 : Nat := 1502958902671462324913969

theorem tailTrace_2927002 : CollatzResearch.WordTrace tailWord_2927002 prefixEnd_2927002 1502958902671462324913969 := by
  unfold tailWord_2927002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26689133335494780247065815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71171022227986080658842173 26689133335494780247065815)
  ·
    refine ⟨40033700003242170370598723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26689133335494780247065815 40033700003242170370598723)
    ·
      refine ⟨60050550004863255555898085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40033700003242170370598723 60050550004863255555898085)
      ·
        refine ⟨11259478125911860416730891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60050550004863255555898085 11259478125911860416730891)
        ·
          refine ⟨16889217188867790625096337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11259478125911860416730891 16889217188867790625096337)
          ·
            refine ⟨12666912891650842968822253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16889217188867790625096337 12666912891650842968822253)
            ·
              refine ⟨4750092334369066113308345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12666912891650842968822253 4750092334369066113308345)
              ·
                refine ⟨3562569250776799584981259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4750092334369066113308345 3562569250776799584981259)
                ·
                  refine ⟨5343853876165199377471889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3562569250776799584981259 5343853876165199377471889)
                  ·
                    refine ⟨4007890407123899533103917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5343853876165199377471889 4007890407123899533103917)
                    ·
                      refine ⟨1502958902671462324913969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4007890407123899533103917 1502958902671462324913969)
                      ·
                        rfl

theorem cell23_2927002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_2927002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927002 prefixEnd_2927002 := by exact prefixLift 2927002
  have htrace : WordTrace (prefixWord ++ tailWord_2927002) baseStart_2927002 baseEnd_2927002 := by
    simpa [prefixWord, tailWord_2927002, baseEnd_2927002] using wordTrace_append hprefix tailTrace_2927002
  have hstable : (prefixWord ++ tailWord_2927002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927002).length < 2 ^ (prefixWord ++ tailWord_2927002).sum := by decide
  have hdescent : baseEnd_2927002 < baseStart_2927002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927015 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_2927015 : Nat := 118140960795 + 2927015 * 2 ^ 59
def prefixEnd_2927015 : Nat := 4983230072969 + 3 ^ 40 * 2927015 * 2
def baseEnd_2927015 : Nat := 1502965577919970774051409

theorem tailTrace_2927015 : CollatzResearch.WordTrace tailWord_2927015 prefixEnd_2927015 1502965577919970774051409 := by
  unfold tailWord_2927015
  simp only [CollatzResearch.WordTrace]
  refine ⟨106757007490932024208486499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71171338327288016138990999 106757007490932024208486499)
  ·
    refine ⟨160135511236398036312729749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106757007490932024208486499 160135511236398036312729749)
    ·
      refine ⟨7506352089206157952159207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 160135511236398036312729749 7506352089206157952159207)
      ·
        refine ⟨11259528133809236928238811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7506352089206157952159207 11259528133809236928238811)
        ·
          refine ⟨16889292200713855392358217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11259528133809236928238811 16889292200713855392358217)
          ·
            refine ⟨12666969150535391544268663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16889292200713855392358217 12666969150535391544268663)
            ·
              refine ⟨19000453725803087316402995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12666969150535391544268663 19000453725803087316402995)
              ·
                refine ⟨28500680588704630974604493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19000453725803087316402995 28500680588704630974604493)
                ·
                  refine ⟨10687755220764236615476685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28500680588704630974604493 10687755220764236615476685)
                  ·
                    refine ⟨4007908207786588730803757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10687755220764236615476685 4007908207786588730803757)
                    ·
                      refine ⟨1502965577919970774051409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4007908207786588730803757 1502965577919970774051409)
                      ·
                        rfl

theorem cell23_2927015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_2927015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927015 prefixEnd_2927015 := by exact prefixLift 2927015
  have htrace : WordTrace (prefixWord ++ tailWord_2927015) baseStart_2927015 baseEnd_2927015 := by
    simpa [prefixWord, tailWord_2927015, baseEnd_2927015] using wordTrace_append hprefix tailTrace_2927015
  have hstable : (prefixWord ++ tailWord_2927015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927015).length < 2 ^ (prefixWord ++ tailWord_2927015).sum := by decide
  have hdescent : baseEnd_2927015 < baseStart_2927015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927033 : List Nat := [1, 2, 1, 4, 3, 3, 2, 2, 1, 2, 2]
def baseStart_2927033 : Nat := 118140960795 + 2927033 * 2 ^ 59
def prefixEnd_2927033 : Nat := 4983230072969 + 3 ^ 40 * 2927033 * 2
def baseEnd_2927033 : Nat := 1502974820571751703626327

theorem tailTrace_2927033 : CollatzResearch.WordTrace tailWord_2927033 prefixEnd_2927033 1502974820571751703626327 := by
  unfold tailWord_2927033
  simp only [CollatzResearch.WordTrace]
  refine ⟨106757664004866813282641753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71171776003244542188427835 106757664004866813282641753)
  ·
    refine ⟨80068248003650109961981315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106757664004866813282641753 80068248003650109961981315)
    ·
      refine ⟨120102372005475164942971973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80068248003650109961981315 120102372005475164942971973)
      ·
        refine ⟨22519194751026593426807245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120102372005475164942971973 22519194751026593426807245)
        ·
          refine ⟨8444698031634972535052717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22519194751026593426807245 8444698031634972535052717)
          ·
            refine ⟨3166761761863114700644769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8444698031634972535052717 3166761761863114700644769)
            ·
              refine ⟨2375071321397336025483577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3166761761863114700644769 2375071321397336025483577)
              ·
                refine ⟨1781303491048002019112683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2375071321397336025483577 1781303491048002019112683)
                ·
                  refine ⟨2671955236572003028669025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781303491048002019112683 2671955236572003028669025)
                  ·
                    refine ⟨2003966427429002271501769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2671955236572003028669025 2003966427429002271501769)
                    ·
                      refine ⟨1502974820571751703626327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003966427429002271501769 1502974820571751703626327)
                      ·
                        rfl

theorem cell23_2927033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_2927033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927033 prefixEnd_2927033 := by exact prefixLift 2927033
  have htrace : WordTrace (prefixWord ++ tailWord_2927033) baseStart_2927033 baseEnd_2927033 := by
    simpa [prefixWord, tailWord_2927033, baseEnd_2927033] using wordTrace_append hprefix tailTrace_2927033
  have hstable : (prefixWord ++ tailWord_2927033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927033).length < 2 ^ (prefixWord ++ tailWord_2927033).sum := by decide
  have hdescent : baseEnd_2927033 < baseStart_2927033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927048 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 1, 8]
def baseStart_2927048 : Nat := 118140960795 + 2927048 * 2 ^ 59
def prefixEnd_2927048 : Nat := 4983230072969 + 3 ^ 40 * 2927048 * 2
def baseEnd_2927048 : Nat := 500994174260523048312919

theorem tailTrace_2927048 : CollatzResearch.WordTrace tailWord_2927048 prefixEnd_2927048 500994174260523048312919 := by
  unfold tailWord_2927048
  simp only [CollatzResearch.WordTrace]
  refine ⟨53379105549906235422218899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71172140733208313896291865 53379105549906235422218899)
  ·
    refine ⟨80068658324859353133328349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53379105549906235422218899 80068658324859353133328349)
    ·
      refine ⟨30025746871822257424998131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80068658324859353133328349 30025746871822257424998131)
      ·
        refine ⟨45038620307733386137497197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30025746871822257424998131 45038620307733386137497197)
        ·
          refine ⟨16889482615400019801561449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45038620307733386137497197 16889482615400019801561449)
          ·
            refine ⟨12667111961550014851171087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16889482615400019801561449 12667111961550014851171087)
            ·
              refine ⟨19000667942325022276756631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12667111961550014851171087 19000667942325022276756631)
              ·
                refine ⟨28501001913487533415134947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19000667942325022276756631 28501001913487533415134947)
                ·
                  refine ⟨42751502870231300122702421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28501001913487533415134947 42751502870231300122702421)
                  ·
                    refine ⟨500994174260523048312919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42751502870231300122702421 500994174260523048312919)
                    ·
                      rfl

theorem cell23_2927048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_2927048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927048 prefixEnd_2927048 := by exact prefixLift 2927048
  have htrace : WordTrace (prefixWord ++ tailWord_2927048) baseStart_2927048 baseEnd_2927048 := by
    simpa [prefixWord, tailWord_2927048, baseEnd_2927048] using wordTrace_append hprefix tailTrace_2927048
  have hstable : (prefixWord ++ tailWord_2927048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927048).length < 2 ^ (prefixWord ++ tailWord_2927048).sum := by decide
  have hdescent : baseEnd_2927048 < baseStart_2927048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927072 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 4, 2, 2]
def baseStart_2927072 : Nat := 118140960795 + 2927072 * 2 ^ 59
def prefixEnd_2927072 : Nat := 4983230072969 + 3 ^ 40 * 2927072 * 2
def baseEnd_2927072 : Nat := 1502994846317277051038647

theorem tailTrace_2927072 : CollatzResearch.WordTrace tailWord_2927072 prefixEnd_2927072 1502994846317277051038647 := by
  unfold tailWord_2927072
  simp only [CollatzResearch.WordTrace]
  refine ⟨53379543225862761471655735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71172724301150348628874313 53379543225862761471655735)
  ·
    refine ⟨80069314838794142207483603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53379543225862761471655735 80069314838794142207483603)
    ·
      refine ⟨120103972258191213311225405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80069314838794142207483603 120103972258191213311225405)
      ·
        refine ⟨45038989596821704991709527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120103972258191213311225405 45038989596821704991709527)
        ·
          refine ⟨67558484395232557487564291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45038989596821704991709527 67558484395232557487564291)
          ·
            refine ⟨101337726592848836231346437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67558484395232557487564291 101337726592848836231346437)
            ·
              refine ⟨19000823736159156793377457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101337726592848836231346437 19000823736159156793377457)
              ·
                refine ⟨14250617802119367595033093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19000823736159156793377457 14250617802119367595033093)
                ·
                  refine ⟨2671990837897381424068705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14250617802119367595033093 2671990837897381424068705)
                  ·
                    refine ⟨2003993128423036068051529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2671990837897381424068705 2003993128423036068051529)
                    ·
                      refine ⟨1502994846317277051038647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2003993128423036068051529 1502994846317277051038647)
                      ·
                        rfl

theorem cell23_2927072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_2927072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927072 prefixEnd_2927072 := by exact prefixLift 2927072
  have htrace : WordTrace (prefixWord ++ tailWord_2927072) baseStart_2927072 baseEnd_2927072 := by
    simpa [prefixWord, tailWord_2927072, baseEnd_2927072] using wordTrace_append hprefix tailTrace_2927072
  have hstable : (prefixWord ++ tailWord_2927072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927072).length < 2 ^ (prefixWord ++ tailWord_2927072).sum := by decide
  have hdescent : baseEnd_2927072 < baseStart_2927072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927110 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2927110 : Nat := 118140960795 + 2927110 * 2 ^ 59
def prefixEnd_2927110 : Nat := 4983230072969 + 3 ^ 40 * 2927110 * 2
def baseEnd_2927110 : Nat := 1503014358582147902363473

theorem tailTrace_2927110 : CollatzResearch.WordTrace tailWord_2927110 prefixEnd_2927110 1503014358582147902363473 := by
  unfold tailWord_2927110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3336264763299620482287337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71173648283725236955463189 3336264763299620482287337)
  ·
    refine ⟨2502198572474715361715503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3336264763299620482287337 2502198572474715361715503)
    ·
      refine ⟨3753297858712073042573255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2502198572474715361715503 3753297858712073042573255)
      ·
        refine ⟨5629946788068109563859883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3753297858712073042573255 5629946788068109563859883)
        ·
          refine ⟨8444920182102164345789825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5629946788068109563859883 8444920182102164345789825)
          ·
            refine ⟨6333690136576623259342369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8444920182102164345789825 6333690136576623259342369)
            ·
              refine ⟨4750267602432467444506777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6333690136576623259342369 4750267602432467444506777)
              ·
                refine ⟨3562700701824350583380083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4750267602432467444506777 3562700701824350583380083)
                ·
                  refine ⟨5344051052736525875070125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3562700701824350583380083 5344051052736525875070125)
                  ·
                    refine ⟨2004019144776197203151297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5344051052736525875070125 2004019144776197203151297)
                    ·
                      refine ⟨1503014358582147902363473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004019144776197203151297 1503014358582147902363473)
                      ·
                        rfl

theorem cell23_2927110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2927110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927110 prefixEnd_2927110 := by exact prefixLift 2927110
  have htrace : WordTrace (prefixWord ++ tailWord_2927110) baseStart_2927110 baseEnd_2927110 := by
    simpa [prefixWord, tailWord_2927110, baseEnd_2927110] using wordTrace_append hprefix tailTrace_2927110
  have hstable : (prefixWord ++ tailWord_2927110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927110).length < 2 ^ (prefixWord ++ tailWord_2927110).sum := by decide
  have hdescent : baseEnd_2927110 < baseStart_2927110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927125 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_2927125 : Nat := 118140960795 + 2927125 * 2 ^ 59
def prefixEnd_2927125 : Nat := 4983230072969 + 3 ^ 40 * 2927125 * 2
def baseEnd_2927125 : Nat := 501007353597321781225301

theorem tailTrace_2927125 : CollatzResearch.WordTrace tailWord_2927125 prefixEnd_2927125 501007353597321781225301 := by
  unfold tailWord_2927125
  simp only [CollatzResearch.WordTrace]
  refine ⟨106761019520533512994990829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71174013013689008663327219 106761019520533512994990829)
  ·
    refine ⟨40035382320200067373121561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106761019520533512994990829 40035382320200067373121561)
    ·
      refine ⟨30026536740150050529841171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40035382320200067373121561 30026536740150050529841171)
      ·
        refine ⟨45039805110225075794761757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30026536740150050529841171 45039805110225075794761757)
        ·
          refine ⟨16889926916334403423035659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45039805110225075794761757 16889926916334403423035659)
          ·
            refine ⟨25334890374501605134553489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16889926916334403423035659 25334890374501605134553489)
            ·
              refine ⟨19001167780876203850915117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25334890374501605134553489 19001167780876203850915117)
              ·
                refine ⟨7125437917828576444093169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19001167780876203850915117 7125437917828576444093169)
                ·
                  refine ⟨5344078438371432333069877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7125437917828576444093169 5344078438371432333069877)
                  ·
                    refine ⟨501007353597321781225301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5344078438371432333069877 501007353597321781225301)
                    ·
                      rfl

theorem cell23_2927125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_2927125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927125 prefixEnd_2927125 := by exact prefixLift 2927125
  have htrace : WordTrace (prefixWord ++ tailWord_2927125) baseStart_2927125 baseEnd_2927125 := by
    simpa [prefixWord, tailWord_2927125, baseEnd_2927125] using wordTrace_append hprefix tailTrace_2927125
  have hstable : (prefixWord ++ tailWord_2927125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927125).length < 2 ^ (prefixWord ++ tailWord_2927125).sum := by decide
  have hdescent : baseEnd_2927125 < baseStart_2927125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927182 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_2927182 : Nat := 118140960795 + 2927182 * 2 ^ 59
def prefixEnd_2927182 : Nat := 4983230072969 + 3 ^ 40 * 2927182 * 2
def baseEnd_2927182 : Nat := 1503051329189271620663141

theorem tailTrace_2927182 : CollatzResearch.WordTrace tailWord_2927182 prefixEnd_2927182 1503051329189271620663141 := by
  unfold tailWord_2927182
  simp only [CollatzResearch.WordTrace]
  refine ⟨13345387310165876466226975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71175398987551341153210533 13345387310165876466226975)
  ·
    refine ⟨20018080965248814699340463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13345387310165876466226975 20018080965248814699340463)
    ·
      refine ⟨30027121447873222049010695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20018080965248814699340463 30027121447873222049010695)
      ·
        refine ⟨45040682171809833073516043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30027121447873222049010695 45040682171809833073516043)
        ·
          refine ⟨67561023257714749610274065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45040682171809833073516043 67561023257714749610274065)
          ·
            refine ⟨50670767443286062207705549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67561023257714749610274065 50670767443286062207705549)
            ·
              refine ⟨19001537791232273327889581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50670767443286062207705549 19001537791232273327889581)
              ·
                refine ⟨7125576671712102497958593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19001537791232273327889581 7125576671712102497958593)
                ·
                  refine ⟨5344182503784076873468945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7125576671712102497958593 5344182503784076873468945)
                  ·
                    refine ⟨4008136877838057655101709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5344182503784076873468945 4008136877838057655101709)
                    ·
                      refine ⟨1503051329189271620663141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4008136877838057655101709 1503051329189271620663141)
                      ·
                        rfl

theorem cell23_2927182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_2927182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927182 prefixEnd_2927182 := by exact prefixLift 2927182
  have htrace : WordTrace (prefixWord ++ tailWord_2927182) baseStart_2927182 baseEnd_2927182 := by
    simpa [prefixWord, tailWord_2927182, baseEnd_2927182] using wordTrace_append hprefix tailTrace_2927182
  have hstable : (prefixWord ++ tailWord_2927182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927182).length < 2 ^ (prefixWord ++ tailWord_2927182).sum := by decide
  have hdescent : baseEnd_2927182 < baseStart_2927182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927215 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 3, 5]
def baseStart_2927215 : Nat := 118140960795 + 2927215 * 2 ^ 59
def prefixEnd_2927215 : Nat := 4983230072969 + 3 ^ 40 * 2927215 * 2
def baseEnd_2927215 : Nat := 501022758016956663850163

theorem tailTrace_2927215 : CollatzResearch.WordTrace tailWord_2927215 prefixEnd_2927215 501022758016956663850163 := by
  unfold tailWord_2927215
  simp only [CollatzResearch.WordTrace]
  refine ⟨106764302090207458365767099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71176201393471638910511399 106764302090207458365767099)
  ·
    refine ⟨160146453135311187548650649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106764302090207458365767099 160146453135311187548650649)
    ·
      refine ⟨120109839851483390661487987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160146453135311187548650649 120109839851483390661487987)
      ·
        refine ⟨180164759777225085992231981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120109839851483390661487987 180164759777225085992231981)
        ·
          refine ⟨67561784916459407247086993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180164759777225085992231981 67561784916459407247086993)
          ·
            refine ⟨50671338687344555435315245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67561784916459407247086993 50671338687344555435315245)
            ·
              refine ⟨19001752007754208288243217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50671338687344555435315245 19001752007754208288243217)
              ·
                refine ⟨14251314005815656216182413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19001752007754208288243217 14251314005815656216182413)
                ·
                  refine ⟨5344242752180871081068405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14251314005815656216182413 5344242752180871081068405)
                  ·
                    refine ⟨501022758016956663850163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5344242752180871081068405 501022758016956663850163)
                    ·
                      rfl

theorem cell23_2927215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_2927215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927215 prefixEnd_2927215 := by exact prefixLift 2927215
  have htrace : WordTrace (prefixWord ++ tailWord_2927215) baseStart_2927215 baseEnd_2927215 := by
    simpa [prefixWord, tailWord_2927215, baseEnd_2927215] using wordTrace_append hprefix tailTrace_2927215
  have hstable : (prefixWord ++ tailWord_2927215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927215).length < 2 ^ (prefixWord ++ tailWord_2927215).sum := by decide
  have hdescent : baseEnd_2927215 < baseStart_2927215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927297 : List Nat := [1, 2, 6, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2927297 : Nat := 118140960795 + 2927297 * 2 ^ 59
def prefixEnd_2927297 : Nat := 4983230072969 + 3 ^ 40 * 2927297 * 2
def baseEnd_2927297 : Nat := 1503110379464538670725113

theorem tailTrace_2927297 : CollatzResearch.WordTrace tailWord_2927297 prefixEnd_2927297 1503110379464538670725113 := by
  unfold tailWord_2927297
  simp only [CollatzResearch.WordTrace]
  refine ⟨106767292875910386370252145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71178195250606924246834763 106767292875910386370252145)
  ·
    refine ⟨80075469656932789777689109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106767292875910386370252145 80075469656932789777689109)
    ·
      refine ⟨3753537640168724520829177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80075469656932789777689109 3753537640168724520829177)
      ·
        refine ⟨2815153230126543390621883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3753537640168724520829177 2815153230126543390621883)
        ·
          refine ⟨4222729845189815085932825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815153230126543390621883 4222729845189815085932825)
          ·
            refine ⟨3167047383892361314449619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4222729845189815085932825 3167047383892361314449619)
            ·
              refine ⟨4750571075838541971674429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167047383892361314449619 4750571075838541971674429)
              ·
                refine ⟨1781464153439453239377911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4750571075838541971674429 1781464153439453239377911)
                ·
                  refine ⟨2672196230159179859066867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781464153439453239377911 2672196230159179859066867)
                  ·
                    refine ⟨4008294345238769788600301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2672196230159179859066867 4008294345238769788600301)
                    ·
                      refine ⟨1503110379464538670725113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4008294345238769788600301 1503110379464538670725113)
                      ·
                        rfl

theorem cell23_2927297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2927297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927297 prefixEnd_2927297 := by exact prefixLift 2927297
  have htrace : WordTrace (prefixWord ++ tailWord_2927297) baseStart_2927297 baseEnd_2927297 := by
    simpa [prefixWord, tailWord_2927297, baseEnd_2927297] using wordTrace_append hprefix tailTrace_2927297
  have hstable : (prefixWord ++ tailWord_2927297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927297).length < 2 ^ (prefixWord ++ tailWord_2927297).sum := by decide
  have hdescent : baseEnd_2927297 < baseStart_2927297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927312 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 1, 9, 2]
def baseStart_2927312 : Nat := 118140960795 + 2927312 * 2 ^ 59
def prefixEnd_2927312 : Nat := 4983230072969 + 3 ^ 40 * 2927312 * 2
def baseEnd_2927312 : Nat := 1503118081674356112037543

theorem tailTrace_2927312 : CollatzResearch.WordTrace tailWord_2927312 prefixEnd_2927312 1503118081674356112037543 := by
  unfold tailWord_2927312
  simp only [CollatzResearch.WordTrace]
  refine ⟨53383919985428021966024095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71178559980570695954698793 53383919985428021966024095)
  ·
    refine ⟨80075879978142032949036143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53383919985428021966024095 80075879978142032949036143)
    ·
      refine ⟨120113819967213049423554215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80075879978142032949036143 120113819967213049423554215)
      ·
        refine ⟨180170729950819574135331323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120113819967213049423554215 180170729950819574135331323)
        ·
          refine ⟨270256094926229361202996985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180170729950819574135331323 270256094926229361202996985)
          ·
            refine ⟨202692071194672020902247739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270256094926229361202996985 202692071194672020902247739)
            ·
              refine ⟨304038106792008031353371609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202692071194672020902247739 304038106792008031353371609)
              ·
                refine ⟨228028580094006023515028707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304038106792008031353371609 228028580094006023515028707)
                ·
                  refine ⟨342042870141009035272543061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228028580094006023515028707 342042870141009035272543061)
                  ·
                    refine ⟨2004157442232474816050057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 342042870141009035272543061 2004157442232474816050057)
                    ·
                      refine ⟨1503118081674356112037543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004157442232474816050057 1503118081674356112037543)
                      ·
                        rfl

theorem cell23_2927312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 9, 2].length) (baseStart_2927312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927312 prefixEnd_2927312 := by exact prefixLift 2927312
  have htrace : WordTrace (prefixWord ++ tailWord_2927312) baseStart_2927312 baseEnd_2927312 := by
    simpa [prefixWord, tailWord_2927312, baseEnd_2927312] using wordTrace_append hprefix tailTrace_2927312
  have hstable : (prefixWord ++ tailWord_2927312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927312).length < 2 ^ (prefixWord ++ tailWord_2927312).sum := by decide
  have hdescent : baseEnd_2927312 < baseStart_2927312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927319 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 4, 1, 3]
def baseStart_2927319 : Nat := 118140960795 + 2927319 * 2 ^ 59
def prefixEnd_2927319 : Nat := 4983230072969 + 3 ^ 40 * 2927319 * 2
def baseEnd_2927319 : Nat := 1503121676038937584650011

theorem tailTrace_2927319 : CollatzResearch.WordTrace tailWord_2927319 prefixEnd_2927319 1503121676038937584650011 := by
  unfold tailWord_2927319
  simp only [CollatzResearch.WordTrace]
  refine ⟨106768095281830684127553011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71178730187887122751702007 106768095281830684127553011)
  ·
    refine ⟨160152142922746026191329517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106768095281830684127553011 160152142922746026191329517)
    ·
      refine ⟨60057053596029759821748569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160152142922746026191329517 60057053596029759821748569)
      ·
        refine ⟨45042790197022319866311427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60057053596029759821748569 45042790197022319866311427)
        ·
          refine ⟨67564185295533479799467141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45042790197022319866311427 67564185295533479799467141)
          ·
            refine ⟨12668284742912527462400089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67564185295533479799467141 12668284742912527462400089)
            ·
              refine ⟨9501213557184395596800067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12668284742912527462400089 9501213557184395596800067)
              ·
                refine ⟨14251820335776593395200101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9501213557184395596800067 14251820335776593395200101)
                ·
                  refine ⟨2672216312958111261600019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14251820335776593395200101 2672216312958111261600019)
                  ·
                    refine ⟨4008324469437166892400029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2672216312958111261600019 4008324469437166892400029)
                    ·
                      refine ⟨1503121676038937584650011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4008324469437166892400029 1503121676038937584650011)
                      ·
                        rfl

theorem cell23_2927319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_2927319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927319 prefixEnd_2927319 := by exact prefixLift 2927319
  have htrace : WordTrace (prefixWord ++ tailWord_2927319) baseStart_2927319 baseEnd_2927319 := by
    simpa [prefixWord, tailWord_2927319, baseEnd_2927319] using wordTrace_append hprefix tailTrace_2927319
  have hstable : (prefixWord ++ tailWord_2927319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927319).length < 2 ^ (prefixWord ++ tailWord_2927319).sum := by decide
  have hdescent : baseEnd_2927319 < baseStart_2927319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927320 : List Nat := [2, 1, 2, 2, 3, 3, 3, 2, 1, 2, 2]
def baseStart_2927320 : Nat := 118140960795 + 2927320 * 2 ^ 59
def prefixEnd_2927320 : Nat := 4983230072969 + 3 ^ 40 * 2927320 * 2
def baseEnd_2927320 : Nat := 1503122189519592080737507

theorem tailTrace_2927320 : CollatzResearch.WordTrace tailWord_2927320 prefixEnd_2927320 1503122189519592080737507 := by
  unfold tailWord_2927320
  simp only [CollatzResearch.WordTrace]
  refine ⟨53384065877413530649169707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71178754503218040865559609 53384065877413530649169707)
  ·
    refine ⟨80076098816120295973754561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53384065877413530649169707 80076098816120295973754561)
    ·
      refine ⟨60057074112090221980315921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80076098816120295973754561 60057074112090221980315921)
      ·
        refine ⟨45042805584067666485236941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60057074112090221980315921 45042805584067666485236941)
        ·
          refine ⟨16891052094025374931963853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45042805584067666485236941 16891052094025374931963853)
          ·
            refine ⟨6334144535259515599486445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16891052094025374931963853 6334144535259515599486445)
            ·
              refine ⟨2375304200722318349807417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6334144535259515599486445 2375304200722318349807417)
              ·
                refine ⟨1781478150541738762355563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2375304200722318349807417 1781478150541738762355563)
                ·
                  refine ⟨2672217225812608143533345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781478150541738762355563 2672217225812608143533345)
                  ·
                    refine ⟨2004162919359456107650009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2672217225812608143533345 2004162919359456107650009)
                    ·
                      refine ⟨1503122189519592080737507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004162919359456107650009 1503122189519592080737507)
                      ·
                        rfl

theorem cell23_2927320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_2927320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927320 prefixEnd_2927320 := by exact prefixLift 2927320
  have htrace : WordTrace (prefixWord ++ tailWord_2927320) baseStart_2927320 baseEnd_2927320 := by
    simpa [prefixWord, tailWord_2927320, baseEnd_2927320] using wordTrace_append hprefix tailTrace_2927320
  have hstable : (prefixWord ++ tailWord_2927320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927320).length < 2 ^ (prefixWord ++ tailWord_2927320).sum := by decide
  have hdescent : baseEnd_2927320 < baseStart_2927320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927346 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 3, 3, 2]
def baseStart_2927346 : Nat := 118140960795 + 2927346 * 2 ^ 59
def prefixEnd_2927346 : Nat := 4983230072969 + 3 ^ 40 * 2927346 * 2
def baseEnd_2927346 : Nat := 1503135540016608979012387

theorem tailTrace_2927346 : CollatzResearch.WordTrace tailWord_2927346 prefixEnd_2927346 1503135540016608979012387 := by
  unfold tailWord_2927346
  simp only [CollatzResearch.WordTrace]
  refine ⟨26692270013183216934696473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71179386701821911825857261 26692270013183216934696473)
  ·
    refine ⟨20019202509887412701022355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26692270013183216934696473 20019202509887412701022355)
    ·
      refine ⟨30028803764831119051533533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20019202509887412701022355 30028803764831119051533533)
      ·
        refine ⟨11260801411811669644325075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30028803764831119051533533 11260801411811669644325075)
        ·
          refine ⟨16891202117717504466487613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11260801411811669644325075 16891202117717504466487613)
          ·
            refine ⟨6334200794144064174932855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16891202117717504466487613 6334200794144064174932855)
            ·
              refine ⟨9501301191216096262399283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6334200794144064174932855 9501301191216096262399283)
              ·
                refine ⟨14251951786824144393598925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9501301191216096262399283 14251951786824144393598925)
                ·
                  refine ⟨5344481920059054147599597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14251951786824144393598925 5344481920059054147599597)
                  ·
                    refine ⟨2004180720022145305349849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5344481920059054147599597 2004180720022145305349849)
                    ·
                      refine ⟨1503135540016608979012387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004180720022145305349849 1503135540016608979012387)
                      ·
                        rfl

theorem cell23_2927346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_2927346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927346 prefixEnd_2927346 := by exact prefixLift 2927346
  have htrace : WordTrace (prefixWord ++ tailWord_2927346) baseStart_2927346 baseEnd_2927346 := by
    simpa [prefixWord, tailWord_2927346, baseEnd_2927346] using wordTrace_append hprefix tailTrace_2927346
  have hstable : (prefixWord ++ tailWord_2927346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927346).length < 2 ^ (prefixWord ++ tailWord_2927346).sum := by decide
  have hdescent : baseEnd_2927346 < baseStart_2927346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927355 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 6]
def baseStart_2927355 : Nat := 118140960795 + 2927355 * 2 ^ 59
def prefixEnd_2927355 : Nat := 4983230072969 + 3 ^ 40 * 2927355 * 2
def baseEnd_2927355 : Nat := 1503140161342499443799845

theorem tailTrace_2927355 : CollatzResearch.WordTrace tailWord_2927355 prefixEnd_2927355 1503140161342499443799845 := by
  unfold tailWord_2927355
  simp only [CollatzResearch.WordTrace]
  refine ⟨106769408309700262275863519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71179605539800174850575679 106769408309700262275863519)
  ·
    refine ⟨160154112464550393413795279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106769408309700262275863519 160154112464550393413795279)
    ·
      refine ⟨240231168696825590120692919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160154112464550393413795279 240231168696825590120692919)
      ·
        refine ⟨360346753045238385181039379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240231168696825590120692919 360346753045238385181039379)
        ·
          refine ⟨540520129567857577771559069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360346753045238385181039379 540520129567857577771559069)
          ·
            refine ⟨202695048587946591664334651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 540520129567857577771559069 202695048587946591664334651)
            ·
              refine ⟨304042572881919887496501977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202695048587946591664334651 304042572881919887496501977)
              ·
                refine ⟨228031929661439915622376483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304042572881919887496501977 228031929661439915622376483)
                ·
                  refine ⟨342047894492159873433564725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228031929661439915622376483 342047894492159873433564725)
                  ·
                    refine ⟨32066990108639988134396693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 342047894492159873433564725 32066990108639988134396693)
                    ·
                      refine ⟨1503140161342499443799845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32066990108639988134396693 1503140161342499443799845)
                      ·
                        rfl

theorem cell23_2927355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_2927355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927355 prefixEnd_2927355 := by exact prefixLift 2927355
  have htrace : WordTrace (prefixWord ++ tailWord_2927355) baseStart_2927355 baseEnd_2927355 := by
    simpa [prefixWord, tailWord_2927355, baseEnd_2927355] using wordTrace_append hprefix tailTrace_2927355
  have hstable : (prefixWord ++ tailWord_2927355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927355).length < 2 ^ (prefixWord ++ tailWord_2927355).sum := by decide
  have hdescent : baseEnd_2927355 < baseStart_2927355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927372 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_2927372 : Nat := 118140960795 + 2927372 * 2 ^ 59
def prefixEnd_2927372 : Nat := 4983230072969 + 3 ^ 40 * 2927372 * 2
def baseEnd_2927372 : Nat := 1503148890513625877287267

theorem tailTrace_2927372 : CollatzResearch.WordTrace tailWord_2927372 prefixEnd_2927372 1503148890513625877287267 := by
  unfold tailWord_2927372
  simp only [CollatzResearch.WordTrace]
  refine ⟨53385014175319337089616185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71180018900425782786154913 53385014175319337089616185)
  ·
    refine ⟨40038760631489502817212139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53385014175319337089616185 40038760631489502817212139)
    ·
      refine ⟨60058140947234254225818209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40038760631489502817212139 60058140947234254225818209)
      ·
        refine ⟨45043605710425690669363657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60058140947234254225818209 45043605710425690669363657)
        ·
          refine ⟨33782704282819268002022743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45043605710425690669363657 33782704282819268002022743)
          ·
            refine ⟨50674056424228902003034115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33782704282819268002022743 50674056424228902003034115)
            ·
              refine ⟨76011084636343353004551173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50674056424228902003034115 76011084636343353004551173)
              ·
                refine ⟨14252078369314378688353345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76011084636343353004551173 14252078369314378688353345)
                ·
                  refine ⟨10689058776985784016265009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14252078369314378688353345 10689058776985784016265009)
                  ·
                    refine ⟨8016794082739338012198757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10689058776985784016265009 8016794082739338012198757)
                    ·
                      refine ⟨1503148890513625877287267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8016794082739338012198757 1503148890513625877287267)
                      ·
                        rfl

theorem cell23_2927372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_2927372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927372 prefixEnd_2927372 := by exact prefixLift 2927372
  have htrace : WordTrace (prefixWord ++ tailWord_2927372) baseStart_2927372 baseEnd_2927372 := by
    simpa [prefixWord, tailWord_2927372, baseEnd_2927372] using wordTrace_append hprefix tailTrace_2927372
  have hstable : (prefixWord ++ tailWord_2927372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927372).length < 2 ^ (prefixWord ++ tailWord_2927372).sum := by decide
  have hdescent : baseEnd_2927372 < baseStart_2927372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927414 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_2927414 : Nat := 118140960795 + 2927414 * 2 ^ 59
def prefixEnd_2927414 : Nat := 4983230072969 + 3 ^ 40 * 2927414 * 2
def baseEnd_2927414 : Nat := 1503170456701114712962075

theorem tailTrace_2927414 : CollatzResearch.WordTrace tailWord_2927414 prefixEnd_2927414 1503170456701114712962075 := by
  unfold tailWord_2927414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6673222513530407209516331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71181040144324343568174197 6673222513530407209516331)
  ·
    refine ⟨10009833770295610814274497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6673222513530407209516331 10009833770295610814274497)
    ·
      refine ⟨7507375327721708110705873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10009833770295610814274497 7507375327721708110705873)
      ·
        refine ⟨5630531495791281083029405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7507375327721708110705873 5630531495791281083029405)
        ·
          refine ⟨2111449310921730406136027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5630531495791281083029405 2111449310921730406136027)
          ·
            refine ⟨3167173966382595609204041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111449310921730406136027 3167173966382595609204041)
            ·
              refine ⟨2375380474786946706903031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3167173966382595609204041 2375380474786946706903031)
              ·
                refine ⟨3563070712180420060354547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375380474786946706903031 3563070712180420060354547)
                ·
                  refine ⟨5344606068270630090531821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563070712180420060354547 5344606068270630090531821)
                  ·
                    refine ⟨2004227275601486283949433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5344606068270630090531821 2004227275601486283949433)
                    ·
                      refine ⟨1503170456701114712962075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004227275601486283949433 1503170456701114712962075)
                      ·
                        rfl

theorem cell23_2927414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_2927414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927414 prefixEnd_2927414 := by exact prefixLift 2927414
  have htrace : WordTrace (prefixWord ++ tailWord_2927414) baseStart_2927414 baseEnd_2927414 := by
    simpa [prefixWord, tailWord_2927414, baseEnd_2927414] using wordTrace_append hprefix tailTrace_2927414
  have hstable : (prefixWord ++ tailWord_2927414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927414).length < 2 ^ (prefixWord ++ tailWord_2927414).sum := by decide
  have hdescent : baseEnd_2927414 < baseStart_2927414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927472 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 8]
def baseStart_2927472 : Nat := 118140960795 + 2927472 * 2 ^ 59
def prefixEnd_2927472 : Nat := 4983230072969 + 3 ^ 40 * 2927472 * 2
def baseEnd_2927472 : Nat := 167022248731008387337423

theorem tailTrace_2927472 : CollatzResearch.WordTrace tailWord_2927472 prefixEnd_2927472 167022248731008387337423 := by
  unfold tailWord_2927472
  simp only [CollatzResearch.WordTrace]
  refine ⟨53386837825138195628936335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71182450433517594171915113 53386837825138195628936335)
  ·
    refine ⟨80080256737707293443404503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53386837825138195628936335 80080256737707293443404503)
    ·
      refine ⟨120120385106560940165106755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80080256737707293443404503 120120385106560940165106755)
      ·
        refine ⟨180180577659841410247660133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120120385106560940165106755 180180577659841410247660133)
        ·
          refine ⟨33783858311220264421436275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180180577659841410247660133 33783858311220264421436275)
          ·
            refine ⟨50675787466830396632154413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33783858311220264421436275 50675787466830396632154413)
            ·
              refine ⟨19003420300061398737057905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50675787466830396632154413 19003420300061398737057905)
              ·
                refine ⟨14252565225046049052793429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19003420300061398737057905 14252565225046049052793429)
                ·
                  refine ⟨167022248731008387337423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14252565225046049052793429 167022248731008387337423)
                  ·
                    rfl

theorem cell23_2927472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 8].length) (baseStart_2927472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927472 prefixEnd_2927472 := by exact prefixLift 2927472
  have htrace : WordTrace (prefixWord ++ tailWord_2927472) baseStart_2927472 baseEnd_2927472 := by
    simpa [prefixWord, tailWord_2927472, baseEnd_2927472] using wordTrace_append hprefix tailTrace_2927472
  have hstable : (prefixWord ++ tailWord_2927472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927472).length < 2 ^ (prefixWord ++ tailWord_2927472).sum := by decide
  have hdescent : baseEnd_2927472 < baseStart_2927472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927550 : List Nat := [4, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_2927550 : Nat := 118140960795 + 2927550 * 2 ^ 59
def prefixEnd_2927550 : Nat := 4983230072969 + 3 ^ 40 * 2927550 * 2
def baseEnd_2927550 : Nat := 1503240290070126180861449

theorem tailTrace_2927550 : CollatzResearch.WordTrace tailWord_2927550 prefixEnd_2927550 1503240290070126180861449 := by
  unfold tailWord_2927550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13347065067999226322401513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71184347029329207052808069 13347065067999226322401513)
  ·
    refine ⟨10010298800999419741801135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13347065067999226322401513 10010298800999419741801135)
    ·
      refine ⟨15015448201499129612701703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10010298800999419741801135 15015448201499129612701703)
      ·
        refine ⟨22523172302248694419052555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15015448201499129612701703 22523172302248694419052555)
        ·
          refine ⟨33784758453373041628578833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22523172302248694419052555 33784758453373041628578833)
          ·
            refine ⟨25338568840029781221434125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33784758453373041628578833 25338568840029781221434125)
            ·
              refine ⟨9501963315011167958037797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25338568840029781221434125 9501963315011167958037797)
              ·
                refine ⟨1781618121564593992132087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9501963315011167958037797 1781618121564593992132087)
                ·
                  refine ⟨2672427182346890988198131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781618121564593992132087 2672427182346890988198131)
                  ·
                    refine ⟨4008640773520336482297197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2672427182346890988198131 4008640773520336482297197)
                    ·
                      refine ⟨1503240290070126180861449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4008640773520336482297197 1503240290070126180861449)
                      ·
                        rfl

theorem cell23_2927550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_2927550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927550 prefixEnd_2927550 := by exact prefixLift 2927550
  have htrace : WordTrace (prefixWord ++ tailWord_2927550) baseStart_2927550 baseEnd_2927550 := by
    simpa [prefixWord, tailWord_2927550, baseEnd_2927550] using wordTrace_append hprefix tailTrace_2927550
  have hstable : (prefixWord ++ tailWord_2927550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927550).length < 2 ^ (prefixWord ++ tailWord_2927550).sum := by decide
  have hdescent : baseEnd_2927550 < baseStart_2927550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927559 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_2927559 : Nat := 118140960795 + 2927559 * 2 ^ 59
def prefixEnd_2927559 : Nat := 4983230072969 + 3 ^ 40 * 2927559 * 2
def baseEnd_2927559 : Nat := 1503244911396016645648907

theorem tailTrace_2927559 : CollatzResearch.WordTrace tailWord_2927559 prefixEnd_2927559 1503244911396016645648907 := by
  unfold tailWord_2927559
  simp only [CollatzResearch.WordTrace]
  refine ⟨106776848800961205116289731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71184565867307470077526487 106776848800961205116289731)
  ·
    refine ⟨160165273201441807674434597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106776848800961205116289731 160165273201441807674434597)
    ·
      refine ⟨30030988725270338938956487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160165273201441807674434597 30030988725270338938956487)
      ·
        refine ⟨45046483087905508408434731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30030988725270338938956487 45046483087905508408434731)
        ·
          refine ⟨67569724631858262612652097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45046483087905508408434731 67569724631858262612652097)
          ·
            refine ⟨50677293473893696959489073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67569724631858262612652097 50677293473893696959489073)
            ·
              refine ⟨38007970105420272719616805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50677293473893696959489073 38007970105420272719616805)
              ·
                refine ⟨7126494394766301134928151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38007970105420272719616805 7126494394766301134928151)
                ·
                  refine ⟨10689741592149451702392227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7126494394766301134928151 10689741592149451702392227)
                  ·
                    refine ⟨16034612388224177553588341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10689741592149451702392227 16034612388224177553588341)
                    ·
                      refine ⟨1503244911396016645648907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16034612388224177553588341 1503244911396016645648907)
                      ·
                        rfl

theorem cell23_2927559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_2927559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927559 prefixEnd_2927559 := by exact prefixLift 2927559
  have htrace : WordTrace (prefixWord ++ tailWord_2927559) baseStart_2927559 baseEnd_2927559 := by
    simpa [prefixWord, tailWord_2927559, baseEnd_2927559] using wordTrace_append hprefix tailTrace_2927559
  have hstable : (prefixWord ++ tailWord_2927559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927559).length < 2 ^ (prefixWord ++ tailWord_2927559).sum := by decide
  have hdescent : baseEnd_2927559 < baseStart_2927559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927566 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_2927566 : Nat := 118140960795 + 2927566 * 2 ^ 59
def prefixEnd_2927566 : Nat := 4983230072969 + 3 ^ 40 * 2927566 * 2
def baseEnd_2927566 : Nat := 501082835253532706087125

theorem tailTrace_2927566 : CollatzResearch.WordTrace tailWord_2927566 prefixEnd_2927566 501082835253532706087125 := by
  unfold tailWord_2927566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13347138013991980663974319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71184736074623896874529701 13347138013991980663974319)
  ·
    refine ⟨20020707020987970995961479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13347138013991980663974319 20020707020987970995961479)
    ·
      refine ⟨30031060531481956493942219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20020707020987970995961479 30031060531481956493942219)
      ·
        refine ⟨45046590797222934740913329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30031060531481956493942219 45046590797222934740913329)
        ·
          refine ⟨33784943097917201055684997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45046590797222934740913329 33784943097917201055684997)
          ·
            refine ⟨6334676830859475197940937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33784943097917201055684997 6334676830859475197940937)
            ·
              refine ⟨4751007623144606398455703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6334676830859475197940937 4751007623144606398455703)
              ·
                refine ⟨7126511434716909597683555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751007623144606398455703 7126511434716909597683555)
                ·
                  refine ⟨10689767152075364396525333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7126511434716909597683555 10689767152075364396525333)
                  ·
                    refine ⟨501082835253532706087125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10689767152075364396525333 501082835253532706087125)
                    ·
                      rfl

theorem cell23_2927566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_2927566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927566 prefixEnd_2927566 := by exact prefixLift 2927566
  have htrace : WordTrace (prefixWord ++ tailWord_2927566) baseStart_2927566 baseEnd_2927566 := by
    simpa [prefixWord, tailWord_2927566, baseEnd_2927566] using wordTrace_append hprefix tailTrace_2927566
  have hstable : (prefixWord ++ tailWord_2927566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927566).length < 2 ^ (prefixWord ++ tailWord_2927566).sum := by decide
  have hdescent : baseEnd_2927566 < baseStart_2927566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927576 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 3, 2, 3]
def baseStart_2927576 : Nat := 118140960795 + 2927576 * 2 ^ 59
def prefixEnd_2927576 : Nat := 4983230072969 + 3 ^ 40 * 2927576 * 2
def baseEnd_2927576 : Nat := 1503253640567143079136329

theorem tailTrace_2927576 : CollatzResearch.WordTrace tailWord_2927576 prefixEnd_2927576 1503253640567143079136329 := by
  unfold tailWord_2927576
  simp only [CollatzResearch.WordTrace]
  refine ⟨53388734420949808509829291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71184979227933078013105721 53388734420949808509829291)
  ·
    refine ⟨80083101631424712764743937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53388734420949808509829291 80083101631424712764743937)
    ·
      refine ⟨60062326223568534573557953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80083101631424712764743937 60062326223568534573557953)
      ·
        refine ⟨45046744667676400930168465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60062326223568534573557953 45046744667676400930168465)
        ·
          refine ⟨33785058500757300697626349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45046744667676400930168465 33785058500757300697626349)
          ·
            refine ⟨12669396937783987761609881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33785058500757300697626349 12669396937783987761609881)
            ·
              refine ⟨9502047703337990821207411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12669396937783987761609881 9502047703337990821207411)
              ·
                refine ⟨14253071555006986231811117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9502047703337990821207411 14253071555006986231811117)
                ·
                  refine ⟨5344901833127619836929169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14253071555006986231811117 5344901833127619836929169)
                  ·
                    refine ⟨4008676374845714877696877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5344901833127619836929169 4008676374845714877696877)
                    ·
                      refine ⟨1503253640567143079136329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4008676374845714877696877 1503253640567143079136329)
                      ·
                        rfl

theorem cell23_2927576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_2927576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927576 prefixEnd_2927576 := by exact prefixLift 2927576
  have htrace : WordTrace (prefixWord ++ tailWord_2927576) baseStart_2927576 baseEnd_2927576 := by
    simpa [prefixWord, tailWord_2927576, baseEnd_2927576] using wordTrace_append hprefix tailTrace_2927576
  have hstable : (prefixWord ++ tailWord_2927576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927576).length < 2 ^ (prefixWord ++ tailWord_2927576).sum := by decide
  have hdescent : baseEnd_2927576 < baseStart_2927576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927650 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_2927650 : Nat := 118140960795 + 2927650 * 2 ^ 59
def prefixEnd_2927650 : Nat := 4983230072969 + 3 ^ 40 * 2927650 * 2
def baseEnd_2927650 : Nat := 1503291638135575789610989

theorem tailTrace_2927650 : CollatzResearch.WordTrace tailWord_2927650 prefixEnd_2927650 1503291638135575789610989 := by
  unfold tailWord_2927650
  simp only [CollatzResearch.WordTrace]
  refine ⟨26695041960907881914463101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71186778562421018438568269 26695041960907881914463101)
  ·
    refine ⟨10010640735340455717923663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26695041960907881914463101 10010640735340455717923663)
    ·
      refine ⟨15015961103010683576885495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10010640735340455717923663 15015961103010683576885495)
      ·
        refine ⟨22523941654516025365328243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15015961103010683576885495 22523941654516025365328243)
        ·
          refine ⟨33785912481774038047992365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22523941654516025365328243 33785912481774038047992365)
          ·
            refine ⟨12669717180665264267997137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33785912481774038047992365 12669717180665264267997137)
            ·
              refine ⟨9502287885498948200997853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12669717180665264267997137 9502287885498948200997853)
              ·
                refine ⟨3563357957062105575374195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9502287885498948200997853 3563357957062105575374195)
                ·
                  refine ⟨5345036935593158363061293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563357957062105575374195 5345036935593158363061293)
                  ·
                    refine ⟨2004388850847434386147985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5345036935593158363061293 2004388850847434386147985)
                    ·
                      refine ⟨1503291638135575789610989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004388850847434386147985 1503291638135575789610989)
                      ·
                        rfl

theorem cell23_2927650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_2927650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927650 prefixEnd_2927650 := by exact prefixLift 2927650
  have htrace : WordTrace (prefixWord ++ tailWord_2927650) baseStart_2927650 baseEnd_2927650 := by
    simpa [prefixWord, tailWord_2927650, baseEnd_2927650] using wordTrace_append hprefix tailTrace_2927650
  have hstable : (prefixWord ++ tailWord_2927650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927650).length < 2 ^ (prefixWord ++ tailWord_2927650).sum := by decide
  have hdescent : baseEnd_2927650 < baseStart_2927650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927666 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_2927666 : Nat := 118140960795 + 2927666 * 2 ^ 59
def prefixEnd_2927666 : Nat := 4983230072969 + 3 ^ 40 * 2927666 * 2
def baseEnd_2927666 : Nat := 1503299853826047727010915

theorem tailTrace_2927666 : CollatzResearch.WordTrace tailWord_2927666 prefixEnd_2927666 1503299853826047727010915 := by
  unfold tailWord_2927666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26695187852893390597608713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71187167607715708260289901 26695187852893390597608713)
  ·
    refine ⟨20021390889670042948206535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26695187852893390597608713 20021390889670042948206535)
    ·
      refine ⟨30032086334505064422309803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20021390889670042948206535 30032086334505064422309803)
      ·
        refine ⟨45048129501757596633464705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30032086334505064422309803 45048129501757596633464705)
        ·
          refine ⟨33786097126318197475098529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45048129501757596633464705 33786097126318197475098529)
          ·
            refine ⟨25339572844738648106323897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33786097126318197475098529 25339572844738648106323897)
            ·
              refine ⟨19004679633553986079742923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25339572844738648106323897 19004679633553986079742923)
              ·
                refine ⟨28507019450330979119614385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19004679633553986079742923 28507019450330979119614385)
                ·
                  refine ⟨21380264587748234339710789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28507019450330979119614385 21380264587748234339710789)
                  ·
                    refine ⟨4008799610202793938695773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21380264587748234339710789 4008799610202793938695773)
                    ·
                      refine ⟨1503299853826047727010915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4008799610202793938695773 1503299853826047727010915)
                      ·
                        rfl

theorem cell23_2927666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_2927666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927666 prefixEnd_2927666 := by exact prefixLift 2927666
  have htrace : WordTrace (prefixWord ++ tailWord_2927666) baseStart_2927666 baseEnd_2927666 := by
    simpa [prefixWord, tailWord_2927666, baseEnd_2927666] using wordTrace_append hprefix tailTrace_2927666
  have hstable : (prefixWord ++ tailWord_2927666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927666).length < 2 ^ (prefixWord ++ tailWord_2927666).sum := by decide
  have hdescent : baseEnd_2927666 < baseStart_2927666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927680 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 2, 2, 2]
def baseStart_2927680 : Nat := 118140960795 + 2927680 * 2 ^ 59
def prefixEnd_2927680 : Nat := 4983230072969 + 3 ^ 40 * 2927680 * 2
def baseEnd_2927680 : Nat := 1503307042555210672235851

theorem tailTrace_2927680 : CollatzResearch.WordTrace tailWord_2927680 prefixEnd_2927680 1503307042555210672235851 := by
  unfold tailWord_2927680
  simp only [CollatzResearch.WordTrace]
  refine ⟨53390631016761421390722247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71187508022348561854296329 53390631016761421390722247)
  ·
    refine ⟨80085946525142132086083371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53390631016761421390722247 80085946525142132086083371)
    ·
      refine ⟨120128919787713198129125057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80085946525142132086083371 120128919787713198129125057)
      ·
        refine ⟨90096689840784898596843793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120128919787713198129125057 90096689840784898596843793)
        ·
          refine ⟨67572517380588673947632845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90096689840784898596843793 67572517380588673947632845)
          ·
            refine ⟨25339694017720752730362317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67572517380588673947632845 25339694017720752730362317)
            ·
              refine ⟨9502385256645282273885869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25339694017720752730362317 9502385256645282273885869)
              ·
                refine ⟨3563394471241980852707201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9502385256645282273885869 3563394471241980852707201)
                ·
                  refine ⟨2672545853431485639530401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3563394471241980852707201 2672545853431485639530401)
                  ·
                    refine ⟨2004409390073614229647801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2672545853431485639530401 2004409390073614229647801)
                    ·
                      refine ⟨1503307042555210672235851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004409390073614229647801 1503307042555210672235851)
                      ·
                        rfl

theorem cell23_2927680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2, 2, 2].length) (baseStart_2927680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927680 prefixEnd_2927680 := by exact prefixLift 2927680
  have htrace : WordTrace (prefixWord ++ tailWord_2927680) baseStart_2927680 baseEnd_2927680 := by
    simpa [prefixWord, tailWord_2927680, baseEnd_2927680] using wordTrace_append hprefix tailTrace_2927680
  have hstable : (prefixWord ++ tailWord_2927680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927680).length < 2 ^ (prefixWord ++ tailWord_2927680).sum := by decide
  have hdescent : baseEnd_2927680 < baseStart_2927680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927714 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_2927714 : Nat := 118140960795 + 2927714 * 2 ^ 59
def prefixEnd_2927714 : Nat := 4983230072969 + 3 ^ 40 * 2927714 * 2
def baseEnd_2927714 : Nat := 1503324500897463539210695

theorem tailTrace_2927714 : CollatzResearch.WordTrace tailWord_2927714 prefixEnd_2927714 1503324500897463539210695 := by
  unfold tailWord_2927714
  simp only [CollatzResearch.WordTrace]
  refine ⟨26695625528849916647045549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71188334743599777725454797 26695625528849916647045549)
  ·
    refine ⟨10010859573318718742642081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26695625528849916647045549 10010859573318718742642081)
    ·
      refine ⟨7508144679989039056981561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10010859573318718742642081 7508144679989039056981561)
      ·
        refine ⟨5631108509991779292736171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7508144679989039056981561 5631108509991779292736171)
        ·
          refine ⟨8446662764987668939104257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631108509991779292736171 8446662764987668939104257)
          ·
            refine ⟨6334997073740751704328193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8446662764987668939104257 6334997073740751704328193)
            ·
              refine ⟨4751247805305563778246145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6334997073740751704328193 4751247805305563778246145)
              ·
                refine ⟨3563435853979172833684609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4751247805305563778246145 3563435853979172833684609)
                ·
                  refine ⟨2672576890484379625263457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3563435853979172833684609 2672576890484379625263457)
                  ·
                    refine ⟨2004432667863284718947593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2672576890484379625263457 2004432667863284718947593)
                    ·
                      refine ⟨1503324500897463539210695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004432667863284718947593 1503324500897463539210695)
                      ·
                        rfl

theorem cell23_2927714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_2927714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927714 prefixEnd_2927714 := by exact prefixLift 2927714
  have htrace : WordTrace (prefixWord ++ tailWord_2927714) baseStart_2927714 baseEnd_2927714 := by
    simpa [prefixWord, tailWord_2927714, baseEnd_2927714] using wordTrace_append hprefix tailTrace_2927714
  have hstable : (prefixWord ++ tailWord_2927714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927714).length < 2 ^ (prefixWord ++ tailWord_2927714).sum := by decide
  have hdescent : baseEnd_2927714 < baseStart_2927714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927736 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_2927736 : Nat := 118140960795 + 2927736 * 2 ^ 59
def prefixEnd_2927736 : Nat := 4983230072969 + 3 ^ 40 * 2927736 * 2
def baseEnd_2927736 : Nat := 1503335797471862453135593

theorem tailTrace_2927736 : CollatzResearch.WordTrace tailWord_2927736 prefixEnd_2927736 1503335797471862453135593 := by
  unfold tailWord_2927736
  simp only [CollatzResearch.WordTrace]
  refine ⟨53391652260659982172741531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71188869680879976230322041 53391652260659982172741531)
  ·
    refine ⟨80087478390989973259112297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53391652260659982172741531 80087478390989973259112297)
    ·
      refine ⟨60065608793242479944334223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80087478390989973259112297 60065608793242479944334223)
      ·
        refine ⟨90098413189863719916501335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60065608793242479944334223 90098413189863719916501335)
        ·
          refine ⟨135147619784795579874752003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90098413189863719916501335 135147619784795579874752003)
          ·
            refine ⟨202721429677193369812128005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135147619784795579874752003 202721429677193369812128005)
            ·
              refine ⟨38010268064473756839774001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202721429677193369812128005 38010268064473756839774001)
              ·
                refine ⟨28507701048355317629830501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38010268064473756839774001 28507701048355317629830501)
                ·
                  refine ⟨5345193946566622055593219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28507701048355317629830501 5345193946566622055593219)
                  ·
                    refine ⟨8017790919849933083389829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5345193946566622055593219 8017790919849933083389829)
                    ·
                      refine ⟨1503335797471862453135593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8017790919849933083389829 1503335797471862453135593)
                      ·
                        rfl

theorem cell23_2927736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_2927736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927736 prefixEnd_2927736 := by exact prefixLift 2927736
  have htrace : WordTrace (prefixWord ++ tailWord_2927736) baseStart_2927736 baseEnd_2927736 := by
    simpa [prefixWord, tailWord_2927736, baseEnd_2927736] using wordTrace_append hprefix tailTrace_2927736
  have hstable : (prefixWord ++ tailWord_2927736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927736).length < 2 ^ (prefixWord ++ tailWord_2927736).sum := by decide
  have hdescent : baseEnd_2927736 < baseStart_2927736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927753 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 4]
def baseStart_2927753 : Nat := 118140960795 + 2927753 * 2 ^ 59
def prefixEnd_2927753 : Nat := 4983230072969 + 3 ^ 40 * 2927753 * 2
def baseEnd_2927753 : Nat := 1503344526642988886623015

theorem tailTrace_2927753 : CollatzResearch.WordTrace tailWord_2927753 prefixEnd_2927753 1503344526642988886623015 := by
  unfold tailWord_2927753
  simp only [CollatzResearch.WordTrace]
  refine ⟨106783924562258376248851913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71189283041505584165901275 106783924562258376248851913)
  ·
    refine ⟨80087943421693782186638935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106783924562258376248851913 80087943421693782186638935)
    ·
      refine ⟨120131915132540673279958403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80087943421693782186638935 120131915132540673279958403)
      ·
        refine ⟨180197872698811009919937605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120131915132540673279958403 180197872698811009919937605)
        ·
          refine ⟨33787101131027064359988301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180197872698811009919937605 33787101131027064359988301)
          ·
            refine ⟨12670162924135149134995613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33787101131027064359988301 12670162924135149134995613)
            ·
              refine ⟨4751311096550680925623355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12670162924135149134995613 4751311096550680925623355)
              ·
                refine ⟨7126966644826021388435033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751311096550680925623355 7126966644826021388435033)
                ·
                  refine ⟨5345224983619516041326275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7126966644826021388435033 5345224983619516041326275)
                  ·
                    refine ⟨8017837475429274061989413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5345224983619516041326275 8017837475429274061989413)
                    ·
                      refine ⟨1503344526642988886623015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8017837475429274061989413 1503344526642988886623015)
                      ·
                        rfl

theorem cell23_2927753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 4].length) (baseStart_2927753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927753 prefixEnd_2927753 := by exact prefixLift 2927753
  have htrace : WordTrace (prefixWord ++ tailWord_2927753) baseStart_2927753 baseEnd_2927753 := by
    simpa [prefixWord, tailWord_2927753, baseEnd_2927753] using wordTrace_append hprefix tailTrace_2927753
  have hstable : (prefixWord ++ tailWord_2927753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927753).length < 2 ^ (prefixWord ++ tailWord_2927753).sum := by decide
  have hdescent : baseEnd_2927753 < baseStart_2927753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927770 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2]
def baseStart_2927770 : Nat := 118140960795 + 2927770 * 2 ^ 59
def prefixEnd_2927770 : Nat := 4983230072969 + 3 ^ 40 * 2927770 * 2
def baseEnd_2927770 : Nat := 1503353255814115320110437

theorem tailTrace_2927770 : CollatzResearch.WordTrace tailWord_2927770 prefixEnd_2927770 1503353255814115320110437 := by
  unfold tailWord_2927770
  simp only [CollatzResearch.WordTrace]
  refine ⟨26696136150799197038055191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71189696402131192101480509 26696136150799197038055191)
  ·
    refine ⟨40044204226198795557082787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26696136150799197038055191 40044204226198795557082787)
    ·
      refine ⟨60066306339298193335624181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40044204226198795557082787 60066306339298193335624181)
      ·
        refine ⟨5631216219309205625214767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60066306339298193335624181 5631216219309205625214767)
        ·
          refine ⟨8446824328963808437822151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631216219309205625214767 8446824328963808437822151)
          ·
            refine ⟨12670236493445712656733227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8446824328963808437822151 12670236493445712656733227)
            ·
              refine ⟨19005354740168568985099841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12670236493445712656733227 19005354740168568985099841)
              ·
                refine ⟨14254016055126426738824881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19005354740168568985099841 14254016055126426738824881)
                ·
                  refine ⟨10690512041344820054118661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14254016055126426738824881 10690512041344820054118661)
                  ·
                    refine ⟨2004471007752153760147249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10690512041344820054118661 2004471007752153760147249)
                    ·
                      refine ⟨1503353255814115320110437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004471007752153760147249 1503353255814115320110437)
                      ·
                        rfl

theorem cell23_2927770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_2927770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927770 prefixEnd_2927770 := by exact prefixLift 2927770
  have htrace : WordTrace (prefixWord ++ tailWord_2927770) baseStart_2927770 baseEnd_2927770 := by
    simpa [prefixWord, tailWord_2927770, baseEnd_2927770] using wordTrace_append hprefix tailTrace_2927770
  have hstable : (prefixWord ++ tailWord_2927770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927770).length < 2 ^ (prefixWord ++ tailWord_2927770).sum := by decide
  have hdescent : baseEnd_2927770 < baseStart_2927770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927773 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_2927773 : Nat := 118140960795 + 2927773 * 2 ^ 59
def prefixEnd_2927773 : Nat := 4983230072969 + 3 ^ 40 * 2927773 * 2
def baseEnd_2927773 : Nat := 1503354796256078808372923

theorem tailTrace_2927773 : CollatzResearch.WordTrace tailWord_2927773 prefixEnd_2927773 1503354796256078808372923 := by
  unfold tailWord_2927773
  simp only [CollatzResearch.WordTrace]
  refine ⟨106784654022185919664579973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71189769348123946443053315 106784654022185919664579973)
  ·
    refine ⟨20022122629159859937108745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106784654022185919664579973 20022122629159859937108745)
    ·
      refine ⟨15016591971869894952831559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20022122629159859937108745 15016591971869894952831559)
      ·
        refine ⟨22524887957804842429247339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15016591971869894952831559 22524887957804842429247339)
        ·
          refine ⟨33787331936707263643871009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22524887957804842429247339 33787331936707263643871009)
          ·
            refine ⟨25340498952530447732903257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33787331936707263643871009 25340498952530447732903257)
            ·
              refine ⟨19005374214397835799677443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25340498952530447732903257 19005374214397835799677443)
              ·
                refine ⟨28508061321596753699516165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19005374214397835799677443 28508061321596753699516165)
                ·
                  refine ⟨5345261497799391318659281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28508061321596753699516165 5345261497799391318659281)
                  ·
                    refine ⟨4008946123349543488994461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5345261497799391318659281 4008946123349543488994461)
                    ·
                      refine ⟨1503354796256078808372923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4008946123349543488994461 1503354796256078808372923)
                      ·
                        rfl

theorem cell23_2927773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_2927773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927773 prefixEnd_2927773 := by exact prefixLift 2927773
  have htrace : WordTrace (prefixWord ++ tailWord_2927773) baseStart_2927773 baseEnd_2927773 := by
    simpa [prefixWord, tailWord_2927773, baseEnd_2927773] using wordTrace_append hprefix tailTrace_2927773
  have hstable : (prefixWord ++ tailWord_2927773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927773).length < 2 ^ (prefixWord ++ tailWord_2927773).sum := by decide
  have hdescent : baseEnd_2927773 < baseStart_2927773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927776 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 8]
def baseStart_2927776 : Nat := 118140960795 + 2927776 * 2 ^ 59
def prefixEnd_2927776 : Nat := 4983230072969 + 3 ^ 40 * 2927776 * 2
def baseEnd_2927776 : Nat := 167039592966449144070601

theorem tailTrace_2927776 : CollatzResearch.WordTrace tailWord_2927776 prefixEnd_2927776 167039592966449144070601 := by
  unfold tailWord_2927776
  simp only [CollatzResearch.WordTrace]
  refine ⟨53392381720587525588469591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71189842294116700784626121 53392381720587525588469591)
  ·
    refine ⟨80088572580881288382704387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53392381720587525588469591 80088572580881288382704387)
    ·
      refine ⟨120132858871321932574056581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80088572580881288382704387 120132858871321932574056581)
      ·
        refine ⟨22524911038372862357635609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120132858871321932574056581 22524911038372862357635609)
        ·
          refine ⟨16893683278779646768226707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22524911038372862357635609 16893683278779646768226707)
          ·
            refine ⟨25340524918169470152340061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16893683278779646768226707 25340524918169470152340061)
            ·
              refine ⟨9502696844313551307127523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25340524918169470152340061 9502696844313551307127523)
              ·
                refine ⟨14254045266470326960691285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9502696844313551307127523 14254045266470326960691285)
                ·
                  refine ⟨167039592966449144070601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14254045266470326960691285 167039592966449144070601)
                  ·
                    rfl

theorem cell23_2927776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 8].length) (baseStart_2927776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927776 prefixEnd_2927776 := by exact prefixLift 2927776
  have htrace : WordTrace (prefixWord ++ tailWord_2927776) baseStart_2927776 baseEnd_2927776 := by
    simpa [prefixWord, tailWord_2927776, baseEnd_2927776] using wordTrace_append hprefix tailTrace_2927776
  have hstable : (prefixWord ++ tailWord_2927776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927776).length < 2 ^ (prefixWord ++ tailWord_2927776).sum := by decide
  have hdescent : baseEnd_2927776 < baseStart_2927776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927780 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_2927780 : Nat := 118140960795 + 2927780 * 2 ^ 59
def prefixEnd_2927780 : Nat := 4983230072969 + 3 ^ 40 * 2927780 * 2
def baseEnd_2927780 : Nat := 501119463540220093661797

theorem tailTrace_2927780 : CollatzResearch.WordTrace tailWord_2927780 prefixEnd_2927780 501119463540220093661797 := by
  unfold tailWord_2927780
  simp only [CollatzResearch.WordTrace]
  refine ⟨53392454666580279930042397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71189939555440373240056529 53392454666580279930042397)
  ·
    refine ⟨20022170499967604973765899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53392454666580279930042397 20022170499967604973765899)
    ·
      refine ⟨30033255749951407460648849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20022170499967604973765899 30033255749951407460648849)
      ·
        refine ⟨22524941812463555595486637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30033255749951407460648849 22524941812463555595486637)
        ·
          refine ⟨8446853179673833348307489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22524941812463555595486637 8446853179673833348307489)
          ·
            refine ⟨6335139884755375011230617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8446853179673833348307489 6335139884755375011230617)
            ·
              refine ⟨4751354913566531258422963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6335139884755375011230617 4751354913566531258422963)
              ·
                refine ⟨7127032370349796887634445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751354913566531258422963 7127032370349796887634445)
                ·
                  refine ⟨2672637138881173832862917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7127032370349796887634445 2672637138881173832862917)
                  ·
                    refine ⟨501119463540220093661797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2672637138881173832862917 501119463540220093661797)
                    ·
                      rfl

theorem cell23_2927780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_2927780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927780 prefixEnd_2927780 := by exact prefixLift 2927780
  have htrace : WordTrace (prefixWord ++ tailWord_2927780) baseStart_2927780 baseEnd_2927780 := by
    simpa [prefixWord, tailWord_2927780, baseEnd_2927780] using wordTrace_append hprefix tailTrace_2927780
  have hstable : (prefixWord ++ tailWord_2927780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927780).length < 2 ^ (prefixWord ++ tailWord_2927780).sum := by decide
  have hdescent : baseEnd_2927780 < baseStart_2927780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927803 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 5, 1, 3]
def baseStart_2927803 : Nat := 118140960795 + 2927803 * 2 ^ 59
def prefixEnd_2927803 : Nat := 4983230072969 + 3 ^ 40 * 2927803 * 2
def baseEnd_2927803 : Nat := 1503370200675713690997785

theorem tailTrace_2927803 : CollatzResearch.WordTrace tailWord_2927803 prefixEnd_2927803 1503370200675713690997785 := by
  unfold tailWord_2927803
  simp only [CollatzResearch.WordTrace]
  refine ⟨106785748212077234788172063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71190498808051489858781375 106785748212077234788172063)
  ·
    refine ⟨160178622318115852182258095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106785748212077234788172063 160178622318115852182258095)
    ·
      refine ⟨240267933477173778273387143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160178622318115852182258095 240267933477173778273387143)
      ·
        refine ⟨360401900215760667410080715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240267933477173778273387143 360401900215760667410080715)
        ·
          refine ⟨540602850323641001115121073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360401900215760667410080715 540602850323641001115121073)
          ·
            refine ⟨405452137742730750836340805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540602850323641001115121073 405452137742730750836340805)
            ·
              refine ⟨76022275826762015781813901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 405452137742730750836340805 76022275826762015781813901)
              ·
                refine ⟨28508353435035755918180213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76022275826762015781813901 28508353435035755918180213)
                ·
                  refine ⟨2672658134534602117329395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28508353435035755918180213 2672658134534602117329395)
                  ·
                    refine ⟨4008987201801903175994093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2672658134534602117329395 4008987201801903175994093)
                    ·
                      refine ⟨1503370200675713690997785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4008987201801903175994093 1503370200675713690997785)
                      ·
                        rfl

theorem cell23_2927803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 1, 3].length) (baseStart_2927803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927803 prefixEnd_2927803 := by exact prefixLift 2927803
  have htrace : WordTrace (prefixWord ++ tailWord_2927803) baseStart_2927803 baseEnd_2927803 := by
    simpa [prefixWord, tailWord_2927803, baseEnd_2927803] using wordTrace_append hprefix tailTrace_2927803
  have hstable : (prefixWord ++ tailWord_2927803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927803).length < 2 ^ (prefixWord ++ tailWord_2927803).sum := by decide
  have hdescent : baseEnd_2927803 < baseStart_2927803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927863 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 3]
def baseStart_2927863 : Nat := 118140960795 + 2927863 * 2 ^ 59
def prefixEnd_2927863 : Nat := 4983230072969 + 3 ^ 40 * 2927863 * 2
def baseEnd_2927863 : Nat := 1503401009514983456247509

theorem tailTrace_2927863 : CollatzResearch.WordTrace tailWord_2927863 prefixEnd_2927863 1503401009514983456247509 := by
  unfold tailWord_2927863
  simp only [CollatzResearch.WordTrace]
  refine ⟨106787936591859865035356243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71191957727906576690237495 106787936591859865035356243)
  ·
    refine ⟨160181904887789797553034365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106787936591859865035356243 160181904887789797553034365)
    ·
      refine ⟨60068214332921174082387887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160181904887789797553034365 60068214332921174082387887)
      ·
        refine ⟨90102321499381761123581831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60068214332921174082387887 90102321499381761123581831)
        ·
          refine ⟨135153482249072641685372747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90102321499381761123581831 135153482249072641685372747)
          ·
            refine ⟨202730223373608962528059121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135153482249072641685372747 202730223373608962528059121)
            ·
              refine ⟨152047667530206721896044341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202730223373608962528059121 152047667530206721896044341)
              ·
                refine ⟨14254468830956880177754157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152047667530206721896044341 14254468830956880177754157)
                ·
                  refine ⟨5345425811608830066657809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14254468830956880177754157 5345425811608830066657809)
                  ·
                    refine ⟨4009069358706622549993357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5345425811608830066657809 4009069358706622549993357)
                    ·
                      refine ⟨1503401009514983456247509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4009069358706622549993357 1503401009514983456247509)
                      ·
                        rfl

theorem cell23_2927863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_2927863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927863 prefixEnd_2927863 := by exact prefixLift 2927863
  have htrace : WordTrace (prefixWord ++ tailWord_2927863) baseStart_2927863 baseEnd_2927863 := by
    simpa [prefixWord, tailWord_2927863, baseEnd_2927863] using wordTrace_append hprefix tailTrace_2927863
  have hstable : (prefixWord ++ tailWord_2927863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927863).length < 2 ^ (prefixWord ++ tailWord_2927863).sum := by decide
  have hdescent : baseEnd_2927863 < baseStart_2927863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927866 : List Nat := [3, 1, 1, 1, 1, 4, 1, 11]
def baseStart_2927866 : Nat := 118140960795 + 2927866 * 2 ^ 59
def prefixEnd_2927866 : Nat := 4983230072969 + 3 ^ 40 * 2927866 * 2
def baseEnd_2927866 : Nat := 55681575924331368315185

theorem tailTrace_2927866 : CollatzResearch.WordTrace tailWord_2927866 prefixEnd_2927866 55681575924331368315185 := by
  unfold tailWord_2927866
  simp only [CollatzResearch.WordTrace]
  refine ⟨26697011502712249136928863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71192030673899331031810301 26697011502712249136928863)
  ·
    refine ⟨40045517254068373705393295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26697011502712249136928863 40045517254068373705393295)
    ·
      refine ⟨60068275881102560558089943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40045517254068373705393295 60068275881102560558089943)
      ·
        refine ⟨90102413821653840837134915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60068275881102560558089943 90102413821653840837134915)
        ·
          refine ⟨135153620732480761255702373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90102413821653840837134915 135153620732480761255702373)
          ·
            refine ⟨25341303887340142735444195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135153620732480761255702373 25341303887340142735444195)
            ·
              refine ⟨38011955831010214103166293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25341303887340142735444195 38011955831010214103166293)
              ·
                refine ⟨55681575924331368315185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 38011955831010214103166293 55681575924331368315185)
                ·
                  rfl

theorem cell23_2927866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 11].length) (baseStart_2927866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927866 prefixEnd_2927866 := by exact prefixLift 2927866
  have htrace : WordTrace (prefixWord ++ tailWord_2927866) baseStart_2927866 baseEnd_2927866 := by
    simpa [prefixWord, tailWord_2927866, baseEnd_2927866] using wordTrace_append hprefix tailTrace_2927866
  have hstable : (prefixWord ++ tailWord_2927866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927866).length < 2 ^ (prefixWord ++ tailWord_2927866).sum := by decide
  have hdescent : baseEnd_2927866 < baseStart_2927866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927870 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2927870 : Nat := 118140960795 + 2927870 * 2 ^ 59
def prefixEnd_2927870 : Nat := 4983230072969 + 3 ^ 40 * 2927870 * 2
def baseEnd_2927870 : Nat := 501134867959854976286659

theorem tailTrace_2927870 : CollatzResearch.WordTrace tailWord_2927870 prefixEnd_2927870 501134867959854976286659 := by
  unfold tailWord_2927870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13348523987854313153857633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71192127935223003487240709 13348523987854313153857633)
  ·
    refine ⟨10011392990890734865393225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13348523987854313153857633 10011392990890734865393225)
    ·
      refine ⟨7508544743168051149044919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10011392990890734865393225 7508544743168051149044919)
      ·
        refine ⟨11262817114752076723567379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7508544743168051149044919 11262817114752076723567379)
        ·
          refine ⟨16894225672128115085351069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11262817114752076723567379 16894225672128115085351069)
          ·
            refine ⟨6335334627048043157006651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16894225672128115085351069 6335334627048043157006651)
            ·
              refine ⟨9503001940572064735509977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6335334627048043157006651 9503001940572064735509977)
              ·
                refine ⟨7127251455429048551632483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9503001940572064735509977 7127251455429048551632483)
                ·
                  refine ⟨10690877183143572827448725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7127251455429048551632483 10690877183143572827448725)
                  ·
                    refine ⟨501134867959854976286659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10690877183143572827448725 501134867959854976286659)
                    ·
                      rfl

theorem cell23_2927870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2927870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927870 prefixEnd_2927870 := by exact prefixLift 2927870
  have htrace : WordTrace (prefixWord ++ tailWord_2927870) baseStart_2927870 baseEnd_2927870 := by
    simpa [prefixWord, tailWord_2927870, baseEnd_2927870] using wordTrace_append hprefix tailTrace_2927870
  have hstable : (prefixWord ++ tailWord_2927870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927870).length < 2 ^ (prefixWord ++ tailWord_2927870).sum := by decide
  have hdescent : baseEnd_2927870 < baseStart_2927870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927873 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_2927873 : Nat := 118140960795 + 2927873 * 2 ^ 59
def prefixEnd_2927873 : Nat := 4983230072969 + 3 ^ 40 * 2927873 * 2
def baseEnd_2927873 : Nat := 1503406144321528417122463

theorem tailTrace_2927873 : CollatzResearch.WordTrace tailWord_2927873 prefixEnd_2927873 1503406144321528417122463 := by
  unfold tailWord_2927873
  simp only [CollatzResearch.WordTrace]
  refine ⟨106788301321823636743220273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71192200881215757828813515 106788301321823636743220273)
  ·
    refine ⟨80091225991367727557415205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106788301321823636743220273 80091225991367727557415205)
    ·
      refine ⟨15017104873381448917015351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80091225991367727557415205 15017104873381448917015351)
      ·
        refine ⟨22525657310072173375523027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15017104873381448917015351 22525657310072173375523027)
        ·
          refine ⟨33788485965108260063284541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22525657310072173375523027 33788485965108260063284541)
          ·
            refine ⟨12670682236915597523731703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33788485965108260063284541 12670682236915597523731703)
            ·
              refine ⟨19006023355373396285597555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12670682236915597523731703 19006023355373396285597555)
              ·
                refine ⟨28509035033060094428396333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19006023355373396285597555 28509035033060094428396333)
                ·
                  refine ⟨10690888137397535410648625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28509035033060094428396333 10690888137397535410648625)
                  ·
                    refine ⟨8018166103048151557986469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10690888137397535410648625 8018166103048151557986469)
                    ·
                      refine ⟨1503406144321528417122463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8018166103048151557986469 1503406144321528417122463)
                      ·
                        rfl

theorem cell23_2927873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_2927873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927873 prefixEnd_2927873 := by exact prefixLift 2927873
  have htrace : WordTrace (prefixWord ++ tailWord_2927873) baseStart_2927873 baseEnd_2927873 := by
    simpa [prefixWord, tailWord_2927873, baseEnd_2927873] using wordTrace_append hprefix tailTrace_2927873
  have hstable : (prefixWord ++ tailWord_2927873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927873).length < 2 ^ (prefixWord ++ tailWord_2927873).sum := by decide
  have hdescent : baseEnd_2927873 < baseStart_2927873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927874 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2927874 : Nat := 118140960795 + 2927874 * 2 ^ 59
def prefixEnd_2927874 : Nat := 4983230072969 + 3 ^ 40 * 2927874 * 2
def baseEnd_2927874 : Nat := 501135552600727637736653

theorem tailTrace_2927874 : CollatzResearch.WordTrace tailWord_2927874 prefixEnd_2927874 501135552600727637736653 := by
  unfold tailWord_2927874
  simp only [CollatzResearch.WordTrace]
  refine ⟨26697084448705003478501669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71192225196546675942671117 26697084448705003478501669)
  ·
    refine ⟨5005703334132188152219063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26697084448705003478501669 5005703334132188152219063)
    ·
      refine ⟨7508555001198282228328595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5005703334132188152219063 7508555001198282228328595)
      ·
        refine ⟨11262832501797423342492893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7508555001198282228328595 11262832501797423342492893)
        ·
          refine ⟨4223562188174033753434835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11262832501797423342492893 4223562188174033753434835)
          ·
            refine ⟨6335343282261050630152253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223562188174033753434835 6335343282261050630152253)
            ·
              refine ⟨2375753730847893986307095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6335343282261050630152253 2375753730847893986307095)
              ·
                refine ⟨3563630596271840979460643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375753730847893986307095 3563630596271840979460643)
                ·
                  refine ⟨5345445894407761469190965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563630596271840979460643 5345445894407761469190965)
                  ·
                    refine ⟨501135552600727637736653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5345445894407761469190965 501135552600727637736653)
                    ·
                      rfl

theorem cell23_2927874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2927874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927874 prefixEnd_2927874 := by exact prefixLift 2927874
  have htrace : WordTrace (prefixWord ++ tailWord_2927874) baseStart_2927874 baseEnd_2927874 := by
    simpa [prefixWord, tailWord_2927874, baseEnd_2927874] using wordTrace_append hprefix tailTrace_2927874
  have hstable : (prefixWord ++ tailWord_2927874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927874).length < 2 ^ (prefixWord ++ tailWord_2927874).sum := by decide
  have hdescent : baseEnd_2927874 < baseStart_2927874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927893 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_2927893 : Nat := 118140960795 + 2927893 * 2 ^ 59
def prefixEnd_2927893 : Nat := 4983230072969 + 3 ^ 40 * 2927893 * 2
def baseEnd_2927893 : Nat := 1503416413934618338872371

theorem tailTrace_2927893 : CollatzResearch.WordTrace tailWord_2927893 prefixEnd_2927893 1503416413934618338872371 := by
  unfold tailWord_2927893
  simp only [CollatzResearch.WordTrace]
  refine ⟨106789030781751180158948333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71192687187834120105965555 106789030781751180158948333)
  ·
    refine ⟨40045886543156692559605625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106789030781751180158948333 40045886543156692559605625)
    ·
      refine ⟨30034414907367519419704219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40045886543156692559605625 30034414907367519419704219)
      ·
        refine ⟨45051622361051279129556329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30034414907367519419704219 45051622361051279129556329)
        ·
          refine ⟨33788716770788459347167247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45051622361051279129556329 33788716770788459347167247)
          ·
            refine ⟨50683075156182689020750871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33788716770788459347167247 50683075156182689020750871)
            ·
              refine ⟨76024612734274033531126307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50683075156182689020750871 76024612734274033531126307)
              ·
                refine ⟨114036919101411050296689461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76024612734274033531126307 114036919101411050296689461)
                ·
                  refine ⟨10690961165757285965314637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114036919101411050296689461 10690961165757285965314637)
                  ·
                    refine ⟨4009110437158982236992989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10690961165757285965314637 4009110437158982236992989)
                    ·
                      refine ⟨1503416413934618338872371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4009110437158982236992989 1503416413934618338872371)
                      ·
                        rfl

theorem cell23_2927893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_2927893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927893 prefixEnd_2927893 := by exact prefixLift 2927893
  have htrace : WordTrace (prefixWord ++ tailWord_2927893) baseStart_2927893 baseEnd_2927893 := by
    simpa [prefixWord, tailWord_2927893, baseEnd_2927893] using wordTrace_append hprefix tailTrace_2927893
  have hstable : (prefixWord ++ tailWord_2927893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927893).length < 2 ^ (prefixWord ++ tailWord_2927893).sum := by decide
  have hdescent : baseEnd_2927893 < baseStart_2927893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927917 : List Nat := [1, 5, 3, 1, 1, 2, 3, 7]
def baseStart_2927917 : Nat := 118140960795 + 2927917 * 2 ^ 59
def prefixEnd_2927917 : Nat := 4983230072969 + 3 ^ 40 * 2927917 * 2
def baseEnd_2927917 : Nat := 55682545832234305369343

theorem tailTrace_2927917 : CollatzResearch.WordTrace tailWord_2927917 prefixEnd_2927917 55682545832234305369343 := by
  unfold tailWord_2927917
  simp only [CollatzResearch.WordTrace]
  refine ⟨106789906133664232257822005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71193270755776154838548003 106789906133664232257822005)
  ·
    refine ⟨10011553700031021774170813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106789906133664232257822005 10011553700031021774170813)
    ·
      refine ⟨3754332637511633165314055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10011553700031021774170813 3754332637511633165314055)
      ·
        refine ⟨5631498956267449747971083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3754332637511633165314055 5631498956267449747971083)
        ·
          refine ⟨8447248434401174621956625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631498956267449747971083 8447248434401174621956625)
          ·
            refine ⟨6335436325800880966467469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8447248434401174621956625 6335436325800880966467469)
            ·
              refine ⟨2375788622175330362425301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6335436325800880966467469 2375788622175330362425301)
              ·
                refine ⟨55682545832234305369343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2375788622175330362425301 55682545832234305369343)
                ·
                  rfl

theorem cell23_2927917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 7].length) (baseStart_2927917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927917 prefixEnd_2927917 := by exact prefixLift 2927917
  have htrace : WordTrace (prefixWord ++ tailWord_2927917) baseStart_2927917 baseEnd_2927917 := by
    simpa [prefixWord, tailWord_2927917, baseEnd_2927917] using wordTrace_append hprefix tailTrace_2927917
  have hstable : (prefixWord ++ tailWord_2927917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927917).length < 2 ^ (prefixWord ++ tailWord_2927917).sum := by decide
  have hdescent : baseEnd_2927917 < baseStart_2927917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927920 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 3, 3, 2]
def baseStart_2927920 : Nat := 118140960795 + 2927920 * 2 ^ 59
def prefixEnd_2927920 : Nat := 4983230072969 + 3 ^ 40 * 2927920 * 2
def baseEnd_2927920 : Nat := 1503430277912289733234747

theorem tailTrace_2927920 : CollatzResearch.WordTrace tailWord_2927920 prefixEnd_2927920 1503430277912289733234747 := by
  unfold tailWord_2927920
  simp only [CollatzResearch.WordTrace]
  refine ⟨53395007776326681885090607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71193343701768909180120809 53395007776326681885090607)
  ·
    refine ⟨80092511664490022827635911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53395007776326681885090607 80092511664490022827635911)
    ·
      refine ⟨120138767496735034241453867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80092511664490022827635911 120138767496735034241453867)
      ·
        refine ⟨180208151245102551362180801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120138767496735034241453867 180208151245102551362180801)
        ·
          refine ⟨135156113433826913521635601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180208151245102551362180801 135156113433826913521635601)
          ·
            refine ⟨101367085075370185141226701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135156113433826913521635601 101367085075370185141226701)
            ·
              refine ⟨38012656903263819427960013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101367085075370185141226701 38012656903263819427960013)
              ·
                refine ⟨14254746338723932285485005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38012656903263819427960013 14254746338723932285485005)
                ·
                  refine ⟨5345529877021474607056877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14254746338723932285485005 5345529877021474607056877)
                  ·
                    refine ⟨2004573703883052977646329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5345529877021474607056877 2004573703883052977646329)
                    ·
                      refine ⟨1503430277912289733234747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004573703883052977646329 1503430277912289733234747)
                      ·
                        rfl

theorem cell23_2927920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 3, 2].length) (baseStart_2927920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927920 prefixEnd_2927920 := by exact prefixLift 2927920
  have htrace : WordTrace (prefixWord ++ tailWord_2927920) baseStart_2927920 baseEnd_2927920 := by
    simpa [prefixWord, tailWord_2927920, baseEnd_2927920] using wordTrace_append hprefix tailTrace_2927920
  have hstable : (prefixWord ++ tailWord_2927920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927920).length < 2 ^ (prefixWord ++ tailWord_2927920).sum := by decide
  have hdescent : baseEnd_2927920 < baseStart_2927920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927943 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 2, 6]
def baseStart_2927943 : Nat := 118140960795 + 2927943 * 2 ^ 59
def prefixEnd_2927943 : Nat := 4983230072969 + 3 ^ 40 * 2927943 * 2
def baseEnd_2927943 : Nat := 501147362655781047749047

theorem tailTrace_2927943 : CollatzResearch.WordTrace tailWord_2927943 prefixEnd_2927943 501147362655781047749047 := by
  unfold tailWord_2927943
  simp only [CollatzResearch.WordTrace]
  refine ⟨106790854431570038698268483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71193902954380025798845655 106790854431570038698268483)
  ·
    refine ⟨160186281647355058047402725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106790854431570038698268483 160186281647355058047402725)
    ·
      refine ⟨30034927808879073383888011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160186281647355058047402725 30034927808879073383888011)
      ·
        refine ⟨45052391713318610075832017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30034927808879073383888011 45052391713318610075832017)
        ·
          refine ⟨33789293784988957556874013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45052391713318610075832017 33789293784988957556874013)
          ·
            refine ⟨12670985169370859083827755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33789293784988957556874013 12670985169370859083827755)
            ·
              refine ⟨19006477754056288625741633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12670985169370859083827755 19006477754056288625741633)
              ·
                refine ⟨14254858315542216469306225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19006477754056288625741633 14254858315542216469306225)
                ·
                  refine ⟨10691143736656662351979669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14254858315542216469306225 10691143736656662351979669)
                  ·
                    refine ⟨501147362655781047749047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10691143736656662351979669 501147362655781047749047)
                    ·
                      rfl

theorem cell23_2927943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_2927943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927943 prefixEnd_2927943 := by exact prefixLift 2927943
  have htrace : WordTrace (prefixWord ++ tailWord_2927943) baseStart_2927943 baseEnd_2927943 := by
    simpa [prefixWord, tailWord_2927943, baseEnd_2927943] using wordTrace_append hprefix tailTrace_2927943
  have hstable : (prefixWord ++ tailWord_2927943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927943).length < 2 ^ (prefixWord ++ tailWord_2927943).sum := by decide
  have hdescent : baseEnd_2927943 < baseStart_2927943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927958 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2927958 : Nat := 118140960795 + 2927958 * 2 ^ 59
def prefixEnd_2927958 : Nat := 4983230072969 + 3 ^ 40 * 2927958 * 2
def baseEnd_2927958 : Nat := 1503449790177160584559573

theorem tailTrace_2927958 : CollatzResearch.WordTrace tailWord_2927958 prefixEnd_2927958 1503449790177160584559573 := by
  unfold tailWord_2927958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6674462595407231016254033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71194267684343797506709685 6674462595407231016254033)
  ·
    refine ⟨5005846946555423262190525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6674462595407231016254033 5005846946555423262190525)
    ·
      refine ⟨1877192604958283723321447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5005846946555423262190525 1877192604958283723321447)
      ·
        refine ⟨2815788907437425584982171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1877192604958283723321447 2815788907437425584982171)
        ·
          refine ⟨4223683361156138377473257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815788907437425584982171 4223683361156138377473257)
          ·
            refine ⟨3167762520867103783104943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4223683361156138377473257 3167762520867103783104943)
            ·
              refine ⟨4751643781300655674657415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167762520867103783104943 4751643781300655674657415)
              ·
                refine ⟨7127465671950983511986123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751643781300655674657415 7127465671950983511986123)
                ·
                  refine ⟨10691198507926475267979185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7127465671950983511986123 10691198507926475267979185)
                  ·
                    refine ⟨8018398880944856450984389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10691198507926475267979185 8018398880944856450984389)
                    ·
                      refine ⟨1503449790177160584559573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8018398880944856450984389 1503449790177160584559573)
                      ·
                        rfl

theorem cell23_2927958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2927958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927958 prefixEnd_2927958 := by exact prefixLift 2927958
  have htrace : WordTrace (prefixWord ++ tailWord_2927958) baseStart_2927958 baseEnd_2927958 := by
    simpa [prefixWord, tailWord_2927958, baseEnd_2927958] using wordTrace_append hprefix tailTrace_2927958
  have hstable : (prefixWord ++ tailWord_2927958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927958).length < 2 ^ (prefixWord ++ tailWord_2927958).sum := by decide
  have hdescent : baseEnd_2927958 < baseStart_2927958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927970 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2927970 : Nat := 118140960795 + 2927970 * 2 ^ 59
def prefixEnd_2927970 : Nat := 4983230072969 + 3 ^ 40 * 2927970 * 2
def baseEnd_2927970 : Nat := 1503455951945014537609517

theorem tailTrace_2927970 : CollatzResearch.WordTrace tailWord_2927970 prefixEnd_2927970 1503455951945014537609517 := by
  unfold tailWord_2927970
  simp only [CollatzResearch.WordTrace]
  refine ⟨26697959800618055577375341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71194559468314814873000909 26697959800618055577375341)
  ·
    refine ⟨10011734925231770841515753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26697959800618055577375341 10011734925231770841515753)
    ·
      refine ⟨7508801193923828131136815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10011734925231770841515753 7508801193923828131136815)
      ·
        refine ⟨11263201790885742196705223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7508801193923828131136815 11263201790885742196705223)
        ·
          refine ⟨16894802686328613295057835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11263201790885742196705223 16894802686328613295057835)
          ·
            refine ⟨25342204029492919942586753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16894802686328613295057835 25342204029492919942586753)
            ·
              refine ⟨19006653022119689956940065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25342204029492919942586753 19006653022119689956940065)
              ·
                refine ⟨14254989766589767467705049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19006653022119689956940065 14254989766589767467705049)
                ·
                  refine ⟨10691242324942325600778787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14254989766589767467705049 10691242324942325600778787)
                  ·
                    refine ⟨16036863487413488401168181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10691242324942325600778787 16036863487413488401168181)
                    ·
                      refine ⟨1503455951945014537609517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16036863487413488401168181 1503455951945014537609517)
                      ·
                        rfl

theorem cell23_2927970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2927970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927970 prefixEnd_2927970 := by exact prefixLift 2927970
  have htrace : WordTrace (prefixWord ++ tailWord_2927970) baseStart_2927970 baseEnd_2927970 := by
    simpa [prefixWord, tailWord_2927970, baseEnd_2927970] using wordTrace_append hprefix tailTrace_2927970
  have hstable : (prefixWord ++ tailWord_2927970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927970).length < 2 ^ (prefixWord ++ tailWord_2927970).sum := by decide
  have hdescent : baseEnd_2927970 < baseStart_2927970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927973 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 7]
def baseStart_2927973 : Nat := 118140960795 + 2927973 * 2 ^ 59
def prefixEnd_2927973 : Nat := 4983230072969 + 3 ^ 40 * 2927973 * 2
def baseEnd_2927973 : Nat := 167050832487442002874667

theorem tailTrace_2927973 : CollatzResearch.WordTrace tailWord_2927973 prefixEnd_2927973 167050832487442002874667 := by
  unfold tailWord_2927973
  simp only [CollatzResearch.WordTrace]
  refine ⟨106791948621461353821860573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71194632414307569214573715 106791948621461353821860573)
  ·
    refine ⟨40046980733048007683197715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106791948621461353821860573 40046980733048007683197715)
    ·
      refine ⟨60070471099572011524796573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40046980733048007683197715 60070471099572011524796573)
      ·
        refine ⟨22526426662339504321798715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60070471099572011524796573 22526426662339504321798715)
        ·
          refine ⟨33789639993509256482698073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22526426662339504321798715 33789639993509256482698073)
          ·
            refine ⟨25342229995131942362023555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33789639993509256482698073 25342229995131942362023555)
            ·
              refine ⟨38013344992697913543035333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25342229995131942362023555 38013344992697913543035333)
              ·
                refine ⟨7127502186130858789319125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38013344992697913543035333 7127502186130858789319125)
                ·
                  refine ⟨167050832487442002874667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7127502186130858789319125 167050832487442002874667)
                  ·
                    rfl

theorem cell23_2927973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_2927973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2927973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2927973 prefixEnd_2927973 := by exact prefixLift 2927973
  have htrace : WordTrace (prefixWord ++ tailWord_2927973) baseStart_2927973 baseEnd_2927973 := by
    simpa [prefixWord, tailWord_2927973, baseEnd_2927973] using wordTrace_append hprefix tailTrace_2927973
  have hstable : (prefixWord ++ tailWord_2927973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927973).length < 2 ^ (prefixWord ++ tailWord_2927973).sum := by decide
  have hdescent : baseEnd_2927973 < baseStart_2927973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928018 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2928018 : Nat := 118140960795 + 2928018 * 2 ^ 59
def prefixEnd_2928018 : Nat := 4983230072969 + 3 ^ 40 * 2928018 * 2
def baseEnd_2928018 : Nat := 1503480599016430349809297

theorem tailTrace_2928018 : CollatzResearch.WordTrace tailWord_2928018 prefixEnd_2928018 1503480599016430349809297 := by
  unfold tailWord_2928018
  simp only [CollatzResearch.WordTrace]
  refine ⟨26698397476574581626812177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71195726604198884338165805 26698397476574581626812177)
  ·
    refine ⟨20023798107430936220109133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26698397476574581626812177 20023798107430936220109133)
    ·
      refine ⟨7508924290286601082540925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20023798107430936220109133 7508924290286601082540925)
      ·
        refine ⟨2815846608857475405952847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7508924290286601082540925 2815846608857475405952847)
        ·
          refine ⟨4223769913286213108929271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815846608857475405952847 4223769913286213108929271)
          ·
            refine ⟨6335654869929319663393907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223769913286213108929271 6335654869929319663393907)
            ·
              refine ⟨9503482304893979495090861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6335654869929319663393907 9503482304893979495090861)
              ·
                refine ⟨3563805864335242310659073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9503482304893979495090861 3563805864335242310659073)
                ·
                  refine ⟨2672854398251431732994305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3563805864335242310659073 2672854398251431732994305)
                  ·
                    refine ⟨2004640798688573799745729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2672854398251431732994305 2004640798688573799745729)
                    ·
                      refine ⟨1503480599016430349809297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004640798688573799745729 1503480599016430349809297)
                      ·
                        rfl

theorem cell23_2928018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2928018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928018 prefixEnd_2928018 := by exact prefixLift 2928018
  have htrace : WordTrace (prefixWord ++ tailWord_2928018) baseStart_2928018 baseEnd_2928018 := by
    simpa [prefixWord, tailWord_2928018, baseEnd_2928018] using wordTrace_append hprefix tailTrace_2928018
  have hstable : (prefixWord ++ tailWord_2928018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928018).length < 2 ^ (prefixWord ++ tailWord_2928018).sum := by decide
  have hdescent : baseEnd_2928018 < baseStart_2928018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928050 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_2928050 : Nat := 118140960795 + 2928050 * 2 ^ 59
def prefixEnd_2928050 : Nat := 4983230072969 + 3 ^ 40 * 2928050 * 2
def baseEnd_2928050 : Nat := 501165676799124741536383

theorem tailTrace_2928050 : CollatzResearch.WordTrace tailWord_2928050 prefixEnd_2928050 501165676799124741536383 := by
  unfold tailWord_2928050
  simp only [CollatzResearch.WordTrace]
  refine ⟨26698689260545598993103401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71196504694788263981609069 26698689260545598993103401)
  ·
    refine ⟨20024016945409199244827551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26698689260545598993103401 20024016945409199244827551)
    ·
      refine ⟨30036025418113798867241327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20024016945409199244827551 30036025418113798867241327)
      ·
        refine ⟨45054038127170698300861991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30036025418113798867241327 45054038127170698300861991)
        ·
          refine ⟨67581057190756047451292987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45054038127170698300861991 67581057190756047451292987)
          ·
            refine ⟨101371585786134071176939481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67581057190756047451292987 101371585786134071176939481)
            ·
              refine ⟨76028689339600553382704611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101371585786134071176939481 76028689339600553382704611)
              ·
                refine ⟨114043034009400830074056917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76028689339600553382704611 114043034009400830074056917)
                ·
                  refine ⟨2672883609595331954860709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 114043034009400830074056917 2672883609595331954860709)
                  ·
                    refine ⟨501165676799124741536383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2672883609595331954860709 501165676799124741536383)
                    ·
                      rfl

theorem cell23_2928050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_2928050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928050 prefixEnd_2928050 := by exact prefixLift 2928050
  have htrace : WordTrace (prefixWord ++ tailWord_2928050) baseStart_2928050 baseEnd_2928050 := by
    simpa [prefixWord, tailWord_2928050, baseEnd_2928050] using wordTrace_append hprefix tailTrace_2928050
  have hstable : (prefixWord ++ tailWord_2928050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928050).length < 2 ^ (prefixWord ++ tailWord_2928050).sum := by decide
  have hdescent : baseEnd_2928050 < baseStart_2928050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928063 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 8]
def baseStart_2928063 : Nat := 118140960795 + 2928063 * 2 ^ 59
def prefixEnd_2928063 : Nat := 4983230072969 + 3 ^ 40 * 2928063 * 2
def baseEnd_2928063 : Nat := 167055967293986963749621

theorem tailTrace_2928063 : CollatzResearch.WordTrace tailWord_2928063 prefixEnd_2928063 167055967293986963749621 := by
  unfold tailWord_2928063
  simp only [CollatzResearch.WordTrace]
  refine ⟨106795231191135299192636843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71196820794090199461757895 106795231191135299192636843)
  ·
    refine ⟨160192846786702948788955265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106795231191135299192636843 160192846786702948788955265)
    ·
      refine ⟨120144635090027211591716449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160192846786702948788955265 120144635090027211591716449)
      ·
        refine ⟨90108476317520408693787337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120144635090027211591716449 90108476317520408693787337)
        ·
          refine ⟨67581357238140306520340503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90108476317520408693787337 67581357238140306520340503)
          ·
            refine ⟨101372035857210459780510755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67581357238140306520340503 101372035857210459780510755)
            ·
              refine ⟨152058053785815689670766133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101372035857210459780510755 152058053785815689670766133)
              ·
                refine ⟨14255442542420220906634325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152058053785815689670766133 14255442542420220906634325)
                ·
                  refine ⟨167055967293986963749621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14255442542420220906634325 167055967293986963749621)
                  ·
                    rfl

theorem cell23_2928063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 8].length) (baseStart_2928063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928063 prefixEnd_2928063 := by exact prefixLift 2928063
  have htrace : WordTrace (prefixWord ++ tailWord_2928063) baseStart_2928063 baseEnd_2928063 := by
    simpa [prefixWord, tailWord_2928063, baseEnd_2928063] using wordTrace_append hprefix tailTrace_2928063
  have hstable : (prefixWord ++ tailWord_2928063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928063).length < 2 ^ (prefixWord ++ tailWord_2928063).sum := by decide
  have hdescent : baseEnd_2928063 < baseStart_2928063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928084 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_2928084 : Nat := 118140960795 + 2928084 * 2 ^ 59
def prefixEnd_2928084 : Nat := 4983230072969 + 3 ^ 40 * 2928084 * 2
def baseEnd_2928084 : Nat := 501171496246542363861331

theorem tailTrace_2928084 : CollatzResearch.WordTrace tailWord_2928084 prefixEnd_2928084 501171496246542363861331 := by
  unfold tailWord_2928084
  simp only [CollatzResearch.WordTrace]
  refine ⟨53397998562029609889575653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71197331416039479852767537 53397998562029609889575653)
  ·
    refine ⟨10012124730380551854295435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53397998562029609889575653 10012124730380551854295435)
    ·
      refine ⟨15018187095570827781443153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10012124730380551854295435 15018187095570827781443153)
      ·
        refine ⟨11263640321678120836082365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15018187095570827781443153 11263640321678120836082365)
        ·
          refine ⟨4223865120629295313530887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11263640321678120836082365 4223865120629295313530887)
          ·
            refine ⟨6335797680943942970296331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223865120629295313530887 6335797680943942970296331)
            ·
              refine ⟨9503696521415914455444497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6335797680943942970296331 9503696521415914455444497)
              ·
                refine ⟨7127772391061935841583373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9503696521415914455444497 7127772391061935841583373)
                ·
                  refine ⟨2672914646648225940593765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7127772391061935841583373 2672914646648225940593765)
                  ·
                    refine ⟨501171496246542363861331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2672914646648225940593765 501171496246542363861331)
                    ·
                      rfl

theorem cell23_2928084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_2928084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928084 prefixEnd_2928084 := by exact prefixLift 2928084
  have htrace : WordTrace (prefixWord ++ tailWord_2928084) baseStart_2928084 baseEnd_2928084 := by
    simpa [prefixWord, tailWord_2928084, baseEnd_2928084] using wordTrace_append hprefix tailTrace_2928084
  have hstable : (prefixWord ++ tailWord_2928084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928084).length < 2 ^ (prefixWord ++ tailWord_2928084).sum := by decide
  have hdescent : baseEnd_2928084 < baseStart_2928084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928101 : List Nat := [1, 3, 1, 5, 1, 2, 2, 3, 1, 4]
def baseStart_2928101 : Nat := 118140960795 + 2928101 * 2 ^ 59
def prefixEnd_2928101 : Nat := 4983230072969 + 3 ^ 40 * 2928101 * 2
def baseEnd_2928101 : Nat := 501174405970251175023805

theorem tailTrace_2928101 : CollatzResearch.WordTrace tailWord_2928101 prefixEnd_2928101 501174405970251175023805 := by
  unfold tailWord_2928101
  simp only [CollatzResearch.WordTrace]
  refine ⟨106796617164997631682520157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71197744776665087788346771 106796617164997631682520157)
  ·
    refine ⟨40048731436874111880945059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106796617164997631682520157 40048731436874111880945059)
    ·
      refine ⟨60073097155311167821417589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40048731436874111880945059 60073097155311167821417589)
      ·
        refine ⟨5631852858310421983257899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60073097155311167821417589 5631852858310421983257899)
        ·
          refine ⟨8447779287465632974886849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631852858310421983257899 8447779287465632974886849)
          ·
            refine ⟨6335834465599224731165137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8447779287465632974886849 6335834465599224731165137)
            ·
              refine ⟨4751875849199418548373853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6335834465599224731165137 4751875849199418548373853)
              ·
                refine ⟨1781953443449781955640195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4751875849199418548373853 1781953443449781955640195)
                ·
                  refine ⟨2672930165174672933460293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781953443449781955640195 2672930165174672933460293)
                  ·
                    refine ⟨501174405970251175023805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2672930165174672933460293 501174405970251175023805)
                    ·
                      rfl

theorem cell23_2928101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_2928101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928101 prefixEnd_2928101 := by exact prefixLift 2928101
  have htrace : WordTrace (prefixWord ++ tailWord_2928101) baseStart_2928101 baseEnd_2928101 := by
    simpa [prefixWord, tailWord_2928101, baseEnd_2928101] using wordTrace_append hprefix tailTrace_2928101
  have hstable : (prefixWord ++ tailWord_2928101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928101).length < 2 ^ (prefixWord ++ tailWord_2928101).sum := by decide
  have hdescent : baseEnd_2928101 < baseStart_2928101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928114 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 6]
def baseStart_2928114 : Nat := 118140960795 + 2928114 * 2 ^ 59
def prefixEnd_2928114 : Nat := 4983230072969 + 3 ^ 40 * 2928114 * 2
def baseEnd_2928114 : Nat := 167058877017695774912095

theorem tailTrace_2928114 : CollatzResearch.WordTrace tailWord_2928114 prefixEnd_2928114 167058877017695774912095 := by
  unfold tailWord_2928114
  simp only [CollatzResearch.WordTrace]
  refine ⟨26699272828487633725685849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71198060875967023268495597 26699272828487633725685849)
  ·
    refine ⟨20024454621365725294264387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26699272828487633725685849 20024454621365725294264387)
    ·
      refine ⟨30036681932048587941396581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20024454621365725294264387 30036681932048587941396581)
      ·
        refine ⟨5631877862259110239011859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30036681932048587941396581 5631877862259110239011859)
        ·
          refine ⟨8447816793388665358517789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631877862259110239011859 8447816793388665358517789)
          ·
            refine ⟨3167931297520749509444171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8447816793388665358517789 3167931297520749509444171)
            ·
              refine ⟨4751896946281124264166257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167931297520749509444171 4751896946281124264166257)
              ·
                refine ⟨3563922709710843198124693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4751896946281124264166257 3563922709710843198124693)
                ·
                  refine ⟨167058877017695774912095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3563922709710843198124693 167058877017695774912095)
                  ·
                    rfl

theorem cell23_2928114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_2928114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928114 prefixEnd_2928114 := by exact prefixLift 2928114
  have htrace : WordTrace (prefixWord ++ tailWord_2928114) baseStart_2928114 baseEnd_2928114 := by
    simpa [prefixWord, tailWord_2928114, baseEnd_2928114] using wordTrace_append hprefix tailTrace_2928114
  have hstable : (prefixWord ++ tailWord_2928114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928114).length < 2 ^ (prefixWord ++ tailWord_2928114).sum := by decide
  have hdescent : baseEnd_2928114 < baseStart_2928114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928117 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2928117 : Nat := 118140960795 + 2928117 * 2 ^ 59
def prefixEnd_2928117 : Nat := 4983230072969 + 3 ^ 40 * 2928117 * 2
def baseEnd_2928117 : Nat := 1503531433601225462471341

theorem tailTrace_2928117 : CollatzResearch.WordTrace tailWord_2928117 prefixEnd_2928117 1503531433601225462471341 := by
  unfold tailWord_2928117
  simp only [CollatzResearch.WordTrace]
  refine ⟨106797200732939666415102605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71198133821959777610068403 106797200732939666415102605)
  ·
    refine ⟨40048950274852374905663477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106797200732939666415102605 40048950274852374905663477)
    ·
      refine ⟨3754589088267410147405951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40048950274852374905663477 3754589088267410147405951)
      ·
        refine ⟨5631883632401115221108927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3754589088267410147405951 5631883632401115221108927)
        ·
          refine ⟨8447825448601672831663391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631883632401115221108927 8447825448601672831663391)
          ·
            refine ⟨12671738172902509247495087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8447825448601672831663391 12671738172902509247495087)
            ·
              refine ⟨19007607259353763871242631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12671738172902509247495087 19007607259353763871242631)
              ·
                refine ⟨28511410889030645806863947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19007607259353763871242631 28511410889030645806863947)
                ·
                  refine ⟨42767116333545968710295921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28511410889030645806863947 42767116333545968710295921)
                  ·
                    refine ⟨32075337250159476532721941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42767116333545968710295921 32075337250159476532721941)
                    ·
                      refine ⟨1503531433601225462471341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32075337250159476532721941 1503531433601225462471341)
                      ·
                        rfl

theorem cell23_2928117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2928117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928117 prefixEnd_2928117 := by exact prefixLift 2928117
  have htrace : WordTrace (prefixWord ++ tailWord_2928117) baseStart_2928117 baseEnd_2928117 := by
    simpa [prefixWord, tailWord_2928117, baseEnd_2928117] using wordTrace_append hprefix tailTrace_2928117
  have hstable : (prefixWord ++ tailWord_2928117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928117).length < 2 ^ (prefixWord ++ tailWord_2928117).sum := by decide
  have hdescent : baseEnd_2928117 < baseStart_2928117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928147 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 4]
def baseStart_2928147 : Nat := 118140960795 + 2928147 * 2 ^ 59
def prefixEnd_2928147 : Nat := 4983230072969 + 3 ^ 40 * 2928147 * 2
def baseEnd_2928147 : Nat := 1503546838020860345096203

theorem tailTrace_2928147 : CollatzResearch.WordTrace tailWord_2928147 prefixEnd_2928147 1503546838020860345096203 := by
  unfold tailWord_2928147
  simp only [CollatzResearch.WordTrace]
  refine ⟨106798294922830981538694695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71198863281887321025796463 106798294922830981538694695)
  ·
    refine ⟨160197442384246472308042043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106798294922830981538694695 160197442384246472308042043)
    ·
      refine ⟨240296163576369708462063065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160197442384246472308042043 240296163576369708462063065)
      ·
        refine ⟨180222122682277281346547299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240296163576369708462063065 180222122682277281346547299)
        ·
          refine ⟨270333184023415922019820949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180222122682277281346547299 270333184023415922019820949)
          ·
            refine ⟨12671868001097621344679107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 270333184023415922019820949 12671868001097621344679107)
            ·
              refine ⟨19007802001646432017018661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12671868001097621344679107 19007802001646432017018661)
              ·
                refine ⟨3563962875308706003190999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19007802001646432017018661 3563962875308706003190999)
                ·
                  refine ⟨5345944312963059004786499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563962875308706003190999 5345944312963059004786499)
                  ·
                    refine ⟨8018916469444588507179749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5345944312963059004786499 8018916469444588507179749)
                    ·
                      refine ⟨1503546838020860345096203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8018916469444588507179749 1503546838020860345096203)
                      ·
                        rfl

theorem cell23_2928147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 4].length) (baseStart_2928147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928147 prefixEnd_2928147 := by exact prefixLift 2928147
  have htrace : WordTrace (prefixWord ++ tailWord_2928147) baseStart_2928147 baseEnd_2928147 := by
    simpa [prefixWord, tailWord_2928147, baseEnd_2928147] using wordTrace_append hprefix tailTrace_2928147
  have hstable : (prefixWord ++ tailWord_2928147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928147).length < 2 ^ (prefixWord ++ tailWord_2928147).sum := by decide
  have hdescent : baseEnd_2928147 < baseStart_2928147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928157 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2928157 : Nat := 118140960795 + 2928157 * 2 ^ 59
def prefixEnd_2928157 : Nat := 4983230072969 + 3 ^ 40 * 2928157 * 2
def baseEnd_2928157 : Nat := 501183990942468435323719

theorem tailTrace_2928157 : CollatzResearch.WordTrace tailWord_2928157 prefixEnd_2928157 501183990942468435323719 := by
  unfold tailWord_2928157
  simp only [CollatzResearch.WordTrace]
  refine ⟨106798659652794753246558725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71199106435196502164372483 106798659652794753246558725)
  ·
    refine ⟨20024748684899016233729761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106798659652794753246558725 20024748684899016233729761)
    ·
      refine ⟨15018561513674262175297321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20024748684899016233729761 15018561513674262175297321)
      ·
        refine ⟨11263921135255696631472991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15018561513674262175297321 11263921135255696631472991)
        ·
          refine ⟨16895881702883544947209487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11263921135255696631472991 16895881702883544947209487)
          ·
            refine ⟨25343822554325317420814231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16895881702883544947209487 25343822554325317420814231)
            ·
              refine ⟨38015733831487976131221347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25343822554325317420814231 38015733831487976131221347)
              ·
                refine ⟨57023600747231964196832021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38015733831487976131221347 57023600747231964196832021)
                ·
                  refine ⟨2672981285026498321726501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57023600747231964196832021 2672981285026498321726501)
                  ·
                    refine ⟨501183990942468435323719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2672981285026498321726501 501183990942468435323719)
                    ·
                      rfl

theorem cell23_2928157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2928157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928157 prefixEnd_2928157 := by exact prefixLift 2928157
  have htrace : WordTrace (prefixWord ++ tailWord_2928157) baseStart_2928157 baseEnd_2928157 := by
    simpa [prefixWord, tailWord_2928157, baseEnd_2928157] using wordTrace_append hprefix tailTrace_2928157
  have hstable : (prefixWord ++ tailWord_2928157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928157).length < 2 ^ (prefixWord ++ tailWord_2928157).sum := by decide
  have hdescent : baseEnd_2928157 < baseStart_2928157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
