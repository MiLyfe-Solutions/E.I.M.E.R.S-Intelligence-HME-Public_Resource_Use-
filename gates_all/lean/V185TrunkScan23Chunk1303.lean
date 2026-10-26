import V185TrunkScan23Chunk1302

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7717721 : List Nat := [1, 2, 1, 2, 2, 4, 4, 7]
def baseStart_7717721 : Nat := 118140960795 + 7717721 * 2 ^ 59
def prefixEnd_7717721 : Nat := 4983230072969 + 3 ^ 40 * 7717721 * 2
def baseEnd_7717721 : Nat := 146774090011048300547939

theorem tailTrace_7717721 : CollatzResearch.WordTrace tailWord_7717721 prefixEnd_7717721 146774090011048300547939 := by
  unfold tailWord_7717721
  simp only [CollatzResearch.WordTrace]
  refine ⟨281488410073022373654057017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187658940048681582436038011 281488410073022373654057017)
  ·
    refine ⟨211116307554766780240542763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281488410073022373654057017 211116307554766780240542763)
    ·
      refine ⟨316674461332150170360814145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211116307554766780240542763 316674461332150170360814145)
      ·
        refine ⟨237505845999112627770610609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316674461332150170360814145 237505845999112627770610609)
        ·
          refine ⟨178129384499334470827957957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237505845999112627770610609 178129384499334470827957957)
          ·
            refine ⟨33399259593625213280242117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178129384499334470827957957 33399259593625213280242117)
            ·
              refine ⟨6262361173804727490045397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33399259593625213280242117 6262361173804727490045397)
              ·
                refine ⟨146774090011048300547939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6262361173804727490045397 146774090011048300547939)
                ·
                  rfl

theorem cell23_7717721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 7].length) (baseStart_7717721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717721 prefixEnd_7717721 := by exact prefixLift 7717721
  have htrace : WordTrace (prefixWord ++ tailWord_7717721) baseStart_7717721 baseEnd_7717721 := by
    simpa [prefixWord, tailWord_7717721, baseEnd_7717721] using wordTrace_append hprefix tailTrace_7717721
  have hstable : (prefixWord ++ tailWord_7717721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717721).length < 2 ^ (prefixWord ++ tailWord_7717721).sum := by decide
  have hdescent : baseEnd_7717721 < baseStart_7717721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717765 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 2, 1, 3]
def baseStart_7717765 : Nat := 118140960795 + 7717765 * 2 ^ 59
def prefixEnd_7717765 : Nat := 4983230072969 + 3 ^ 40 * 7717765 * 2
def baseEnd_7717765 : Nat := 3962923023447101942644151

theorem tailTrace_7717765 : CollatzResearch.WordTrace tailWord_7717765 prefixEnd_7717765 3962923023447101942644151 := by
  unfold tailWord_7717765
  simp only [CollatzResearch.WordTrace]
  refine ⟨281490014884862969168658749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187660009923241979445772499 281490014884862969168658749)
  ·
    refine ⟨105558755581823613438247031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281490014884862969168658749 105558755581823613438247031)
    ·
      refine ⟨158338133372735420157370547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105558755581823613438247031 158338133372735420157370547)
      ·
        refine ⟨237507200059103130236055821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158338133372735420157370547 237507200059103130236055821)
        ·
          refine ⟨89065200022163673838520933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237507200059103130236055821 89065200022163673838520933)
          ·
            refine ⟨16699725004155688844722675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89065200022163673838520933 16699725004155688844722675)
            ·
              refine ⟨25049587506233533267084013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16699725004155688844722675 25049587506233533267084013)
              ·
                refine ⟨9393595314837574975156505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25049587506233533267084013 9393595314837574975156505)
                ·
                  refine ⟨7045196486128181231367379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9393595314837574975156505 7045196486128181231367379)
                  ·
                    refine ⟨10567794729192271847051069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7045196486128181231367379 10567794729192271847051069)
                    ·
                      refine ⟨3962923023447101942644151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10567794729192271847051069 3962923023447101942644151)
                      ·
                        rfl

theorem cell23_7717765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_7717765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717765 prefixEnd_7717765 := by exact prefixLift 7717765
  have htrace : WordTrace (prefixWord ++ tailWord_7717765) baseStart_7717765 baseEnd_7717765 := by
    simpa [prefixWord, tailWord_7717765, baseEnd_7717765] using wordTrace_append hprefix tailTrace_7717765
  have hstable : (prefixWord ++ tailWord_7717765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717765).length < 2 ^ (prefixWord ++ tailWord_7717765).sum := by decide
  have hdescent : baseEnd_7717765 < baseStart_7717765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717782 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_7717782 : Nat := 118140960795 + 7717782 * 2 ^ 59
def prefixEnd_7717782 : Nat := 4983230072969 + 3 ^ 40 * 7717782 * 2
def baseEnd_7717782 : Nat := 3962931752618228376131573

theorem tailTrace_7717782 : CollatzResearch.WordTrace tailWord_7717782 prefixEnd_7717782 3962931752618228376131573 := by
  unfold tailWord_7717782
  simp only [CollatzResearch.WordTrace]
  refine ⟨17593164682862586317001725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187660423283867587381351733 17593164682862586317001725)
  ·
    refine ⟨6597436756073469868875647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17593164682862586317001725 6597436756073469868875647)
    ·
      refine ⟨9896155134110204803313471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6597436756073469868875647 9896155134110204803313471)
      ·
        refine ⟨14844232701165307204970207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9896155134110204803313471 14844232701165307204970207)
        ·
          refine ⟨22266349051747960807455311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14844232701165307204970207 22266349051747960807455311)
          ·
            refine ⟨33399523577621941211182967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22266349051747960807455311 33399523577621941211182967)
            ·
              refine ⟨50099285366432911816774451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33399523577621941211182967 50099285366432911816774451)
              ·
                refine ⟨75148928049649367725161677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50099285366432911816774451 75148928049649367725161677)
                ·
                  refine ⟨28180848018618512896935629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75148928049649367725161677 28180848018618512896935629)
                  ·
                    refine ⟨10567818006981942336350861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28180848018618512896935629 10567818006981942336350861)
                    ·
                      refine ⟨3962931752618228376131573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10567818006981942336350861 3962931752618228376131573)
                      ·
                        rfl

theorem cell23_7717782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_7717782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717782 prefixEnd_7717782 := by exact prefixLift 7717782
  have htrace : WordTrace (prefixWord ++ tailWord_7717782) baseStart_7717782 baseEnd_7717782 := by
    simpa [prefixWord, tailWord_7717782, baseEnd_7717782] using wordTrace_append hprefix tailTrace_7717782
  have hstable : (prefixWord ++ tailWord_7717782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717782).length < 2 ^ (prefixWord ++ tailWord_7717782).sum := by decide
  have hdescent : baseEnd_7717782 < baseStart_7717782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717801 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 4]
def baseStart_7717801 : Nat := 118140960795 + 7717801 * 2 ^ 59
def prefixEnd_7717801 : Nat := 4983230072969 + 3 ^ 40 * 7717801 * 2
def baseEnd_7717801 : Nat := 3962941508750663801793985

theorem tailTrace_7717801 : CollatzResearch.WordTrace tailWord_7717801 prefixEnd_7717801 3962941508750663801793985 := by
  unfold tailWord_7717801
  simp only [CollatzResearch.WordTrace]
  refine ⟨281491327912732547316969257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187660885275155031544646171 281491327912732547316969257)
  ·
    refine ⟨211118495934549410487726943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281491327912732547316969257 211118495934549410487726943)
    ·
      refine ⟨316677743901824115731590415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211118495934549410487726943 316677743901824115731590415)
      ·
        refine ⟨475016615852736173597385623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316677743901824115731590415 475016615852736173597385623)
        ·
          refine ⟨712524923779104260396078435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475016615852736173597385623 712524923779104260396078435)
          ·
            refine ⟨1068787385668656390594117653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712524923779104260396078435 1068787385668656390594117653)
            ·
              refine ⟨50099408703218268309099265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1068787385668656390594117653 50099408703218268309099265)
              ·
                refine ⟨37574556527413701231824449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50099408703218268309099265 37574556527413701231824449)
                ·
                  refine ⟨28180917395560275923868337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37574556527413701231824449 28180917395560275923868337)
                  ·
                    refine ⟨21135688046670206942901253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28180917395560275923868337 21135688046670206942901253)
                    ·
                      refine ⟨3962941508750663801793985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21135688046670206942901253 3962941508750663801793985)
                      ·
                        rfl

theorem cell23_7717801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_7717801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717801 prefixEnd_7717801 := by exact prefixLift 7717801
  have htrace : WordTrace (prefixWord ++ tailWord_7717801) baseStart_7717801 baseEnd_7717801 := by
    simpa [prefixWord, tailWord_7717801, baseEnd_7717801] using wordTrace_append hprefix tailTrace_7717801
  have hstable : (prefixWord ++ tailWord_7717801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717801).length < 2 ^ (prefixWord ++ tailWord_7717801).sum := by decide
  have hdescent : baseEnd_7717801 < baseStart_7717801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717822 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_7717822 : Nat := 118140960795 + 7717822 * 2 ^ 59
def prefixEnd_7717822 : Nat := 4983230072969 + 3 ^ 40 * 7717822 * 2
def baseEnd_7717822 : Nat := 3962952291844408219631389

theorem tailTrace_7717822 : CollatzResearch.WordTrace tailWord_7717822 prefixEnd_7717822 3962952291844408219631389 := by
  unfold tailWord_7717822
  simp only [CollatzResearch.WordTrace]
  refine ⟨35186511730707058487935465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187661395897104311935655813 35186511730707058487935465)
  ·
    refine ⟨26389883798030293865951599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35186511730707058487935465 26389883798030293865951599)
    ·
      refine ⟨39584825697045440798927399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26389883798030293865951599 39584825697045440798927399)
      ·
        refine ⟨59377238545568161198391099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39584825697045440798927399 59377238545568161198391099)
        ·
          refine ⟨89065857818352241797586649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59377238545568161198391099 89065857818352241797586649)
          ·
            refine ⟨66799393363764181348189987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89065857818352241797586649 66799393363764181348189987)
            ·
              refine ⟨100199090045646272022284981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66799393363764181348189987 100199090045646272022284981)
              ·
                refine ⟨9393664691779338002089217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100199090045646272022284981 9393664691779338002089217)
                ·
                  refine ⟨7045248518834503501566913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9393664691779338002089217 7045248518834503501566913)
                  ·
                    refine ⟨5283936389125877626175185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7045248518834503501566913 5283936389125877626175185)
                    ·
                      refine ⟨3962952291844408219631389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5283936389125877626175185 3962952291844408219631389)
                      ·
                        rfl

theorem cell23_7717822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_7717822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717822 prefixEnd_7717822 := by exact prefixLift 7717822
  have htrace : WordTrace (prefixWord ++ tailWord_7717822) baseStart_7717822 baseEnd_7717822 := by
    simpa [prefixWord, tailWord_7717822, baseEnd_7717822] using wordTrace_append hprefix tailTrace_7717822
  have hstable : (prefixWord ++ tailWord_7717822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717822).length < 2 ^ (prefixWord ++ tailWord_7717822).sum := by decide
  have hdescent : baseEnd_7717822 < baseStart_7717822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717841 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 1, 7]
def baseStart_7717841 : Nat := 118140960795 + 7717841 * 2 ^ 59
def prefixEnd_7717841 : Nat := 4983230072969 + 3 ^ 40 * 7717841 * 2
def baseEnd_7717841 : Nat := 1320987349325614548431267

theorem tailTrace_7717841 : CollatzResearch.WordTrace tailWord_7717841 prefixEnd_7717841 1320987349325614548431267 := by
  unfold tailWord_7717841
  simp only [CollatzResearch.WordTrace]
  refine ⟨281492786832587634148425377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187661857888391756098950251 281492786832587634148425377)
  ·
    refine ⟨211119590124440725611319033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281492786832587634148425377 211119590124440725611319033)
    ·
      refine ⟨158339692593330544208489275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211119590124440725611319033 158339692593330544208489275)
      ·
        refine ⟨237509538889995816312733913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158339692593330544208489275 237509538889995816312733913)
        ·
          refine ⟨178132154167496862234550435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237509538889995816312733913 178132154167496862234550435)
          ·
            refine ⟨267198231251245293351825653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178132154167496862234550435 267198231251245293351825653)
            ·
              refine ⟨25049834179804246251733655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267198231251245293351825653 25049834179804246251733655)
              ·
                refine ⟨37574751269706369377600483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25049834179804246251733655 37574751269706369377600483)
                ·
                  refine ⟨56362126904559554066400725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37574751269706369377600483 56362126904559554066400725)
                  ·
                    refine ⟨1320987349325614548431267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56362126904559554066400725 1320987349325614548431267)
                    ·
                      rfl

theorem cell23_7717841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_7717841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717841 prefixEnd_7717841 := by exact prefixLift 7717841
  have htrace : WordTrace (prefixWord ++ tailWord_7717841) baseStart_7717841 baseEnd_7717841 := by
    simpa [prefixWord, tailWord_7717841, baseEnd_7717841] using wordTrace_append hprefix tailTrace_7717841
  have hstable : (prefixWord ++ tailWord_7717841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717841).length < 2 ^ (prefixWord ++ tailWord_7717841).sum := by decide
  have hdescent : baseEnd_7717841 < baseStart_7717841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717922 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_7717922 : Nat := 118140960795 + 7717922 * 2 ^ 59
def prefixEnd_7717922 : Nat := 4983230072969 + 3 ^ 40 * 7717922 * 2
def baseEnd_7717922 : Nat := 1321001213303285942793643

theorem tailTrace_7717922 : CollatzResearch.WordTrace tailWord_7717922 prefixEnd_7717922 1321001213303285942793643 := by
  unfold tailWord_7717922
  simp only [CollatzResearch.WordTrace]
  refine ⟨70373935286323546245531005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187663827430196123321416013 70373935286323546245531005)
  ·
    refine ⟨26390225732371329842074127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70373935286323546245531005 26390225732371329842074127)
    ·
      refine ⟨39585338598556994763111191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26390225732371329842074127 39585338598556994763111191)
      ·
        refine ⟨59378007897835492144666787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39585338598556994763111191 59378007897835492144666787)
        ·
          refine ⟨89067011846753238217000181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59378007897835492144666787 89067011846753238217000181)
          ·
            refine ⟨8350032360633116082843767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89067011846753238217000181 8350032360633116082843767)
            ·
              refine ⟨12525048540949674124265651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8350032360633116082843767 12525048540949674124265651)
              ·
                refine ⟨18787572811424511186398477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12525048540949674124265651 18787572811424511186398477)
                ·
                  refine ⟨7045339804284191694899429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18787572811424511186398477 7045339804284191694899429)
                  ·
                    refine ⟨1321001213303285942793643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7045339804284191694899429 1321001213303285942793643)
                    ·
                      rfl

theorem cell23_7717922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_7717922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717922 prefixEnd_7717922 := by exact prefixLift 7717922
  have htrace : WordTrace (prefixWord ++ tailWord_7717922) baseStart_7717922 baseEnd_7717922 := by
    simpa [prefixWord, tailWord_7717922, baseEnd_7717922] using wordTrace_append hprefix tailTrace_7717922
  have hstable : (prefixWord ++ tailWord_7717922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717922).length < 2 ^ (prefixWord ++ tailWord_7717922).sum := by decide
  have hdescent : baseEnd_7717922 < baseStart_7717922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717972 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_7717972 : Nat := 118140960795 + 7717972 * 2 ^ 59
def prefixEnd_7717972 : Nat := 4983230072969 + 3 ^ 40 * 7717972 * 2
def baseEnd_7717972 : Nat := 3963029313942582632755699

theorem tailTrace_7717972 : CollatzResearch.WordTrace tailWord_7717972 prefixEnd_7717972 3963029313942582632755699 := by
  unfold tailWord_7717972
  simp only [CollatzResearch.WordTrace]
  refine ⟨140748782397556521760722085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187665043196742029014296113 140748782397556521760722085)
  ·
    refine ⟨26390396699541847830135391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140748782397556521760722085 26390396699541847830135391)
    ·
      refine ⟨39585595049312771745203087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26390396699541847830135391 39585595049312771745203087)
      ·
        refine ⟨59378392573969157617804631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39585595049312771745203087 59378392573969157617804631)
        ·
          refine ⟨89067588860953736426706947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59378392573969157617804631 89067588860953736426706947)
          ·
            refine ⟨133601383291430604640060421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89067588860953736426706947 133601383291430604640060421)
            ·
              refine ⟨25050259367143238370011329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133601383291430604640060421 25050259367143238370011329)
              ·
                refine ⟨18787694525357428777508497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25050259367143238370011329 18787694525357428777508497)
                ·
                  refine ⟨14090770894018071583131373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18787694525357428777508497 14090770894018071583131373)
                  ·
                    refine ⟨5284039085256776843674265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14090770894018071583131373 5284039085256776843674265)
                    ·
                      refine ⟨3963029313942582632755699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5284039085256776843674265 3963029313942582632755699)
                      ·
                        rfl

theorem cell23_7717972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_7717972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717972 prefixEnd_7717972 := by exact prefixLift 7717972
  have htrace : WordTrace (prefixWord ++ tailWord_7717972) baseStart_7717972 baseEnd_7717972 := by
    simpa [prefixWord, tailWord_7717972, baseEnd_7717972] using wordTrace_append hprefix tailTrace_7717972
  have hstable : (prefixWord ++ tailWord_7717972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717972).length < 2 ^ (prefixWord ++ tailWord_7717972).sum := by decide
  have hdescent : baseEnd_7717972 < baseStart_7717972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717988 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_7717988 : Nat := 118140960795 + 7717988 * 2 ^ 59
def prefixEnd_7717988 : Nat := 4983230072969 + 3 ^ 40 * 7717988 * 2
def baseEnd_7717988 : Nat := 3963037529633054570155625

theorem tailTrace_7717988 : CollatzResearch.WordTrace tailWord_7717988 prefixEnd_7717988 3963037529633054570155625 := by
  unfold tailWord_7717988
  simp only [CollatzResearch.WordTrace]
  refine ⟨140749074181527539127013309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187665432242036718836017745 140749074181527539127013309)
  ·
    refine ⟨52780902818072827172629991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140749074181527539127013309 52780902818072827172629991)
    ·
      refine ⟨79171354227109240758944987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52780902818072827172629991 79171354227109240758944987)
      ·
        refine ⟨118757031340663861138417481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79171354227109240758944987 118757031340663861138417481)
        ·
          refine ⟨89067773505497895853813111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118757031340663861138417481 89067773505497895853813111)
          ·
            refine ⟨133601660258246843780719667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89067773505497895853813111 133601660258246843780719667)
            ·
              refine ⟨200402490387370265671079501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133601660258246843780719667 200402490387370265671079501)
              ·
                refine ⟨75150933895263849626654813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200402490387370265671079501 75150933895263849626654813)
                ·
                  refine ⟨28181600210723943609995555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75150933895263849626654813 28181600210723943609995555)
                  ·
                    refine ⟨42272400316085915414993333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28181600210723943609995555 42272400316085915414993333)
                    ·
                      refine ⟨3963037529633054570155625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42272400316085915414993333 3963037529633054570155625)
                      ·
                        rfl

theorem cell23_7717988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_7717988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717988 prefixEnd_7717988 := by exact prefixLift 7717988
  have htrace : WordTrace (prefixWord ++ tailWord_7717988) baseStart_7717988 baseEnd_7717988 := by
    simpa [prefixWord, tailWord_7717988, baseEnd_7717988] using wordTrace_append hprefix tailTrace_7717988
  have hstable : (prefixWord ++ tailWord_7717988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717988).length < 2 ^ (prefixWord ++ tailWord_7717988).sum := by decide
  have hdescent : baseEnd_7717988 < baseStart_7717988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718046 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_7718046 : Nat := 118140960795 + 7718046 * 2 ^ 59
def prefixEnd_7718046 : Nat := 4983230072969 + 3 ^ 40 * 7718046 * 2
def baseEnd_7718046 : Nat := 1321022437170338447743453

theorem tailTrace_7718046 : CollatzResearch.WordTrace tailWord_7718046 prefixEnd_7718046 1321022437170338447743453 := by
  unfold tailWord_7718046
  simp only [CollatzResearch.WordTrace]
  refine ⟨35187532974605619269954749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187666842531229969439758661 35187532974605619269954749)
  ·
    refine ⟨13195324865477107226233031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35187532974605619269954749 13195324865477107226233031)
    ·
      refine ⟨19792987298215660839349547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13195324865477107226233031 19792987298215660839349547)
      ·
        refine ⟨29689480947323491259024321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19792987298215660839349547 29689480947323491259024321)
        ·
          refine ⟨22267110710492618444268241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29689480947323491259024321 22267110710492618444268241)
          ·
            refine ⟨16700333032869463833201181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22267110710492618444268241 16700333032869463833201181)
            ·
              refine ⟨6262624887326048937450443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16700333032869463833201181 6262624887326048937450443)
              ·
                refine ⟨9393937330989073406175665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6262624887326048937450443 9393937330989073406175665)
                ·
                  refine ⟨7045452998241805054631749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9393937330989073406175665 7045452998241805054631749)
                  ·
                    refine ⟨1321022437170338447743453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7045452998241805054631749 1321022437170338447743453)
                    ·
                      rfl

theorem cell23_7718046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_7718046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718046 prefixEnd_7718046 := by exact prefixLift 7718046
  have htrace : WordTrace (prefixWord ++ tailWord_7718046) baseStart_7718046 baseEnd_7718046 := by
    simpa [prefixWord, tailWord_7718046, baseEnd_7718046] using wordTrace_append hprefix tailTrace_7718046
  have hstable : (prefixWord ++ tailWord_7718046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718046).length < 2 ^ (prefixWord ++ tailWord_7718046).sum := by decide
  have hdescent : baseEnd_7718046 < baseStart_7718046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718052 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_7718052 : Nat := 118140960795 + 7718052 * 2 ^ 59
def prefixEnd_7718052 : Nat := 4983230072969 + 3 ^ 40 * 7718052 * 2
def baseEnd_7718052 : Nat := 3963070392394942319755331

theorem tailTrace_7718052 : CollatzResearch.WordTrace tailWord_7718052 prefixEnd_7718052 3963070392394942319755331 := by
  unfold tailWord_7718052
  simp only [CollatzResearch.WordTrace]
  refine ⟨140750241317411608592178205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187666988423215478122904273 140750241317411608592178205)
  ·
    refine ⟨52781340494029353222066827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140750241317411608592178205 52781340494029353222066827)
    ·
      refine ⟨79172010741044029833100241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52781340494029353222066827 79172010741044029833100241)
      ·
        refine ⟨59379008055783022374825181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79172010741044029833100241 59379008055783022374825181)
        ·
          refine ⟨22267128020918633390559443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59379008055783022374825181 22267128020918633390559443)
          ·
            refine ⟨33400692031377950085839165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22267128020918633390559443 33400692031377950085839165)
            ·
              refine ⟨12525259511766731282189687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33400692031377950085839165 12525259511766731282189687)
              ·
                refine ⟨18787889267650096923284531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12525259511766731282189687 18787889267650096923284531)
                ·
                  refine ⟨28181833901475145384926797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18787889267650096923284531 28181833901475145384926797)
                  ·
                    refine ⟨10568187713053179519347549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28181833901475145384926797 10568187713053179519347549)
                    ·
                      refine ⟨3963070392394942319755331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10568187713053179519347549 3963070392394942319755331)
                      ·
                        rfl

theorem cell23_7718052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_7718052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718052 prefixEnd_7718052 := by exact prefixLift 7718052
  have htrace : WordTrace (prefixWord ++ tailWord_7718052) baseStart_7718052 baseEnd_7718052 := by
    simpa [prefixWord, tailWord_7718052, baseEnd_7718052] using wordTrace_append hprefix tailTrace_7718052
  have hstable : (prefixWord ++ tailWord_7718052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718052).length < 2 ^ (prefixWord ++ tailWord_7718052).sum := by decide
  have hdescent : baseEnd_7718052 < baseStart_7718052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718065 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7718065 : Nat := 118140960795 + 7718065 * 2 ^ 59
def prefixEnd_7718065 : Nat := 4983230072969 + 3 ^ 40 * 7718065 * 2
def baseEnd_7718065 : Nat := 3963077067643450768892771

theorem tailTrace_7718065 : CollatzResearch.WordTrace tailWord_7718065 prefixEnd_7718065 3963077067643450768892771 := by
  unfold tailWord_7718065
  simp only [CollatzResearch.WordTrace]
  refine ⟨281500956783776120404579649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187667304522517413603053099 281500956783776120404579649)
  ·
    refine ⟨211125717587832090303434737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281500956783776120404579649 211125717587832090303434737)
    ·
      refine ⟨158344288190874067727576053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211125717587832090303434737 158344288190874067727576053)
      ·
        refine ⟨14844777017894443849460255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158344288190874067727576053 14844777017894443849460255)
        ·
          refine ⟨22267165526841665774190383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14844777017894443849460255 22267165526841665774190383)
          ·
            refine ⟨33400748290262498661285575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22267165526841665774190383 33400748290262498661285575)
            ·
              refine ⟨50101122435393747991928363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33400748290262498661285575 50101122435393747991928363)
              ·
                refine ⟨75151683653090621987892545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50101122435393747991928363 75151683653090621987892545)
                ·
                  refine ⟨56363762739817966490919409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75151683653090621987892545 56363762739817966490919409)
                  ·
                    refine ⟨42272822054863474868189557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56363762739817966490919409 42272822054863474868189557)
                    ·
                      refine ⟨3963077067643450768892771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42272822054863474868189557 3963077067643450768892771)
                      ·
                        rfl

theorem cell23_7718065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7718065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718065 prefixEnd_7718065 := by exact prefixLift 7718065
  have htrace : WordTrace (prefixWord ++ tailWord_7718065) baseStart_7718065 baseEnd_7718065 := by
    simpa [prefixWord, tailWord_7718065, baseEnd_7718065] using wordTrace_append hprefix tailTrace_7718065
  have hstable : (prefixWord ++ tailWord_7718065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718065).length < 2 ^ (prefixWord ++ tailWord_7718065).sum := by decide
  have hdescent : baseEnd_7718065 < baseStart_7718065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718155 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 5]
def baseStart_7718155 : Nat := 118140960795 + 7718155 * 2 ^ 59
def prefixEnd_7718155 : Nat := 4983230072969 + 3 ^ 40 * 7718155 * 2
def baseEnd_7718155 : Nat := 3963123280902355416767357

theorem tailTrace_7718155 : CollatzResearch.WordTrace tailWord_7718155 prefixEnd_7718155 3963123280902355416767357 := by
  unfold tailWord_7718155
  simp only [CollatzResearch.WordTrace]
  refine ⟨281504239353450065775355919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187669492902300043850237279 281504239353450065775355919)
  ·
    refine ⟨422256359030175098663033879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281504239353450065775355919 422256359030175098663033879)
    ·
      refine ⟨633384538545262647994550819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422256359030175098663033879 633384538545262647994550819)
      ·
        refine ⟨950076807817893971991826229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633384538545262647994550819 950076807817893971991826229)
        ·
          refine ⟨89069700732927559874233709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 950076807817893971991826229 89069700732927559874233709)
          ·
            refine ⟨33401137774847834952837641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89069700732927559874233709 33401137774847834952837641)
            ·
              refine ⟨25050853331135876214628231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33401137774847834952837641 25050853331135876214628231)
              ·
                refine ⟨37576279996703814321942347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25050853331135876214628231 37576279996703814321942347)
                ·
                  refine ⟨56364419995055721482913521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37576279996703814321942347 56364419995055721482913521)
                  ·
                    refine ⟨42273314996291791112185141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56364419995055721482913521 42273314996291791112185141)
                    ·
                      refine ⟨3963123280902355416767357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42273314996291791112185141 3963123280902355416767357)
                      ·
                        rfl

theorem cell23_7718155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 5].length) (baseStart_7718155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718155 prefixEnd_7718155 := by exact prefixLift 7718155
  have htrace : WordTrace (prefixWord ++ tailWord_7718155) baseStart_7718155 baseEnd_7718155 := by
    simpa [prefixWord, tailWord_7718155, baseEnd_7718155] using wordTrace_append hprefix tailTrace_7718155
  have hstable : (prefixWord ++ tailWord_7718155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718155).length < 2 ^ (prefixWord ++ tailWord_7718155).sum := by decide
  have hdescent : baseEnd_7718155 < baseStart_7718155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718165 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_7718165 : Nat := 118140960795 + 7718165 * 2 ^ 59
def prefixEnd_7718165 : Nat := 4983230072969 + 3 ^ 40 * 7718165 * 2
def baseEnd_7718165 : Nat := 3963128415708900377642311

theorem tailTrace_7718165 : CollatzResearch.WordTrace tailWord_7718165 prefixEnd_7718165 3963128415708900377642311 := by
  unfold tailWord_7718165
  simp only [CollatzResearch.WordTrace]
  refine ⟨281504604083413837483219949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187669736055609224988813299 281504604083413837483219949)
  ·
    refine ⟨105564226531280189056207481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281504604083413837483219949 105564226531280189056207481)
    ·
      refine ⟨79173169898460141792155611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105564226531280189056207481 79173169898460141792155611)
      ·
        refine ⟨118759754847690212688233417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79173169898460141792155611 118759754847690212688233417)
        ·
          refine ⟨89069816135767659516175063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118759754847690212688233417 89069816135767659516175063)
          ·
            refine ⟨133604724203651489274262595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89069816135767659516175063 133604724203651489274262595)
            ·
              refine ⟨200407086305477233911393893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133604724203651489274262595 200407086305477233911393893)
              ·
                refine ⟨37576328682276981358386355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200407086305477233911393893 37576328682276981358386355)
                ·
                  refine ⟨56364493023415472037579533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37576328682276981358386355 56364493023415472037579533)
                  ·
                    refine ⟨21136684883780802014092325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56364493023415472037579533 21136684883780802014092325)
                    ·
                      refine ⟨3963128415708900377642311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21136684883780802014092325 3963128415708900377642311)
                      ·
                        rfl

theorem cell23_7718165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_7718165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718165 prefixEnd_7718165 := by exact prefixLift 7718165
  have htrace : WordTrace (prefixWord ++ tailWord_7718165) baseStart_7718165 baseEnd_7718165 := by
    simpa [prefixWord, tailWord_7718165, baseEnd_7718165] using wordTrace_append hprefix tailTrace_7718165
  have hstable : (prefixWord ++ tailWord_7718165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718165).length < 2 ^ (prefixWord ++ tailWord_7718165).sum := by decide
  have hdescent : baseEnd_7718165 < baseStart_7718165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718195 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 6]
def baseStart_7718195 : Nat := 118140960795 + 7718195 * 2 ^ 59
def prefixEnd_7718195 : Nat := 4983230072969 + 3 ^ 40 * 7718195 * 2
def baseEnd_7718195 : Nat := 3963143820128535260267173

theorem tailTrace_7718195 : CollatzResearch.WordTrace tailWord_7718195 prefixEnd_7718195 3963143820128535260267173 := by
  unfold tailWord_7718195
  simp only [CollatzResearch.WordTrace]
  refine ⟨281505698273305152606812039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187670465515536768404541359 281505698273305152606812039)
  ·
    refine ⟨422258547409957728910218059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281505698273305152606812039 422258547409957728910218059)
    ·
      refine ⟨633387821114936593365327089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422258547409957728910218059 633387821114936593365327089)
      ·
        refine ⟨475040865836202445023995317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633387821114936593365327089 475040865836202445023995317)
        ·
          refine ⟨44535081172143979220999561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 475040865836202445023995317 44535081172143979220999561)
          ·
            refine ⟨33401310879107984415749671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44535081172143979220999561 33401310879107984415749671)
            ·
              refine ⟨50101966318661976623624507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33401310879107984415749671 50101966318661976623624507)
              ·
                refine ⟨75152949477992964935436761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50101966318661976623624507 75152949477992964935436761)
                ·
                  refine ⟨56364712108494723701577571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75152949477992964935436761 56364712108494723701577571)
                  ·
                    refine ⟨84547068162742085552366357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56364712108494723701577571 84547068162742085552366357)
                    ·
                      refine ⟨3963143820128535260267173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84547068162742085552366357 3963143820128535260267173)
                      ·
                        rfl

theorem cell23_7718195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_7718195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718195 prefixEnd_7718195 := by exact prefixLift 7718195
  have htrace : WordTrace (prefixWord ++ tailWord_7718195) baseStart_7718195 baseEnd_7718195 := by
    simpa [prefixWord, tailWord_7718195, baseEnd_7718195] using wordTrace_append hprefix tailTrace_7718195
  have hstable : (prefixWord ++ tailWord_7718195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718195).length < 2 ^ (prefixWord ++ tailWord_7718195).sum := by decide
  have hdescent : baseEnd_7718195 < baseStart_7718195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718202 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3]
def baseStart_7718202 : Nat := 118140960795 + 7718202 * 2 ^ 59
def prefixEnd_7718202 : Nat := 4983230072969 + 3 ^ 40 * 7718202 * 2
def baseEnd_7718202 : Nat := 3963147414493116732879641

theorem tailTrace_7718202 : CollatzResearch.WordTrace tailWord_7718202 prefixEnd_7718202 3963147414493116732879641 := by
  unfold tailWord_7718202
  simp only [CollatzResearch.WordTrace]
  refine ⟨70376488396069948200579215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187670635722853195201544573 70376488396069948200579215)
  ·
    refine ⟨105564732594104922300868823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70376488396069948200579215 105564732594104922300868823)
    ·
      refine ⟨158347098891157383451303235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105564732594104922300868823 158347098891157383451303235)
      ·
        refine ⟨237520648336736075176954853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158347098891157383451303235 237520648336736075176954853)
        ·
          refine ⟨44535121563138014095679035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237520648336736075176954853 44535121563138014095679035)
          ·
            refine ⟨66802682344707021143518553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44535121563138014095679035 66802682344707021143518553)
            ·
              refine ⟨50102011758530265857638915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66802682344707021143518553 50102011758530265857638915)
              ·
                refine ⟨75153017637795398786458373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50102011758530265857638915 75153017637795398786458373)
                ·
                  refine ⟨14091190807086637272460945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75153017637795398786458373 14091190807086637272460945)
                  ·
                    refine ⟨10568393105314977954345709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14091190807086637272460945 10568393105314977954345709)
                    ·
                      refine ⟨3963147414493116732879641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10568393105314977954345709 3963147414493116732879641)
                      ·
                        rfl

theorem cell23_7718202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_7718202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718202 prefixEnd_7718202 := by exact prefixLift 7718202
  have htrace : WordTrace (prefixWord ++ tailWord_7718202) baseStart_7718202 baseEnd_7718202 := by
    simpa [prefixWord, tailWord_7718202, baseEnd_7718202] using wordTrace_append hprefix tailTrace_7718202
  have hstable : (prefixWord ++ tailWord_7718202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718202).length < 2 ^ (prefixWord ++ tailWord_7718202).sum := by decide
  have hdescent : baseEnd_7718202 < baseStart_7718202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718209 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 3, 4]
def baseStart_7718209 : Nat := 118140960795 + 7718209 * 2 ^ 59
def prefixEnd_7718209 : Nat := 4983230072969 + 3 ^ 40 * 7718209 * 2
def baseEnd_7718209 : Nat := 1321050336285899401830703

theorem tailTrace_7718209 : CollatzResearch.WordTrace tailWord_7718209 prefixEnd_7718209 1321050336285899401830703 := by
  unfold tailWord_7718209
  simp only [CollatzResearch.WordTrace]
  refine ⟨281506208895254432997821681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187670805930169621998547787 281506208895254432997821681)
  ·
    refine ⟨211129656671440824748366261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281506208895254432997821681 211129656671440824748366261)
    ·
      refine ⟨19793405312947577320159337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211129656671440824748366261 19793405312947577320159337)
      ·
        refine ⟨14845053984710682990119503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19793405312947577320159337 14845053984710682990119503)
        ·
          refine ⟨22267580977066024485179255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14845053984710682990119503 22267580977066024485179255)
          ·
            refine ⟨33401371465599036727768883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22267580977066024485179255 33401371465599036727768883)
            ·
              refine ⟨50102057198398555091653325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33401371465599036727768883 50102057198398555091653325)
              ·
                refine ⟨18788271449399458159369997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50102057198398555091653325 18788271449399458159369997)
                ·
                  refine ⟨7045601793524796809763749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18788271449399458159369997 7045601793524796809763749)
                  ·
                    refine ⟨1321050336285899401830703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7045601793524796809763749 1321050336285899401830703)
                    ·
                      rfl

theorem cell23_7718209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_7718209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718209 prefixEnd_7718209 := by exact prefixLift 7718209
  have htrace : WordTrace (prefixWord ++ tailWord_7718209) baseStart_7718209 baseEnd_7718209 := by
    simpa [prefixWord, tailWord_7718209, baseEnd_7718209] using wordTrace_append hprefix tailTrace_7718209
  have hstable : (prefixWord ++ tailWord_7718209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718209).length < 2 ^ (prefixWord ++ tailWord_7718209).sum := by decide
  have hdescent : baseEnd_7718209 < baseStart_7718209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718225 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_7718225 : Nat := 118140960795 + 7718225 * 2 ^ 59
def prefixEnd_7718225 : Nat := 4983230072969 + 3 ^ 40 * 7718225 * 2
def baseEnd_7718225 : Nat := 3963159224548170142892035

theorem tailTrace_7718225 : CollatzResearch.WordTrace tailWord_7718225 prefixEnd_7718225 3963159224548170142892035 := by
  unfold tailWord_7718225
  simp only [CollatzResearch.WordTrace]
  refine ⟨281506792463196467730404129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187671194975464311820269419 281506792463196467730404129)
  ·
    refine ⟨211130094347397350797803097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281506792463196467730404129 211130094347397350797803097)
    ·
      refine ⟨158347570760548013098352323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211130094347397350797803097 158347570760548013098352323)
      ·
        refine ⟨237521356140822019647528485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158347570760548013098352323 237521356140822019647528485)
        ·
          refine ⟨44535254276404128683911591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237521356140822019647528485 44535254276404128683911591)
          ·
            refine ⟨66802881414606193025867387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44535254276404128683911591 66802881414606193025867387)
            ·
              refine ⟨100204322121909289538801081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66802881414606193025867387 100204322121909289538801081)
              ·
                refine ⟨75153241591431967154100811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100204322121909289538801081 75153241591431967154100811)
                ·
                  refine ⟨112729862387147950731151217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75153241591431967154100811 112729862387147950731151217)
                  ·
                    refine ⟨84547396790360963048363413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112729862387147950731151217 84547396790360963048363413)
                    ·
                      refine ⟨3963159224548170142892035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84547396790360963048363413 3963159224548170142892035)
                      ·
                        rfl

theorem cell23_7718225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_7718225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718225 prefixEnd_7718225 := by exact prefixLift 7718225
  have htrace : WordTrace (prefixWord ++ tailWord_7718225) baseStart_7718225 baseEnd_7718225 := by
    simpa [prefixWord, tailWord_7718225, baseEnd_7718225] using wordTrace_append hprefix tailTrace_7718225
  have hstable : (prefixWord ++ tailWord_7718225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718225).length < 2 ^ (prefixWord ++ tailWord_7718225).sum := by decide
  have hdescent : baseEnd_7718225 < baseStart_7718225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718273 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 6]
def baseStart_7718273 : Nat := 118140960795 + 7718273 * 2 ^ 59
def prefixEnd_7718273 : Nat := 4983230072969 + 3 ^ 40 * 7718273 * 2
def baseEnd_7718273 : Nat := 440353763513287328343535

theorem tailTrace_7718273 : CollatzResearch.WordTrace tailWord_7718273 prefixEnd_7718273 440353763513287328343535 := by
  unfold tailWord_7718273
  simp only [CollatzResearch.WordTrace]
  refine ⟨281508543167022571928151473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187672362111348381285434315 281508543167022571928151473)
  ·
    refine ⟨211131407375266928946113605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281508543167022571928151473 211131407375266928946113605)
    ·
      refine ⟨39587138882862549177396301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211131407375266928946113605 39587138882862549177396301)
      ·
        refine ⟨14845177081073455941523613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39587138882862549177396301 14845177081073455941523613)
        ·
          refine ⟨5566941405402545978071355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14845177081073455941523613 5566941405402545978071355)
          ·
            refine ⟨8350412108103818967107033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5566941405402545978071355 8350412108103818967107033)
            ·
              refine ⟨6262809081077864225330275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8350412108103818967107033 6262809081077864225330275)
              ·
                refine ⟨9394213621616796337995413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6262809081077864225330275 9394213621616796337995413)
                ·
                  refine ⟨440353763513287328343535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9394213621616796337995413 440353763513287328343535)
                  ·
                    rfl

theorem cell23_7718273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 6].length) (baseStart_7718273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718273 prefixEnd_7718273 := by exact prefixLift 7718273
  have htrace : WordTrace (prefixWord ++ tailWord_7718273) baseStart_7718273 baseEnd_7718273 := by
    simpa [prefixWord, tailWord_7718273, baseEnd_7718273] using wordTrace_append hprefix tailTrace_7718273
  have hstable : (prefixWord ++ tailWord_7718273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718273).length < 2 ^ (prefixWord ++ tailWord_7718273).sum := by decide
  have hdescent : baseEnd_7718273 < baseStart_7718273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718312 : List Nat := [2, 1, 6, 1, 13]
def baseStart_7718312 : Nat := 118140960795 + 7718312 * 2 ^ 59
def prefixEnd_7718312 : Nat := 4983230072969 + 3 ^ 40 * 7718312 * 2
def baseEnd_7718312 : Nat := 5436493686371894790815

theorem tailTrace_7718312 : CollatzResearch.WordTrace tailWord_7718312 prefixEnd_7718312 5436493686371894790815 := by
  unfold tailWord_7718312
  simp only [CollatzResearch.WordTrace]
  refine ⟨140754982806940640794410595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187673310409254187725880793 140754982806940640794410595)
  ·
    refine ⟨211132474210410961191615893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140754982806940640794410595 211132474210410961191615893)
    ·
      refine ⟨9896834728613013805856995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211132474210410961191615893 9896834728613013805856995)
      ·
        refine ⟨14845252092919520708785493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9896834728613013805856995 14845252092919520708785493)
        ·
          refine ⟨5436493686371894790815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 14845252092919520708785493 5436493686371894790815)
          ·
            rfl

theorem cell23_7718312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 13].length) (baseStart_7718312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718312 prefixEnd_7718312 := by exact prefixLift 7718312
  have htrace : WordTrace (prefixWord ++ tailWord_7718312) baseStart_7718312 baseEnd_7718312 := by
    simpa [prefixWord, tailWord_7718312, baseEnd_7718312] using wordTrace_append hprefix tailTrace_7718312
  have hstable : (prefixWord ++ tailWord_7718312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718312).length < 2 ^ (prefixWord ++ tailWord_7718312).sum := by decide
  have hdescent : baseEnd_7718312 < baseStart_7718312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718315 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 6]
def baseStart_7718315 : Nat := 118140960795 + 7718315 * 2 ^ 59
def prefixEnd_7718315 : Nat := 4983230072969 + 3 ^ 40 * 7718315 * 2
def baseEnd_7718315 : Nat := 3963205437807074790766621

theorem tailTrace_7718315 : CollatzResearch.WordTrace tailWord_7718315 prefixEnd_7718315 3963205437807074790766621 := by
  unfold tailWord_7718315
  simp only [CollatzResearch.WordTrace]
  refine ⟨281510075032870413101180399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187673383355246942067453599 281510075032870413101180399)
  ·
    refine ⟨422265112549305619651770599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281510075032870413101180399 422265112549305619651770599)
    ·
      refine ⟨633397668823958429477655899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422265112549305619651770599 633397668823958429477655899)
      ·
        refine ⟨950096503235937644216483849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633397668823958429477655899 950096503235937644216483849)
        ·
          refine ⟨712572377426953233162362887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950096503235937644216483849 712572377426953233162362887)
          ·
            refine ⟨1068858566140429849743544331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712572377426953233162362887 1068858566140429849743544331)
            ·
              refine ⟨1603287849210644774615316497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068858566140429849743544331 1603287849210644774615316497)
              ·
                refine ⟨1202465886907983580961487373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1603287849210644774615316497 1202465886907983580961487373)
                ·
                  refine ⟨450924707590493842860557765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202465886907983580961487373 450924707590493842860557765)
                  ·
                    refine ⟨84548382673217595536354581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 450924707590493842860557765 84548382673217595536354581)
                    ·
                      refine ⟨3963205437807074790766621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84548382673217595536354581 3963205437807074790766621)
                      ·
                        rfl

theorem cell23_7718315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_7718315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718315 prefixEnd_7718315 := by exact prefixLift 7718315
  have htrace : WordTrace (prefixWord ++ tailWord_7718315) baseStart_7718315 baseEnd_7718315 := by
    simpa [prefixWord, tailWord_7718315, baseEnd_7718315] using wordTrace_append hprefix tailTrace_7718315
  have hstable : (prefixWord ++ tailWord_7718315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718315).length < 2 ^ (prefixWord ++ tailWord_7718315).sum := by decide
  have hdescent : baseEnd_7718315 < baseStart_7718315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718317 : List Nat := [1, 5, 2, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_7718317 : Nat := 118140960795 + 7718317 * 2 ^ 59
def prefixEnd_7718317 : Nat := 4983230072969 + 3 ^ 40 * 7718317 * 2
def baseEnd_7718317 : Nat := 3963206464768383782941613

theorem tailTrace_7718317 : CollatzResearch.WordTrace tailWord_7718317 prefixEnd_7718317 3963206464768383782941613 := by
  unfold tailWord_7718317
  simp only [CollatzResearch.WordTrace]
  refine ⟨281510147978863167442753205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187673431985908778295168803 281510147978863167442753205)
  ·
    refine ⟨26391576373018421947758113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281510147978863167442753205 26391576373018421947758113)
    ·
      refine ⟨19793682279763816460818585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26391576373018421947758113 19793682279763816460818585)
      ·
        refine ⟨14845261709822862345613939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19793682279763816460818585 14845261709822862345613939)
        ·
          refine ⟨22267892564734293518420909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14845261709822862345613939 22267892564734293518420909)
          ·
            refine ⟨8350459711775360069407841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22267892564734293518420909 8350459711775360069407841)
            ·
              refine ⟨6262844783831520052055881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8350459711775360069407841 6262844783831520052055881)
              ·
                refine ⟨4697133587873640039041911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6262844783831520052055881 4697133587873640039041911)
                ·
                  refine ⟨7045700381810460058562867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697133587873640039041911 7045700381810460058562867)
                  ·
                    refine ⟨10568550572715690087844301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7045700381810460058562867 10568550572715690087844301)
                    ·
                      refine ⟨3963206464768383782941613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10568550572715690087844301 3963206464768383782941613)
                      ·
                        rfl

theorem cell23_7718317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_7718317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718317 prefixEnd_7718317 := by exact prefixLift 7718317
  have htrace : WordTrace (prefixWord ++ tailWord_7718317) baseStart_7718317 baseEnd_7718317 := by
    simpa [prefixWord, tailWord_7718317, baseEnd_7718317] using wordTrace_append hprefix tailTrace_7718317
  have hstable : (prefixWord ++ tailWord_7718317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718317).length < 2 ^ (prefixWord ++ tailWord_7718317).sum := by decide
  have hdescent : baseEnd_7718317 < baseStart_7718317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718329 : List Nat := [1, 2, 1, 4, 4, 2, 1, 8]
def baseStart_7718329 : Nat := 118140960795 + 7718329 * 2 ^ 59
def prefixEnd_7718329 : Nat := 4983230072969 + 3 ^ 40 * 7718329 * 2
def baseEnd_7718329 : Nat := 146785652834675471703391

theorem tailTrace_7718329 : CollatzResearch.WordTrace tailWord_7718329 prefixEnd_7718329 146785652834675471703391 := by
  unfold tailWord_7718329
  simp only [CollatzResearch.WordTrace]
  refine ⟨281510585654819693492190041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187673723769879795661460027 281510585654819693492190041)
  ·
    refine ⟨211132939241114770119142531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281510585654819693492190041 211132939241114770119142531)
    ·
      refine ⟨316699408861672155178713797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211132939241114770119142531 316699408861672155178713797)
      ·
        refine ⟨59381139161563529096008837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316699408861672155178713797 59381139161563529096008837)
        ·
          refine ⟨11133963592793161705501657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59381139161563529096008837 11133963592793161705501657)
          ·
            refine ⟨8350472694594871279126243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11133963592793161705501657 8350472694594871279126243)
            ·
              refine ⟨12525709041892306918689365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8350472694594871279126243 12525709041892306918689365)
              ·
                refine ⟨146785652834675471703391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12525709041892306918689365 146785652834675471703391)
                ·
                  rfl

theorem cell23_7718329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 8].length) (baseStart_7718329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718329 prefixEnd_7718329 := by exact prefixLift 7718329
  have htrace : WordTrace (prefixWord ++ tailWord_7718329) baseStart_7718329 baseEnd_7718329 := by
    simpa [prefixWord, tailWord_7718329, baseEnd_7718329] using wordTrace_append hprefix tailTrace_7718329
  have hstable : (prefixWord ++ tailWord_7718329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718329).length < 2 ^ (prefixWord ++ tailWord_7718329).sum := by decide
  have hdescent : baseEnd_7718329 < baseStart_7718329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718373 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 2, 1, 3]
def baseStart_7718373 : Nat := 118140960795 + 7718373 * 2 ^ 59
def prefixEnd_7718373 : Nat := 4983230072969 + 3 ^ 40 * 7718373 * 2
def baseEnd_7718373 : Nat := 3963235219685035563841355

theorem tailTrace_7718373 : CollatzResearch.WordTrace tailWord_7718373 prefixEnd_7718373 3963235219685035563841355 := by
  unfold tailWord_7718373
  simp only [CollatzResearch.WordTrace]
  refine ⟨281512190466660289006791773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187674793644440192671194515 281512190466660289006791773)
  ·
    refine ⟨105567071424997608377546915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281512190466660289006791773 105567071424997608377546915)
    ·
      refine ⟨158350607137496412566320373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105567071424997608377546915 158350607137496412566320373)
      ·
        refine ⟨14845369419140288678092535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158350607137496412566320373 14845369419140288678092535)
        ·
          refine ⟨22268054128710433017138803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14845369419140288678092535 22268054128710433017138803)
          ·
            refine ⟨33402081193065649525708205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22268054128710433017138803 33402081193065649525708205)
            ·
              refine ⟨12525780447399618572140577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33402081193065649525708205 12525780447399618572140577)
              ·
                refine ⟨9394335335549713929105433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12525780447399618572140577 9394335335549713929105433)
                ·
                  refine ⟨7045751501662285446829075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9394335335549713929105433 7045751501662285446829075)
                  ·
                    refine ⟨10568627252493428170243613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7045751501662285446829075 10568627252493428170243613)
                    ·
                      refine ⟨3963235219685035563841355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10568627252493428170243613 3963235219685035563841355)
                      ·
                        rfl

theorem cell23_7718373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_7718373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718373 prefixEnd_7718373 := by exact prefixLift 7718373
  have htrace : WordTrace (prefixWord ++ tailWord_7718373) baseStart_7718373 baseEnd_7718373 := by
    simpa [prefixWord, tailWord_7718373, baseEnd_7718373] using wordTrace_append hprefix tailTrace_7718373
  have hstable : (prefixWord ++ tailWord_7718373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718373).length < 2 ^ (prefixWord ++ tailWord_7718373).sum := by decide
  have hdescent : baseEnd_7718373 < baseStart_7718373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718390 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_7718390 : Nat := 118140960795 + 7718390 * 2 ^ 59
def prefixEnd_7718390 : Nat := 4983230072969 + 3 ^ 40 * 7718390 * 2
def baseEnd_7718390 : Nat := 3963243948856161997328777

theorem tailTrace_7718390 : CollatzResearch.WordTrace tailWord_7718390 prefixEnd_7718390 3963243948856161997328777 := by
  unfold tailWord_7718390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17594550656724918806885039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187675207005065800606773749 17594550656724918806885039)
  ·
    refine ⟨26391825985087378210327559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17594550656724918806885039 26391825985087378210327559)
    ·
      refine ⟨39587738977631067315491339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26391825985087378210327559 39587738977631067315491339)
      ·
        refine ⟨59381608466446600973237009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39587738977631067315491339 59381608466446600973237009)
        ·
          refine ⟨44536206349834950729927757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59381608466446600973237009 44536206349834950729927757)
          ·
            refine ⟨16701077381188106523722909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44536206349834950729927757 16701077381188106523722909)
            ·
              refine ⟨6262904017945539946396091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16701077381188106523722909 6262904017945539946396091)
              ·
                refine ⟨9394356026918309919594137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6262904017945539946396091 9394356026918309919594137)
                ·
                  refine ⟨7045767020188732439695603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9394356026918309919594137 7045767020188732439695603)
                  ·
                    refine ⟨10568650530283098659543405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7045767020188732439695603 10568650530283098659543405)
                    ·
                      refine ⟨3963243948856161997328777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10568650530283098659543405 3963243948856161997328777)
                      ·
                        rfl

theorem cell23_7718390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_7718390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718390 prefixEnd_7718390 := by exact prefixLift 7718390
  have htrace : WordTrace (prefixWord ++ tailWord_7718390) baseStart_7718390 baseEnd_7718390 := by
    simpa [prefixWord, tailWord_7718390, baseEnd_7718390] using wordTrace_append hprefix tailTrace_7718390
  have hstable : (prefixWord ++ tailWord_7718390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718390).length < 2 ^ (prefixWord ++ tailWord_7718390).sum := by decide
  have hdescent : baseEnd_7718390 < baseStart_7718390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718396 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 1, 4, 2]
def baseStart_7718396 : Nat := 118140960795 + 7718396 * 2 ^ 59
def prefixEnd_7718396 : Nat := 4983230072969 + 3 ^ 40 * 7718396 * 2
def baseEnd_7718396 : Nat := 3963247029740088973853749

theorem tailTrace_7718396 : CollatzResearch.WordTrace tailWord_7718396 prefixEnd_7718396 3963247029740088973853749 := by
  unfold tailWord_7718396
  simp only [CollatzResearch.WordTrace]
  refine ⟨140756514672788481967439521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187675352897051309289919361 140756514672788481967439521)
  ·
    refine ⟨105567386004591361475579641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140756514672788481967439521 105567386004591361475579641)
    ·
      refine ⟨79175539503443521106684731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105567386004591361475579641 79175539503443521106684731)
      ·
        refine ⟨118763309255165281660027097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79175539503443521106684731 118763309255165281660027097)
        ·
          refine ⟨89072481941373961245020323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118763309255165281660027097 89072481941373961245020323)
          ·
            refine ⟨133608722912060941867530485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89072481941373961245020323 133608722912060941867530485)
            ·
              refine ⟨12525817773005713300080983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133608722912060941867530485 12525817773005713300080983)
              ·
                refine ⟨18788726659508569950121475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12525817773005713300080983 18788726659508569950121475)
                ·
                  refine ⟨28183089989262854925182213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18788726659508569950121475 28183089989262854925182213)
                  ·
                    refine ⟨5284329372986785298471665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28183089989262854925182213 5284329372986785298471665)
                    ·
                      refine ⟨3963247029740088973853749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5284329372986785298471665 3963247029740088973853749)
                      ·
                        rfl

theorem cell23_7718396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_7718396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718396 prefixEnd_7718396 := by exact prefixLift 7718396
  have htrace : WordTrace (prefixWord ++ tailWord_7718396) baseStart_7718396 baseEnd_7718396 := by
    simpa [prefixWord, tailWord_7718396, baseEnd_7718396] using wordTrace_append hprefix tailTrace_7718396
  have hstable : (prefixWord ++ tailWord_7718396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718396).length < 2 ^ (prefixWord ++ tailWord_7718396).sum := by decide
  have hdescent : baseEnd_7718396 < baseStart_7718396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718472 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_7718472 : Nat := 118140960795 + 7718472 * 2 ^ 59
def prefixEnd_7718472 : Nat := 4983230072969 + 3 ^ 40 * 7718472 * 2
def baseEnd_7718472 : Nat := 3963286054269830676503399

theorem tailTrace_7718472 : CollatzResearch.WordTrace tailWord_7718472 prefixEnd_7718472 3963286054269830676503399 := by
  unfold tailWord_7718472
  simp only [CollatzResearch.WordTrace]
  refine ⟨140757900646650814457322835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187677200862201085943097113 140757900646650814457322835)
  ·
    refine ⟨211136850969976221685984253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140757900646650814457322835 211136850969976221685984253)
    ·
      refine ⟨79176319113741083132244095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211136850969976221685984253 79176319113741083132244095)
      ·
        refine ⟨118764478670611624698366143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79176319113741083132244095 118764478670611624698366143)
        ·
          refine ⟨178146718005917437047549215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118764478670611624698366143 178146718005917437047549215)
          ·
            refine ⟨267220077008876155571323823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178146718005917437047549215 267220077008876155571323823)
            ·
              refine ⟨400830115513314233356985735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267220077008876155571323823 400830115513314233356985735)
              ·
                refine ⟨601245173269971350035478603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400830115513314233356985735 601245173269971350035478603)
                ·
                  refine ⟨901867759904957025053217905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601245173269971350035478603 901867759904957025053217905)
                  ·
                    refine ⟨676400819928717768789913429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 901867759904957025053217905 676400819928717768789913429)
                    ·
                      refine ⟨3963286054269830676503399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 676400819928717768789913429 3963286054269830676503399)
                      ·
                        rfl

theorem cell23_7718472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_7718472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718472 prefixEnd_7718472 := by exact prefixLift 7718472
  have htrace : WordTrace (prefixWord ++ tailWord_7718472) baseStart_7718472 baseEnd_7718472 := by
    simpa [prefixWord, tailWord_7718472, baseEnd_7718472] using wordTrace_append hprefix tailTrace_7718472
  have hstable : (prefixWord ++ tailWord_7718472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718472).length < 2 ^ (prefixWord ++ tailWord_7718472).sum := by decide
  have hdescent : baseEnd_7718472 < baseStart_7718472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718573 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_7718573 : Nat := 118140960795 + 7718573 * 2 ^ 59
def prefixEnd_7718573 : Nat := 4983230072969 + 3 ^ 40 * 7718573 * 2
def baseEnd_7718573 : Nat := 1321112638605311593780145

theorem tailTrace_7718573 : CollatzResearch.WordTrace tailWord_7718573 prefixEnd_7718573 1321112638605311593780145 := by
  unfold tailWord_7718573
  simp only [CollatzResearch.WordTrace]
  refine ⟨281519485065935723164072373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187679656710623815442714915 281519485065935723164072373)
  ·
    refine ⟨26392451724931474046631785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281519485065935723164072373 26392451724931474046631785)
    ·
      refine ⟨19794338793698605534973839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26392451724931474046631785 19794338793698605534973839)
      ·
        refine ⟨29691508190547908302460759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19794338793698605534973839 29691508190547908302460759)
        ·
          refine ⟨44537262285821862453691139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29691508190547908302460759 44537262285821862453691139)
          ·
            refine ⟨66805893428732793680536709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44537262285821862453691139 66805893428732793680536709)
            ·
              refine ⟨12526105017887398815100633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66805893428732793680536709 12526105017887398815100633)
              ·
                refine ⟨9394578763415549111325475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12526105017887398815100633 9394578763415549111325475)
                ·
                  refine ⟨14091868145123323666988213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9394578763415549111325475 14091868145123323666988213)
                  ·
                    refine ⟨1321112638605311593780145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14091868145123323666988213 1321112638605311593780145)
                    ·
                      rfl

theorem cell23_7718573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_7718573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718573 prefixEnd_7718573 := by exact prefixLift 7718573
  have htrace : WordTrace (prefixWord ++ tailWord_7718573) baseStart_7718573 baseEnd_7718573 := by
    simpa [prefixWord, tailWord_7718573, baseEnd_7718573] using wordTrace_append hprefix tailTrace_7718573
  have hstable : (prefixWord ++ tailWord_7718573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718573).length < 2 ^ (prefixWord ++ tailWord_7718573).sum := by decide
  have hdescent : baseEnd_7718573 < baseStart_7718573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718576 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 4]
def baseStart_7718576 : Nat := 118140960795 + 7718576 * 2 ^ 59
def prefixEnd_7718576 : Nat := 4983230072969 + 3 ^ 40 * 7718576 * 2
def baseEnd_7718576 : Nat := 3963339456257898269602921

theorem tailTrace_7718576 : CollatzResearch.WordTrace tailWord_7718576 prefixEnd_7718576 3963339456257898269602921 := by
  unfold tailWord_7718576
  simp only [CollatzResearch.WordTrace]
  refine ⟨140759797242462427338215791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187679729656616569784287721 140759797242462427338215791)
  ·
    refine ⟨211139695863693641007323687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140759797242462427338215791 211139695863693641007323687)
    ·
      refine ⟨316709543795540461510985531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211139695863693641007323687 316709543795540461510985531)
      ·
        refine ⟨475064315693310692266478297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316709543795540461510985531 475064315693310692266478297)
        ·
          refine ⟨356298236769983019199858723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475064315693310692266478297 356298236769983019199858723)
          ·
            refine ⟨534447355154974528799788085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356298236769983019199858723 534447355154974528799788085)
            ·
              refine ⟨50104439545778862074980133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 534447355154974528799788085 50104439545778862074980133)
              ·
                refine ⟨9394582414833536639058775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50104439545778862074980133 9394582414833536639058775)
                ·
                  refine ⟨14091873622250304958588163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9394582414833536639058775 14091873622250304958588163)
                  ·
                    refine ⟨21137810433375457437882245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14091873622250304958588163 21137810433375457437882245)
                    ·
                      refine ⟨3963339456257898269602921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21137810433375457437882245 3963339456257898269602921)
                      ·
                        rfl

theorem cell23_7718576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 4].length) (baseStart_7718576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718576 prefixEnd_7718576 := by exact prefixLift 7718576
  have htrace : WordTrace (prefixWord ++ tailWord_7718576) baseStart_7718576 baseEnd_7718576 := by
    simpa [prefixWord, tailWord_7718576, baseEnd_7718576] using wordTrace_append hprefix tailTrace_7718576
  have hstable : (prefixWord ++ tailWord_7718576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718576).length < 2 ^ (prefixWord ++ tailWord_7718576).sum := by decide
  have hdescent : baseEnd_7718576 < baseStart_7718576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718579 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 5]
def baseStart_7718579 : Nat := 118140960795 + 7718579 * 2 ^ 59
def prefixEnd_7718579 : Nat := 4983230072969 + 3 ^ 40 * 7718579 * 2
def baseEnd_7718579 : Nat := 3963340996699861757865407

theorem tailTrace_7718579 : CollatzResearch.WordTrace tailWord_7718579 prefixEnd_7718579 3963340996699861757865407 := by
  unfold tailWord_7718579
  simp only [CollatzResearch.WordTrace]
  refine ⟨281519703903913986188790791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187679802602609324125860527 281519703903913986188790791)
  ·
    refine ⟨422279555855870979283186187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281519703903913986188790791 422279555855870979283186187)
    ·
      refine ⟨633419333783806468924779281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422279555855870979283186187 633419333783806468924779281)
      ·
        refine ⟨475064500337854851693584461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633419333783806468924779281 475064500337854851693584461)
        ·
          refine ⟨178149187626695569385094173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475064500337854851693584461 178149187626695569385094173)
          ·
            refine ⟨66805945360010838519410315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178149187626695569385094173 66805945360010838519410315)
            ·
              refine ⟨100208918040016257779115473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66805945360010838519410315 100208918040016257779115473)
              ·
                refine ⟨75156688530012193334336605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100208918040016257779115473 75156688530012193334336605)
                ·
                  refine ⟨28183758198754572500376227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75156688530012193334336605 28183758198754572500376227)
                  ·
                    refine ⟨42275637298131858750564341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28183758198754572500376227 42275637298131858750564341)
                    ·
                      refine ⟨3963340996699861757865407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42275637298131858750564341 3963340996699861757865407)
                      ·
                        rfl

theorem cell23_7718579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_7718579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718579 prefixEnd_7718579 := by exact prefixLift 7718579
  have htrace : WordTrace (prefixWord ++ tailWord_7718579) baseStart_7718579 baseEnd_7718579 := by
    simpa [prefixWord, tailWord_7718579, baseEnd_7718579] using wordTrace_append hprefix tailTrace_7718579
  have hstable : (prefixWord ++ tailWord_7718579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718579).length < 2 ^ (prefixWord ++ tailWord_7718579).sum := by decide
  have hdescent : baseEnd_7718579 < baseStart_7718579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718586 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 4, 4]
def baseStart_7718586 : Nat := 118140960795 + 7718586 * 2 ^ 59
def prefixEnd_7718586 : Nat := 4983230072969 + 3 ^ 40 * 7718586 * 2
def baseEnd_7718586 : Nat := 1321114863688147743492625

theorem tailTrace_7718586 : CollatzResearch.WordTrace tailWord_7718586 prefixEnd_7718586 1321114863688147743492625 := by
  unfold tailWord_7718586
  simp only [CollatzResearch.WordTrace]
  refine ⟨70379989803722156596073903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187679972809925750922863741 70379989803722156596073903)
  ·
    refine ⟨105569984705583234894110855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70379989803722156596073903 105569984705583234894110855)
    ·
      refine ⟨158354977058374852341166283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105569984705583234894110855 158354977058374852341166283)
      ·
        refine ⟨237532465587562278511749425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158354977058374852341166283 237532465587562278511749425)
        ·
          refine ⟨178149349190671708883812069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237532465587562278511749425 178149349190671708883812069)
          ·
            refine ⟨33403002973250945415714763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178149349190671708883812069 33403002973250945415714763)
            ·
              refine ⟨50104504459876418123572145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33403002973250945415714763 50104504459876418123572145)
              ·
                refine ⟨37578378344907313592679109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50104504459876418123572145 37578378344907313592679109)
                ·
                  refine ⟨7045945939670121298627333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37578378344907313592679109 7045945939670121298627333)
                  ·
                    refine ⟨1321114863688147743492625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7045945939670121298627333 1321114863688147743492625)
                    ·
                      rfl

theorem cell23_7718586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_7718586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718586 prefixEnd_7718586 := by exact prefixLift 7718586
  have htrace : WordTrace (prefixWord ++ tailWord_7718586) baseStart_7718586 baseEnd_7718586 := by
    simpa [prefixWord, tailWord_7718586, baseEnd_7718586] using wordTrace_append hprefix tailTrace_7718586
  have hstable : (prefixWord ++ tailWord_7718586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718586).length < 2 ^ (prefixWord ++ tailWord_7718586).sum := by decide
  have hdescent : baseEnd_7718586 < baseStart_7718586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718604 : List Nat := [2, 2, 1, 5, 2, 1, 3, 2, 1, 1, 3]
def baseStart_7718604 : Nat := 118140960795 + 7718604 * 2 ^ 59
def prefixEnd_7718604 : Nat := 4983230072969 + 3 ^ 40 * 7718604 * 2
def baseEnd_7718604 : Nat := 3963353833716224160052793

theorem tailTrace_7718604 : CollatzResearch.WordTrace tailWord_7718604 prefixEnd_7718604 3963353833716224160052793 := by
  unfold tailWord_7718604
  simp only [CollatzResearch.WordTrace]
  refine ⟨140760307864411707729225433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187680410485882276972300577 140760307864411707729225433)
  ·
    refine ⟨105570230898308780796919075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140760307864411707729225433 105570230898308780796919075)
    ·
      refine ⟨158355346347463171195378613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105570230898308780796919075 158355346347463171195378613)
      ·
        refine ⟨14845813720074672299566745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158355346347463171195378613 14845813720074672299566745)
        ·
          refine ⟨11134360290056004224675059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14845813720074672299566745 11134360290056004224675059)
          ·
            refine ⟨16701540435084006337012589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11134360290056004224675059 16701540435084006337012589)
            ·
              refine ⟨6263077663156502376379721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16701540435084006337012589 6263077663156502376379721)
              ·
                refine ⟨4697308247367376782284791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6263077663156502376379721 4697308247367376782284791)
                ·
                  refine ⟨7045962371051065173427187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697308247367376782284791 7045962371051065173427187)
                  ·
                    refine ⟨10568943556576597760140781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7045962371051065173427187 10568943556576597760140781)
                    ·
                      refine ⟨3963353833716224160052793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10568943556576597760140781 3963353833716224160052793)
                      ·
                        rfl

theorem cell23_7718604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_7718604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718604 prefixEnd_7718604 := by exact prefixLift 7718604
  have htrace : WordTrace (prefixWord ++ tailWord_7718604) baseStart_7718604 baseEnd_7718604 := by
    simpa [prefixWord, tailWord_7718604, baseEnd_7718604] using wordTrace_append hprefix tailTrace_7718604
  have hstable : (prefixWord ++ tailWord_7718604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718604).length < 2 ^ (prefixWord ++ tailWord_7718604).sum := by decide
  have hdescent : baseEnd_7718604 < baseStart_7718604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718627 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 1, 1, 4]
def baseStart_7718627 : Nat := 118140960795 + 7718627 * 2 ^ 59
def prefixEnd_7718627 : Nat := 4983230072969 + 3 ^ 40 * 7718627 * 2
def baseEnd_7718627 : Nat := 3963365643771277570065187

theorem tailTrace_7718627 : CollatzResearch.WordTrace tailWord_7718627 prefixEnd_7718627 3963365643771277570065187 := by
  unfold tailWord_7718627
  simp only [CollatzResearch.WordTrace]
  refine ⟨281521454607740090386538135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187680969738493393591025423 281521454607740090386538135)
  ·
    refine ⟨422282181911610135579807203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281521454607740090386538135 422282181911610135579807203)
    ·
      refine ⟨633423272867415203369710805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422282181911610135579807203 633423272867415203369710805)
      ·
        refine ⟨14845857957830043828977597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 633423272867415203369710805 14845857957830043828977597)
        ·
          refine ⟨5567196734186266435866599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14845857957830043828977597 5567196734186266435866599)
          ·
            refine ⟨8350795101279399653799899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567196734186266435866599 8350795101279399653799899)
            ·
              refine ⟨12526192651919099480699849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8350795101279399653799899 12526192651919099480699849)
              ·
                refine ⟨9394644488939324610524887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12526192651919099480699849 9394644488939324610524887)
                ·
                  refine ⟨14091966733408986915787331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9394644488939324610524887 14091966733408986915787331)
                  ·
                    refine ⟨21137950100113480373680997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14091966733408986915787331 21137950100113480373680997)
                    ·
                      refine ⟨3963365643771277570065187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21137950100113480373680997 3963365643771277570065187)
                      ·
                        rfl

theorem cell23_7718627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_7718627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718627 prefixEnd_7718627 := by exact prefixLift 7718627
  have htrace : WordTrace (prefixWord ++ tailWord_7718627) baseStart_7718627 baseEnd_7718627 := by
    simpa [prefixWord, tailWord_7718627, baseEnd_7718627] using wordTrace_append hprefix tailTrace_7718627
  have hstable : (prefixWord ++ tailWord_7718627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718627).length < 2 ^ (prefixWord ++ tailWord_7718627).sum := by decide
  have hdescent : baseEnd_7718627 < baseStart_7718627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718644 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7718644 : Nat := 118140960795 + 7718644 * 2 ^ 59
def prefixEnd_7718644 : Nat := 4983230072969 + 3 ^ 40 * 7718644 * 2
def baseEnd_7718644 : Nat := 3963374372942404003552609

theorem tailTrace_7718644 : CollatzResearch.WordTrace tailWord_7718644 prefixEnd_7718644 3963374372942404003552609 := by
  unfold tailWord_7718644
  simp only [CollatzResearch.WordTrace]
  refine ⟨140761037324339251144953493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187681383099119001526604657 140761037324339251144953493)
  ·
    refine ⟨6598173624578402397419695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140761037324339251144953493 6598173624578402397419695)
    ·
      refine ⟨9897260436867603596129543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6598173624578402397419695 9897260436867603596129543)
      ·
        refine ⟨14845890655301405394194315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9897260436867603596129543 14845890655301405394194315)
        ·
          refine ⟨22268835982952108091291473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14845890655301405394194315 22268835982952108091291473)
          ·
            refine ⟨16701626987214081068468605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22268835982952108091291473 16701626987214081068468605)
            ·
              refine ⟨6263110120205280400675727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16701626987214081068468605 6263110120205280400675727)
              ·
                refine ⟨9394665180307920601013591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6263110120205280400675727 9394665180307920601013591)
                ·
                  refine ⟨14091997770461880901520387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9394665180307920601013591 14091997770461880901520387)
                  ·
                    refine ⟨21137996655692821352280581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14091997770461880901520387 21137996655692821352280581)
                    ·
                      refine ⟨3963374372942404003552609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21137996655692821352280581 3963374372942404003552609)
                      ·
                        rfl

theorem cell23_7718644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7718644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718644 prefixEnd_7718644 := by exact prefixLift 7718644
  have htrace : WordTrace (prefixWord ++ tailWord_7718644) baseStart_7718644 baseEnd_7718644 := by
    simpa [prefixWord, tailWord_7718644, baseEnd_7718644] using wordTrace_append hprefix tailTrace_7718644
  have hstable : (prefixWord ++ tailWord_7718644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718644).length < 2 ^ (prefixWord ++ tailWord_7718644).sum := by decide
  have hdescent : baseEnd_7718644 < baseStart_7718644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718660 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_7718660 : Nat := 118140960795 + 7718660 * 2 ^ 59
def prefixEnd_7718660 : Nat := 4983230072969 + 3 ^ 40 * 7718660 * 2
def baseEnd_7718660 : Nat := 3963382588632875940952535

theorem tailTrace_7718660 : CollatzResearch.WordTrace tailWord_7718660 prefixEnd_7718660 3963382588632875940952535 := by
  unfold tailWord_7718660
  simp only [CollatzResearch.WordTrace]
  refine ⟨140761329108310268511244717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187681772144413691348326289 140761329108310268511244717)
  ·
    refine ⟨52785498415616350691716769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140761329108310268511244717 52785498415616350691716769)
    ·
      refine ⟨39589123811712263018787577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52785498415616350691716769 39589123811712263018787577)
      ·
        refine ⟨29691842858784197264090683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39589123811712263018787577 29691842858784197264090683)
        ·
          refine ⟨44537764288176295896136025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29691842858784197264090683 44537764288176295896136025)
          ·
            refine ⟨33403323216132221922102019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44537764288176295896136025 33403323216132221922102019)
            ·
              refine ⟨50104984824198332883153029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33403323216132221922102019 50104984824198332883153029)
              ·
                refine ⟨9394684654537187415591193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50104984824198332883153029 9394684654537187415591193)
                ·
                  refine ⟨7046013490902890561693395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9394684654537187415591193 7046013490902890561693395)
                  ·
                    refine ⟨10569020236354335842540093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7046013490902890561693395 10569020236354335842540093)
                    ·
                      refine ⟨3963382588632875940952535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10569020236354335842540093 3963382588632875940952535)
                      ·
                        rfl

theorem cell23_7718660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_7718660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718660 prefixEnd_7718660 := by exact prefixLift 7718660
  have htrace : WordTrace (prefixWord ++ tailWord_7718660) baseStart_7718660 baseEnd_7718660 := by
    simpa [prefixWord, tailWord_7718660, baseEnd_7718660] using wordTrace_append hprefix tailTrace_7718660
  have hstable : (prefixWord ++ tailWord_7718660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718660).length < 2 ^ (prefixWord ++ tailWord_7718660).sum := by decide
  have hdescent : baseEnd_7718660 < baseStart_7718660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718666 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_7718666 : Nat := 118140960795 + 7718666 * 2 ^ 59
def prefixEnd_7718666 : Nat := 4983230072969 + 3 ^ 40 * 7718666 * 2
def baseEnd_7718666 : Nat := 3963385669516802917477507

theorem tailTrace_7718666 : CollatzResearch.WordTrace tailWord_7718666 prefixEnd_7718666 3963385669516802917477507 := by
  unfold tailWord_7718666
  simp only [CollatzResearch.WordTrace]
  refine ⟨70380719263649700011801963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187681918036399200031471901 70380719263649700011801963)
  ·
    refine ⟨105571078895474550017702945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70380719263649700011801963 105571078895474550017702945)
    ·
      refine ⟨79178309171605912513277209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105571078895474550017702945 79178309171605912513277209)
      ·
        refine ⟨59383731878704434384957907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79178309171605912513277209 59383731878704434384957907)
        ·
          refine ⟨89075597818056651577436861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59383731878704434384957907 89075597818056651577436861)
          ·
            refine ⟨33403349181771244341538823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89075597818056651577436861 33403349181771244341538823)
            ·
              refine ⟨50105023772656866512308235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33403349181771244341538823 50105023772656866512308235)
              ·
                refine ⟨75157535658985299768462353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50105023772656866512308235 75157535658985299768462353)
                ·
                  refine ⟨56368151744238974826346765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75157535658985299768462353 56368151744238974826346765)
                  ·
                    refine ⟨21138056904089615559880037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56368151744238974826346765 21138056904089615559880037)
                    ·
                      refine ⟨3963385669516802917477507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21138056904089615559880037 3963385669516802917477507)
                      ·
                        rfl

theorem cell23_7718666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_7718666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718666 prefixEnd_7718666 := by exact prefixLift 7718666
  have htrace : WordTrace (prefixWord ++ tailWord_7718666) baseStart_7718666 baseEnd_7718666 := by
    simpa [prefixWord, tailWord_7718666, baseEnd_7718666] using wordTrace_append hprefix tailTrace_7718666
  have hstable : (prefixWord ++ tailWord_7718666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718666).length < 2 ^ (prefixWord ++ tailWord_7718666).sum := by decide
  have hdescent : baseEnd_7718666 < baseStart_7718666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718717 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 4, 2, 2]
def baseStart_7718717 : Nat := 118140960795 + 7718717 * 2 ^ 59
def prefixEnd_7718717 : Nat := 4983230072969 + 3 ^ 40 * 7718717 * 2
def baseEnd_7718717 : Nat := 3963411857030182217939773

theorem tailTrace_7718717 : CollatzResearch.WordTrace tailWord_7718717 prefixEnd_7718717 3963411857030182217939773 := by
  unfold tailWord_7718717
  simp only [CollatzResearch.WordTrace]
  refine ⟨281524737177414035757314405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187683158118276023838209603 281524737177414035757314405)
  ·
    refine ⟨52785888220765131704496451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281524737177414035757314405 52785888220765131704496451)
    ·
      refine ⟨79178832331147697556744677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52785888220765131704496451 79178832331147697556744677)
      ·
        refine ⟨14846031062090193291889627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79178832331147697556744677 14846031062090193291889627)
        ·
          refine ⟨22269046593135289937834441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14846031062090193291889627 22269046593135289937834441)
          ·
            refine ⟨16701784944851467453375831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22269046593135289937834441 16701784944851467453375831)
            ·
              refine ⟨25052677417277201180063747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16701784944851467453375831 25052677417277201180063747)
              ·
                refine ⟨37579016125915801770095621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25052677417277201180063747 37579016125915801770095621)
                ·
                  refine ⟨7046065523609212831892929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37579016125915801770095621 7046065523609212831892929)
                  ·
                    refine ⟨5284549142706909623919697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7046065523609212831892929 5284549142706909623919697)
                    ·
                      refine ⟨3963411857030182217939773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5284549142706909623919697 3963411857030182217939773)
                      ·
                        rfl

theorem cell23_7718717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_7718717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718717 prefixEnd_7718717 := by exact prefixLift 7718717
  have htrace : WordTrace (prefixWord ++ tailWord_7718717) baseStart_7718717 baseEnd_7718717 := by
    simpa [prefixWord, tailWord_7718717, baseEnd_7718717] using wordTrace_append hprefix tailTrace_7718717
  have hstable : (prefixWord ++ tailWord_7718717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718717).length < 2 ^ (prefixWord ++ tailWord_7718717).sum := by decide
  have hdescent : baseEnd_7718717 < baseStart_7718717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718723 : List Nat := [1, 1, 1, 3, 1, 5, 2, 4, 5]
def baseStart_7718723 : Nat := 118140960795 + 7718723 * 2 ^ 59
def prefixEnd_7718723 : Nat := 4983230072969 + 3 ^ 40 * 7718723 * 2
def baseEnd_7718723 : Nat := 440379437546012132718305

theorem tailTrace_7718723 : CollatzResearch.WordTrace tailWord_7718723 prefixEnd_7718723 440379437546012132718305 := by
  unfold tailWord_7718723
  simp only [CollatzResearch.WordTrace]
  refine ⟨281524956015392298782032823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187683304010261532521355215 281524956015392298782032823)
  ·
    refine ⟨422287434023088448173049235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281524956015392298782032823 422287434023088448173049235)
    ·
      refine ⟨633431151034632672259573853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422287434023088448173049235 633431151034632672259573853)
      ·
        refine ⟨237536681637987252097340195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 633431151034632672259573853 237536681637987252097340195)
        ·
          refine ⟨356305022456980878146010293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237536681637987252097340195 356305022456980878146010293)
          ·
            refine ⟨33403595855341957326188465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 356305022456980878146010293 33403595855341957326188465)
            ·
              refine ⟨25052696891506467994641349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33403595855341957326188465 25052696891506467994641349)
              ·
                refine ⟨4697380667157462748995253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25052696891506467994641349 4697380667157462748995253)
                ·
                  refine ⟨440379437546012132718305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4697380667157462748995253 440379437546012132718305)
                  ·
                    rfl

theorem cell23_7718723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 5].length) (baseStart_7718723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718723 prefixEnd_7718723 := by exact prefixLift 7718723
  have htrace : WordTrace (prefixWord ++ tailWord_7718723) baseStart_7718723 baseEnd_7718723 := by
    simpa [prefixWord, tailWord_7718723, baseEnd_7718723] using wordTrace_append hprefix tailTrace_7718723
  have hstable : (prefixWord ++ tailWord_7718723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718723).length < 2 ^ (prefixWord ++ tailWord_7718723).sum := by decide
  have hdescent : baseEnd_7718723 < baseStart_7718723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718774 : List Nat := [5, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_7718774 : Nat := 118140960795 + 7718774 * 2 ^ 59
def prefixEnd_7718774 : Nat := 4983230072969 + 3 ^ 40 * 7718774 * 2
def baseEnd_7718774 : Nat := 440382347269720943880779

theorem tailTrace_7718774 : CollatzResearch.WordTrace tailWord_7718774 prefixEnd_7718774 440382347269720943880779 := by
  unfold tailWord_7718774
  simp only [CollatzResearch.WordTrace]
  refine ⟨17595426008637970905758711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187684544092138356328092917 17595426008637970905758711)
  ·
    refine ⟨26393139012956956358638067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17595426008637970905758711 26393139012956956358638067)
    ·
      refine ⟨39589708519435434537957101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26393139012956956358638067 39589708519435434537957101)
      ·
        refine ⟨14846140694788287951733913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39589708519435434537957101 14846140694788287951733913)
        ·
          refine ⟨11134605521091215963800435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14846140694788287951733913 11134605521091215963800435)
          ·
            refine ⟨16701908281636823945700653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11134605521091215963800435 16701908281636823945700653)
            ·
              refine ⟨6263215605613808979637745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16701908281636823945700653 6263215605613808979637745)
              ·
                refine ⟨4697411704210356734728309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6263215605613808979637745 4697411704210356734728309)
                ·
                  refine ⟨440382347269720943880779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4697411704210356734728309 440382347269720943880779)
                  ·
                    rfl

theorem cell23_7718774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_7718774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718774 prefixEnd_7718774 := by exact prefixLift 7718774
  have htrace : WordTrace (prefixWord ++ tailWord_7718774) baseStart_7718774 baseEnd_7718774 := by
    simpa [prefixWord, tailWord_7718774, baseEnd_7718774] using wordTrace_append hprefix tailTrace_7718774
  have hstable : (prefixWord ++ tailWord_7718774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718774).length < 2 ^ (prefixWord ++ tailWord_7718774).sum := by decide
  have hdescent : baseEnd_7718774 < baseStart_7718774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718793 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 4, 2, 3]
def baseStart_7718793 : Nat := 118140960795 + 7718793 * 2 ^ 59
def prefixEnd_7718793 : Nat := 4983230072969 + 3 ^ 40 * 7718793 * 2
def baseEnd_7718793 : Nat := 3963450881559923920589423

theorem tailTrace_7718793 : CollatzResearch.WordTrace tailWord_7718793 prefixEnd_7718793 3963450881559923920589423 := by
  unfold tailWord_7718793
  simp only [CollatzResearch.WordTrace]
  refine ⟨281527509125138700737081033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187685006083425800491387355 281527509125138700737081033)
  ·
    refine ⟨211145631843854025552810775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281527509125138700737081033 211145631843854025552810775)
    ·
      refine ⟨316718447765781038329216163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211145631843854025552810775 316718447765781038329216163)
      ·
        refine ⟨475077671648671557493824245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316718447765781038329216163 475077671648671557493824245)
        ·
          refine ⟨44538531717062958515046023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 475077671648671557493824245 44538531717062958515046023)
          ·
            refine ⟨66807797575594437772569035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44538531717062958515046023 66807797575594437772569035)
            ·
              refine ⟨100211696363391656658853553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66807797575594437772569035 100211696363391656658853553)
              ·
                refine ⟨75158772272543742494140165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100211696363391656658853553 75158772272543742494140165)
                ·
                  refine ⟨14092269801101951717651281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75158772272543742494140165 14092269801101951717651281)
                  ·
                    refine ⟨10569202350826463788238461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14092269801101951717651281 10569202350826463788238461)
                    ·
                      refine ⟨3963450881559923920589423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10569202350826463788238461 3963450881559923920589423)
                      ·
                        rfl

theorem cell23_7718793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2, 3].length) (baseStart_7718793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718793 prefixEnd_7718793 := by exact prefixLift 7718793
  have htrace : WordTrace (prefixWord ++ tailWord_7718793) baseStart_7718793 baseEnd_7718793 := by
    simpa [prefixWord, tailWord_7718793, baseEnd_7718793] using wordTrace_append hprefix tailTrace_7718793
  have hstable : (prefixWord ++ tailWord_7718793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718793).length < 2 ^ (prefixWord ++ tailWord_7718793).sum := by decide
  have hdescent : baseEnd_7718793 < baseStart_7718793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718810 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3]
def baseStart_7718810 : Nat := 118140960795 + 7718810 * 2 ^ 59
def prefixEnd_7718810 : Nat := 4983230072969 + 3 ^ 40 * 7718810 * 2
def baseEnd_7718810 : Nat := 3963459610731050354076845

theorem tailTrace_7718810 : CollatzResearch.WordTrace tailWord_7718810 prefixEnd_7718810 3963459610731050354076845 := by
  unfold tailWord_7718810
  simp only [CollatzResearch.WordTrace]
  refine ⟨70382032291519278160112471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187685419444051408426966589 70382032291519278160112471)
  ·
    refine ⟨105573048437278917240168707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70382032291519278160112471 105573048437278917240168707)
    ·
      refine ⟨158359572655918375860253061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105573048437278917240168707 158359572655918375860253061)
      ·
        refine ⟨29692419872984695473797449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158359572655918375860253061 29692419872984695473797449)
        ·
          refine ⟨22269314904738521605348087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29692419872984695473797449 22269314904738521605348087)
          ·
            refine ⟨33403972357107782408022131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22269314904738521605348087 33403972357107782408022131)
            ·
              refine ⟨50105958535661673612033197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33403972357107782408022131 50105958535661673612033197)
              ·
                refine ⟨18789734450873127604512449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50105958535661673612033197 18789734450873127604512449)
                ·
                  refine ⟨14092300838154845703384337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18789734450873127604512449 14092300838154845703384337)
                  ·
                    refine ⟨10569225628616134277538253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14092300838154845703384337 10569225628616134277538253)
                    ·
                      refine ⟨3963459610731050354076845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10569225628616134277538253 3963459610731050354076845)
                      ·
                        rfl

theorem cell23_7718810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_7718810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718810 prefixEnd_7718810 := by exact prefixLift 7718810
  have htrace : WordTrace (prefixWord ++ tailWord_7718810) baseStart_7718810 baseEnd_7718810 := by
    simpa [prefixWord, tailWord_7718810, baseEnd_7718810] using wordTrace_append hprefix tailTrace_7718810
  have hstable : (prefixWord ++ tailWord_7718810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718810).length < 2 ^ (prefixWord ++ tailWord_7718810).sum := by decide
  have hdescent : baseEnd_7718810 < baseStart_7718810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718816 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_7718816 : Nat := 118140960795 + 7718816 * 2 ^ 59
def prefixEnd_7718816 : Nat := 4983230072969 + 3 ^ 40 * 7718816 * 2
def baseEnd_7718816 : Nat := 3963462691614977330601817

theorem tailTrace_7718816 : CollatzResearch.WordTrace tailWord_7718816 prefixEnd_7718816 3963462691614977330601817 := by
  unfold tailWord_7718816
  simp only [CollatzResearch.WordTrace]
  refine ⟨140764174002027687832584151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187685565336036917110112201 140764174002027687832584151)
  ·
    refine ⟨211146261003041531748876227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140764174002027687832584151 211146261003041531748876227)
    ·
      refine ⟨316719391504562297623314341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211146261003041531748876227 316719391504562297623314341)
      ·
        refine ⟨59384885907105430804371439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316719391504562297623314341 59384885907105430804371439)
        ·
          refine ⟨89077328860658146206557159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59384885907105430804371439 89077328860658146206557159)
          ·
            refine ⟨133615993290987219309835739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89077328860658146206557159 133615993290987219309835739)
            ·
              refine ⟨200423989936480828964753609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133615993290987219309835739 200423989936480828964753609)
              ·
                refine ⟨150317992452360621723565207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200423989936480828964753609 150317992452360621723565207)
                ·
                  refine ⟨225476988678540932585347811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150317992452360621723565207 225476988678540932585347811)
                  ·
                    refine ⟨338215483017811398878021717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225476988678540932585347811 338215483017811398878021717)
                    ·
                      refine ⟨3963462691614977330601817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 338215483017811398878021717 3963462691614977330601817)
                      ·
                        rfl

theorem cell23_7718816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_7718816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718816 prefixEnd_7718816 := by exact prefixLift 7718816
  have htrace : WordTrace (prefixWord ++ tailWord_7718816) baseStart_7718816 baseEnd_7718816 := by
    simpa [prefixWord, tailWord_7718816, baseEnd_7718816] using wordTrace_append hprefix tailTrace_7718816
  have hstable : (prefixWord ++ tailWord_7718816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718816).length < 2 ^ (prefixWord ++ tailWord_7718816).sum := by decide
  have hdescent : baseEnd_7718816 < baseStart_7718816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718840 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 3, 1, 3]
def baseStart_7718840 : Nat := 118140960795 + 7718840 * 2 ^ 59
def prefixEnd_7718840 : Nat := 4983230072969 + 3 ^ 40 * 7718840 * 2
def baseEnd_7718840 : Nat := 3963475015150685236701707

theorem tailTrace_7718840 : CollatzResearch.WordTrace tailWord_7718840 prefixEnd_7718840 3963475015150685236701707 := by
  unfold tailWord_7718840
  simp only [CollatzResearch.WordTrace]
  refine ⟨140764611677984213882020987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187686148903978951842694649 140764611677984213882020987)
  ·
    refine ⟨211146917516976320823031481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140764611677984213882020987 211146917516976320823031481)
    ·
      refine ⟨158360188137732240617273611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211146917516976320823031481 158360188137732240617273611)
      ·
        refine ⟨237540282206598360925910417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158360188137732240617273611 237540282206598360925910417)
        ·
          refine ⟨178155211654948770694432813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237540282206598360925910417 178155211654948770694432813)
          ·
            refine ⟨66808204370605789010412305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178155211654948770694432813 66808204370605789010412305)
            ·
              refine ⟨50106153277954341757809229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66808204370605789010412305 50106153277954341757809229)
              ·
                refine ⟨18789807479232878159178461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50106153277954341757809229 18789807479232878159178461)
                ·
                  refine ⟨7046177804712329309691923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18789807479232878159178461 7046177804712329309691923)
                  ·
                    refine ⟨10569266707068493964537885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7046177804712329309691923 10569266707068493964537885)
                    ·
                      refine ⟨3963475015150685236701707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10569266707068493964537885 3963475015150685236701707)
                      ·
                        rfl

theorem cell23_7718840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_7718840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718840 prefixEnd_7718840 := by exact prefixLift 7718840
  have htrace : WordTrace (prefixWord ++ tailWord_7718840) baseStart_7718840 baseEnd_7718840 := by
    simpa [prefixWord, tailWord_7718840, baseEnd_7718840] using wordTrace_append hprefix tailTrace_7718840
  have hstable : (prefixWord ++ tailWord_7718840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718840).length < 2 ^ (prefixWord ++ tailWord_7718840).sum := by decide
  have hdescent : baseEnd_7718840 < baseStart_7718840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718863 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 4]
def baseStart_7718863 : Nat := 118140960795 + 7718863 * 2 ^ 59
def prefixEnd_7718863 : Nat := 4983230072969 + 3 ^ 40 * 7718863 * 2
def baseEnd_7718863 : Nat := 3963486825205738646714101

theorem tailTrace_7718863 : CollatzResearch.WordTrace tailWord_7718863 prefixEnd_7718863 3963486825205738646714101 := by
  unfold tailWord_7718863
  simp only [CollatzResearch.WordTrace]
  refine ⟨281530062234885102692129243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187686708156590068461419495 281530062234885102692129243)
  ·
    refine ⟨422295093352327654038193865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281530062234885102692129243 422295093352327654038193865)
    ·
      refine ⟨316721320014245740528645399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422295093352327654038193865 316721320014245740528645399)
      ·
        refine ⟨475081980021368610792968099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316721320014245740528645399 475081980021368610792968099)
        ·
          refine ⟨712622970032052916189452149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475081980021368610792968099 712622970032052916189452149)
          ·
            refine ⟨66808403440504960892761139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 712622970032052916189452149 66808403440504960892761139)
            ·
              refine ⟨100212605160757441339141709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66808403440504960892761139 100212605160757441339141709)
              ·
                refine ⟨37579726935284040502178141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100212605160757441339141709 37579726935284040502178141)
                ·
                  refine ⟨14092397600731515188316803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37579726935284040502178141 14092397600731515188316803)
                  ·
                    refine ⟨21138596401097272782475205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14092397600731515188316803 21138596401097272782475205)
                    ·
                      refine ⟨3963486825205738646714101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21138596401097272782475205 3963486825205738646714101)
                      ·
                        rfl

theorem cell23_7718863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_7718863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718863 prefixEnd_7718863 := by exact prefixLift 7718863
  have htrace : WordTrace (prefixWord ++ tailWord_7718863) baseStart_7718863 baseEnd_7718863 := by
    simpa [prefixWord, tailWord_7718863, baseEnd_7718863] using wordTrace_append hprefix tailTrace_7718863
  have hstable : (prefixWord ++ tailWord_7718863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718863).length < 2 ^ (prefixWord ++ tailWord_7718863).sum := by decide
  have hdescent : baseEnd_7718863 < baseStart_7718863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718877 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_7718877 : Nat := 118140960795 + 7718877 * 2 ^ 59
def prefixEnd_7718877 : Nat := 4983230072969 + 3 ^ 40 * 7718877 * 2
def baseEnd_7718877 : Nat := 1321164671311633863979679

theorem tailTrace_7718877 : CollatzResearch.WordTrace tailWord_7718877 prefixEnd_7718877 1321164671311633863979679 := by
  unfold tailWord_7718877
  simp only [CollatzResearch.WordTrace]
  refine ⟨281530572856834383083138885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187687048571222922055425923 281530572856834383083138885)
  ·
    refine ⟨52786982410656446828088541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281530572856834383083138885 52786982410656446828088541)
    ·
      refine ⟨19795118403996167560533203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52786982410656446828088541 19795118403996167560533203)
      ·
        refine ⟨29692677605994251340799805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19795118403996167560533203 29692677605994251340799805)
        ·
          refine ⟨11134754102247844252799927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29692677605994251340799805 11134754102247844252799927)
          ·
            refine ⟨16702131153371766379199891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11134754102247844252799927 16702131153371766379199891)
            ·
              refine ⟨25053196730057649568799837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16702131153371766379199891 25053196730057649568799837)
              ·
                refine ⟨9394948773771618588299939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25053196730057649568799837 9394948773771618588299939)
                ·
                  refine ⟨14092423160657427882449909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9394948773771618588299939 14092423160657427882449909)
                  ·
                    refine ⟨1321164671311633863979679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14092423160657427882449909 1321164671311633863979679)
                    ·
                      rfl

theorem cell23_7718877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_7718877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718877 prefixEnd_7718877 := by exact prefixLift 7718877
  have htrace : WordTrace (prefixWord ++ tailWord_7718877) baseStart_7718877 baseEnd_7718877 := by
    simpa [prefixWord, tailWord_7718877, baseEnd_7718877] using wordTrace_append hprefix tailTrace_7718877
  have hstable : (prefixWord ++ tailWord_7718877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718877).length < 2 ^ (prefixWord ++ tailWord_7718877).sum := by decide
  have hdescent : baseEnd_7718877 < baseStart_7718877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718890 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 4, 4]
def baseStart_7718890 : Nat := 118140960795 + 7718890 * 2 ^ 59
def prefixEnd_7718890 : Nat := 4983230072969 + 3 ^ 40 * 7718890 * 2
def baseEnd_7718890 : Nat := 1321166896394470013692159

theorem tailTrace_7718890 : CollatzResearch.WordTrace tailWord_7718890 prefixEnd_7718890 1321166896394470013692159 := by
  unfold tailWord_7718890
  simp only [CollatzResearch.WordTrace]
  refine ⟨70382761751446821575840531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187687364670524857535574749 70382761751446821575840531)
  ·
    refine ⟨105574142627170232363760797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70382761751446821575840531 105574142627170232363760797)
    ·
      refine ⟨39590303485188837136410299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105574142627170232363760797 39590303485188837136410299)
      ·
        refine ⟨59385455227783255704615449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39590303485188837136410299 59385455227783255704615449)
        ·
          refine ⟨44539091420837441778461587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59385455227783255704615449 44539091420837441778461587)
          ·
            refine ⟨66808637131256162667692381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44539091420837441778461587 66808637131256162667692381)
            ·
              refine ⟨25053238924221061000384643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66808637131256162667692381 25053238924221061000384643)
              ·
                refine ⟨37579858386331591500576965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25053238924221061000384643 37579858386331591500576965)
                ·
                  refine ⟨7046223447437173406358181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37579858386331591500576965 7046223447437173406358181)
                  ·
                    refine ⟨1321166896394470013692159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7046223447437173406358181 1321166896394470013692159)
                    ·
                      rfl

theorem cell23_7718890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_7718890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718890 prefixEnd_7718890 := by exact prefixLift 7718890
  have htrace : WordTrace (prefixWord ++ tailWord_7718890) baseStart_7718890 baseEnd_7718890 := by
    simpa [prefixWord, tailWord_7718890, baseEnd_7718890] using wordTrace_append hprefix tailTrace_7718890
  have hstable : (prefixWord ++ tailWord_7718890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718890).length < 2 ^ (prefixWord ++ tailWord_7718890).sum := by decide
  have hdescent : baseEnd_7718890 < baseStart_7718890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718917 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 1, 2, 3]
def baseStart_7718917 : Nat := 118140960795 + 7718917 * 2 ^ 59
def prefixEnd_7718917 : Nat := 4983230072969 + 3 ^ 40 * 7718917 * 2
def baseEnd_7718917 : Nat := 3963514553161081435438853

theorem tailTrace_7718917 : CollatzResearch.WordTrace tailWord_7718917 prefixEnd_7718917 3963514553161081435438853 := by
  unfold tailWord_7718917
  simp only [CollatzResearch.WordTrace]
  refine ⟨281532031776689469914595005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187688021184459646609730003 281532031776689469914595005)
  ·
    refine ⟨105574511916258551217973127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281532031776689469914595005 105574511916258551217973127)
    ·
      refine ⟨158361767874387826826959691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105574511916258551217973127 158361767874387826826959691)
      ·
        refine ⟨237542651811581740240439537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158361767874387826826959691 237542651811581740240439537)
        ·
          refine ⟨178156988858686305180329653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237542651811581740240439537 178156988858686305180329653)
          ·
            refine ⟨16702217705501841110655905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178156988858686305180329653 16702217705501841110655905)
            ·
              refine ⟨12526663279126380832991929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16702217705501841110655905 12526663279126380832991929)
              ·
                refine ⟨9394997459344785624743947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12526663279126380832991929 9394997459344785624743947)
                ·
                  refine ⟨14092496189017178437115921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9394997459344785624743947 14092496189017178437115921)
                  ·
                    refine ⟨10569372141762883827836941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14092496189017178437115921 10569372141762883827836941)
                    ·
                      refine ⟨3963514553161081435438853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10569372141762883827836941 3963514553161081435438853)
                      ·
                        rfl

theorem cell23_7718917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_7718917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718917 prefixEnd_7718917 := by exact prefixLift 7718917
  have htrace : WordTrace (prefixWord ++ tailWord_7718917) baseStart_7718917 baseEnd_7718917 := by
    simpa [prefixWord, tailWord_7718917, baseEnd_7718917] using wordTrace_append hprefix tailTrace_7718917
  have hstable : (prefixWord ++ tailWord_7718917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718917).length < 2 ^ (prefixWord ++ tailWord_7718917).sum := by decide
  have hdescent : baseEnd_7718917 < baseStart_7718917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718943 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_7718943 : Nat := 118140960795 + 7718943 * 2 ^ 59
def prefixEnd_7718943 : Nat := 4983230072969 + 3 ^ 40 * 7718943 * 2
def baseEnd_7718943 : Nat := 3963527903658098333713733

theorem tailTrace_7718943 : CollatzResearch.WordTrace tailWord_7718943 prefixEnd_7718943 3963527903658098333713733 := by
  unfold tailWord_7718943
  simp only [CollatzResearch.WordTrace]
  refine ⟨281532980074595276355041483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187688653383063517570027655 281532980074595276355041483)
  ·
    refine ⟨422299470111892914532562225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281532980074595276355041483 422299470111892914532562225)
    ·
      refine ⟨316724602583919685899421669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422299470111892914532562225 316724602583919685899421669)
      ·
        refine ⟨59385862984484941106141563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316724602583919685899421669 59385862984484941106141563)
        ·
          refine ⟨89078794476727411659212345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59385862984484941106141563 89078794476727411659212345)
          ·
            refine ⟨66809095857545558744409259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89078794476727411659212345 66809095857545558744409259)
            ·
              refine ⟨100213643786318338116613889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66809095857545558744409259 100213643786318338116613889)
              ·
                refine ⟨75160232839738753587460417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100213643786318338116613889 75160232839738753587460417)
                ·
                  refine ⟨56370174629804065190595313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75160232839738753587460417 56370174629804065190595313)
                  ·
                    refine ⟨42277630972353048892946485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56370174629804065190595313 42277630972353048892946485)
                    ·
                      refine ⟨3963527903658098333713733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42277630972353048892946485 3963527903658098333713733)
                      ·
                        rfl

theorem cell23_7718943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_7718943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718943 prefixEnd_7718943 := by exact prefixLift 7718943
  have htrace : WordTrace (prefixWord ++ tailWord_7718943) baseStart_7718943 baseEnd_7718943 := by
    simpa [prefixWord, tailWord_7718943, baseEnd_7718943] using wordTrace_append hprefix tailTrace_7718943
  have hstable : (prefixWord ++ tailWord_7718943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718943).length < 2 ^ (prefixWord ++ tailWord_7718943).sum := by decide
  have hdescent : baseEnd_7718943 < baseStart_7718943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718947 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 2, 1, 3]
def baseStart_7718947 : Nat := 118140960795 + 7718947 * 2 ^ 59
def prefixEnd_7718947 : Nat := 4983230072969 + 3 ^ 40 * 7718947 * 2
def baseEnd_7718947 : Nat := 3963529957580716318063715

theorem tailTrace_7718947 : CollatzResearch.WordTrace tailWord_7718947 prefixEnd_7718947 3963529957580716318063715 := by
  unfold tailWord_7718947
  simp only [CollatzResearch.WordTrace]
  refine ⟨281533125966580785038187095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187688750644387190025458063 281533125966580785038187095)
  ·
    refine ⟨422299688949871177557280643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281533125966580785038187095 422299688949871177557280643)
    ·
      refine ⟨633449533424806766335920965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422299688949871177557280643 633449533424806766335920965)
      ·
        refine ⟨118771787517151268687985181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 633449533424806766335920965 118771787517151268687985181)
        ·
          refine ⟨44539420318931725757994443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118771787517151268687985181 44539420318931725757994443)
          ·
            refine ⟨66809130478397588636991665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44539420318931725757994443 66809130478397588636991665)
            ·
              refine ⟨50106847858798191477743749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66809130478397588636991665 50106847858798191477743749)
              ·
                refine ⟨9395033973524660902076953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50106847858798191477743749 9395033973524660902076953)
                ·
                  refine ⟨7046275480143495676557715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9395033973524660902076953 7046275480143495676557715)
                  ·
                    refine ⟨10569413220215243514836573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7046275480143495676557715 10569413220215243514836573)
                    ·
                      refine ⟨3963529957580716318063715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10569413220215243514836573 3963529957580716318063715)
                      ·
                        rfl

theorem cell23_7718947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_7718947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718947 prefixEnd_7718947 := by exact prefixLift 7718947
  have htrace : WordTrace (prefixWord ++ tailWord_7718947) baseStart_7718947 baseEnd_7718947 := by
    simpa [prefixWord, tailWord_7718947, baseEnd_7718947] using wordTrace_append hprefix tailTrace_7718947
  have hstable : (prefixWord ++ tailWord_7718947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718947).length < 2 ^ (prefixWord ++ tailWord_7718947).sum := by decide
  have hdescent : baseEnd_7718947 < baseStart_7718947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718948 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 3, 2, 2]
def baseStart_7718948 : Nat := 118140960795 + 7718948 * 2 ^ 59
def prefixEnd_7718948 : Nat := 4983230072969 + 3 ^ 40 * 7718948 * 2
def baseEnd_7718948 : Nat := 3963530471061370814151211

theorem tailTrace_7718948 : CollatzResearch.WordTrace tailWord_7718948 prefixEnd_7718948 3963530471061370814151211 := by
  unfold tailWord_7718948
  simp only [CollatzResearch.WordTrace]
  refine ⟨140766581219788581104486749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187688774959718108139315665 140766581219788581104486749)
  ·
    refine ⟨52787467957420717914182531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140766581219788581104486749 52787467957420717914182531)
    ·
      refine ⟨79181201936131076871273797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52787467957420717914182531 79181201936131076871273797)
      ·
        refine ⟨14846475363024576913363837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79181201936131076871273797 14846475363024576913363837)
        ·
          refine ⟨5567428261134216342511439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14846475363024576913363837 5567428261134216342511439)
          ·
            refine ⟨8351142391701324513767159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567428261134216342511439 8351142391701324513767159)
            ·
              refine ⟨12526713587551986770650739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8351142391701324513767159 12526713587551986770650739)
              ·
                refine ⟨18790070381327980155976109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12526713587551986770650739 18790070381327980155976109)
                ·
                  refine ⟨7046276392997992558491041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18790070381327980155976109 7046276392997992558491041)
                  ·
                    refine ⟨5284707294748494418868281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7046276392997992558491041 5284707294748494418868281)
                    ·
                      refine ⟨3963530471061370814151211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5284707294748494418868281 3963530471061370814151211)
                      ·
                        rfl

theorem cell23_7718948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_7718948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718948 prefixEnd_7718948 := by exact prefixLift 7718948
  have htrace : WordTrace (prefixWord ++ tailWord_7718948) baseStart_7718948 baseEnd_7718948 := by
    simpa [prefixWord, tailWord_7718948, baseEnd_7718948] using wordTrace_append hprefix tailTrace_7718948
  have hstable : (prefixWord ++ tailWord_7718948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718948).length < 2 ^ (prefixWord ++ tailWord_7718948).sum := by decide
  have hdescent : baseEnd_7718948 < baseStart_7718948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718963 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 2, 6]
def baseStart_7718963 : Nat := 118140960795 + 7718963 * 2 ^ 59
def prefixEnd_7718963 : Nat := 4983230072969 + 3 ^ 40 * 7718963 * 2
def baseEnd_7718963 : Nat := 1321179391090396085154547

theorem tailTrace_7718963 : CollatzResearch.WordTrace tailWord_7718963 prefixEnd_7718963 1321179391090396085154547 := by
  unfold tailWord_7718963
  simp only [CollatzResearch.WordTrace]
  refine ⟨281533709534522819770769543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187689139689681879847179695 281533709534522819770769543)
  ·
    refine ⟨422300564301784229656154315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281533709534522819770769543 422300564301784229656154315)
    ·
      refine ⟨633450846452676344484231473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422300564301784229656154315 633450846452676344484231473)
      ·
        refine ⟨475088134839507258363173605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633450846452676344484231473 475088134839507258363173605)
        ·
          refine ⟨89079025282407610943095051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 475088134839507258363173605 89079025282407610943095051)
          ·
            refine ⟨133618537923611416414642577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89079025282407610943095051 133618537923611416414642577)
            ·
              refine ⟨100213903442708562310981933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133618537923611416414642577 100213903442708562310981933)
              ·
                refine ⟨37580213791015710866618225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100213903442708562310981933 37580213791015710866618225)
                ·
                  refine ⟨28185160343261783149963669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37580213791015710866618225 28185160343261783149963669)
                  ·
                    refine ⟨1321179391090396085154547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28185160343261783149963669 1321179391090396085154547)
                    ·
                      rfl

theorem cell23_7718963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 6].length) (baseStart_7718963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718963 prefixEnd_7718963 := by exact prefixLift 7718963
  have htrace : WordTrace (prefixWord ++ tailWord_7718963) baseStart_7718963 baseEnd_7718963 := by
    simpa [prefixWord, tailWord_7718963, baseEnd_7718963] using wordTrace_append hprefix tailTrace_7718963
  have hstable : (prefixWord ++ tailWord_7718963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718963).length < 2 ^ (prefixWord ++ tailWord_7718963).sum := by decide
  have hdescent : baseEnd_7718963 < baseStart_7718963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718990 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_7718990 : Nat := 118140960795 + 7718990 * 2 ^ 59
def prefixEnd_7718990 : Nat := 4983230072969 + 3 ^ 40 * 7718990 * 2
def baseEnd_7718990 : Nat := 3963552037248859649826017

theorem tailTrace_7718990 : CollatzResearch.WordTrace tailWord_7718990 prefixEnd_7718990 3963552037248859649826017 := by
  unfold tailWord_7718990
  simp only [CollatzResearch.WordTrace]
  refine ⟨35191836788178125422750303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187689796203616668921334949 35191836788178125422750303)
  ·
    refine ⟨52787755182267188134125455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35191836788178125422750303 52787755182267188134125455)
    ·
      refine ⟨79181632773400782201188183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52787755182267188134125455 79181632773400782201188183)
      ·
        refine ⟨118772449160101173301782275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79181632773400782201188183 118772449160101173301782275)
        ·
          refine ⟨178158673740151759952673413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118772449160101173301782275 178158673740151759952673413)
          ·
            refine ⟨33404751326278454991126265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178158673740151759952673413 33404751326278454991126265)
            ·
              refine ⟨25053563494708841243344699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33404751326278454991126265 25053563494708841243344699)
              ·
                refine ⟨37580345242063261865017049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25053563494708841243344699 37580345242063261865017049)
                ·
                  refine ⟨28185258931547446398762787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37580345242063261865017049 28185258931547446398762787)
                  ·
                    refine ⟨42277888397321169598144181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28185258931547446398762787 42277888397321169598144181)
                    ·
                      refine ⟨3963552037248859649826017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42277888397321169598144181 3963552037248859649826017)
                      ·
                        rfl

theorem cell23_7718990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_7718990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718990 prefixEnd_7718990 := by exact prefixLift 7718990
  have htrace : WordTrace (prefixWord ++ tailWord_7718990) baseStart_7718990 baseEnd_7718990 := by
    simpa [prefixWord, tailWord_7718990, baseEnd_7718990] using wordTrace_append hprefix tailTrace_7718990
  have hstable : (prefixWord ++ tailWord_7718990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718990).length < 2 ^ (prefixWord ++ tailWord_7718990).sum := by decide
  have hdescent : baseEnd_7718990 < baseStart_7718990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7718998 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_7718998 : Nat := 118140960795 + 7718998 * 2 ^ 59
def prefixEnd_7718998 : Nat := 4983230072969 + 3 ^ 40 * 7718998 * 2
def baseEnd_7718998 : Nat := 3963556145094095618525981

theorem tailTrace_7718998 : CollatzResearch.WordTrace tailWord_7718998 prefixEnd_7718998 3963556145094095618525981 := by
  unfold tailWord_7718998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17595936630587251296768353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187689990726264013832195765 17595936630587251296768353)
  ·
    refine ⟨13196952472940438472576265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17595936630587251296768353 13196952472940438472576265)
    ·
      refine ⟨9897714354705328854432199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13196952472940438472576265 9897714354705328854432199)
      ·
        refine ⟨14846571532057993281648299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9897714354705328854432199 14846571532057993281648299)
        ·
          refine ⟨22269857298086989922472449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14846571532057993281648299 22269857298086989922472449)
          ·
            refine ⟨16702392973565242441854337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22269857298086989922472449 16702392973565242441854337)
            ·
              refine ⟨12526794730173931831390753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16702392973565242441854337 12526794730173931831390753)
              ·
                refine ⟨9395096047630448873543065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12526794730173931831390753 9395096047630448873543065)
                ·
                  refine ⟨7046322035722836655157299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9395096047630448873543065 7046322035722836655157299)
                  ·
                    refine ⟨10569483053584254982735949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7046322035722836655157299 10569483053584254982735949)
                    ·
                      refine ⟨3963556145094095618525981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10569483053584254982735949 3963556145094095618525981)
                      ·
                        rfl

theorem cell23_7718998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_7718998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7718998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7718998 prefixEnd_7718998 := by exact prefixLift 7718998
  have htrace : WordTrace (prefixWord ++ tailWord_7718998) baseStart_7718998 baseEnd_7718998 := by
    simpa [prefixWord, tailWord_7718998, baseEnd_7718998] using wordTrace_append hprefix tailTrace_7718998
  have hstable : (prefixWord ++ tailWord_7718998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7718998).length < 2 ^ (prefixWord ++ tailWord_7718998).sum := by decide
  have hdescent : baseEnd_7718998 < baseStart_7718998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7718998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719020 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 3]
def baseStart_7719020 : Nat := 118140960795 + 7719020 * 2 ^ 59
def prefixEnd_7719020 : Nat := 4983230072969 + 3 ^ 40 * 7719020 * 2
def baseEnd_7719020 : Nat := 3963567441668494532450879

theorem tailTrace_7719020 : CollatzResearch.WordTrace tailWord_7719020 prefixEnd_7719020 3963567441668494532450879 := by
  unfold tailWord_7719020
  simp only [CollatzResearch.WordTrace]
  refine ⟨140767894247658159252797257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187690525663544212337063009 140767894247658159252797257)
  ·
    refine ⟨105575920685743619439597943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140767894247658159252797257 105575920685743619439597943)
    ·
      refine ⟨158363881028615429159396915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105575920685743619439597943 158363881028615429159396915)
      ·
        refine ⟨237545821542923143739095373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158363881028615429159396915 237545821542923143739095373)
        ·
          refine ⟨89079683078596178902160765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237545821542923143739095373 89079683078596178902160765)
          ·
            refine ⟨33404881154473567088310287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89079683078596178902160765 33404881154473567088310287)
            ·
              refine ⟨50107321731710350632465431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33404881154473567088310287 50107321731710350632465431)
              ·
                refine ⟨75160982597565525948698147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50107321731710350632465431 75160982597565525948698147)
                ·
                  refine ⟨112741473896348288923047221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75160982597565525948698147 112741473896348288923047221)
                  ·
                    refine ⟨10569513177782652086535677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112741473896348288923047221 10569513177782652086535677)
                    ·
                      refine ⟨3963567441668494532450879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10569513177782652086535677 3963567441668494532450879)
                      ·
                        rfl

theorem cell23_7719020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_7719020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719020 prefixEnd_7719020 := by exact prefixLift 7719020
  have htrace : WordTrace (prefixWord ++ tailWord_7719020) baseStart_7719020 baseEnd_7719020 := by
    simpa [prefixWord, tailWord_7719020, baseEnd_7719020] using wordTrace_append hprefix tailTrace_7719020
  have hstable : (prefixWord ++ tailWord_7719020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719020).length < 2 ^ (prefixWord ++ tailWord_7719020).sum := by decide
  have hdescent : baseEnd_7719020 < baseStart_7719020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719077 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 2, 4, 2]
def baseStart_7719077 : Nat := 118140960795 + 7719077 * 2 ^ 59
def prefixEnd_7719077 : Nat := 4983230072969 + 3 ^ 40 * 7719077 * 2
def baseEnd_7719077 : Nat := 3963596710065800809438117

theorem tailTrace_7719077 : CollatzResearch.WordTrace tailWord_7719077 prefixEnd_7719077 3963596710065800809438117 := by
  unfold tailWord_7719077
  simp only [CollatzResearch.WordTrace]
  refine ⟨281537867456109817240419485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187691911637406544826946323 281537867456109817240419485)
  ·
    refine ⟨105576700296041181465157307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281537867456109817240419485 105576700296041181465157307)
    ·
      refine ⟨158365050444061772197735961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105576700296041181465157307 158365050444061772197735961)
      ·
        refine ⟨118773787833046329148301971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158365050444061772197735961 118773787833046329148301971)
        ·
          refine ⟨178160681749569493722452957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118773787833046329148301971 178160681749569493722452957)
          ·
            refine ⟨66810255656088560145919859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178160681749569493722452957 66810255656088560145919859)
            ·
              refine ⟨100215383484132840218879789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66810255656088560145919859 100215383484132840218879789)
              ·
                refine ⟨37580768806549815082079921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100215383484132840218879789 37580768806549815082079921)
                ·
                  refine ⟨28185576604912361311559941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37580768806549815082079921 28185576604912361311559941)
                  ·
                    refine ⟨5284795613421067745917489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28185576604912361311559941 5284795613421067745917489)
                    ·
                      refine ⟨3963596710065800809438117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5284795613421067745917489 3963596710065800809438117)
                      ·
                        rfl

theorem cell23_7719077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_7719077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719077 prefixEnd_7719077 := by exact prefixLift 7719077
  have htrace : WordTrace (prefixWord ++ tailWord_7719077) baseStart_7719077 baseEnd_7719077 := by
    simpa [prefixWord, tailWord_7719077, baseEnd_7719077] using wordTrace_append hprefix tailTrace_7719077
  have hstable : (prefixWord ++ tailWord_7719077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719077).length < 2 ^ (prefixWord ++ tailWord_7719077).sum := by decide
  have hdescent : baseEnd_7719077 < baseStart_7719077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719090 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_7719090 : Nat := 118140960795 + 7719090 * 2 ^ 59
def prefixEnd_7719090 : Nat := 4983230072969 + 3 ^ 40 * 7719090 * 2
def baseEnd_7719090 : Nat := 3963603385314309258575557

theorem tailTrace_7719090 : CollatzResearch.WordTrace tailWord_7719090 prefixEnd_7719090 3963603385314309258575557 := by
  unfold tailWord_7719090
  simp only [CollatzResearch.WordTrace]
  refine ⟨70384585401265680115160681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187692227736708480307095149 70384585401265680115160681)
  ·
    refine ⟨52788439050949260086370511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70384585401265680115160681 52788439050949260086370511)
    ·
      refine ⟨79182658576423890129555767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52788439050949260086370511 79182658576423890129555767)
      ·
        refine ⟨118773987864635835194333651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79182658576423890129555767 118773987864635835194333651)
        ·
          refine ⟨178160981796953752791500477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118773987864635835194333651 178160981796953752791500477)
          ·
            refine ⟨66810368173857657296812679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178160981796953752791500477 66810368173857657296812679)
            ·
              refine ⟨100215552260786485945219019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66810368173857657296812679 100215552260786485945219019)
              ·
                refine ⟨150323328391179728917828529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100215552260786485945219019 150323328391179728917828529)
                ·
                  refine ⟨112742496293384796688371397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150323328391179728917828529 112742496293384796688371397)
                  ·
                    refine ⟨21139218055009649379069637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112742496293384796688371397 21139218055009649379069637)
                    ·
                      refine ⟨3963603385314309258575557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21139218055009649379069637 3963603385314309258575557)
                      ·
                        rfl

theorem cell23_7719090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_7719090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719090 prefixEnd_7719090 := by exact prefixLift 7719090
  have htrace : WordTrace (prefixWord ++ tailWord_7719090) baseStart_7719090 baseEnd_7719090 := by
    simpa [prefixWord, tailWord_7719090, baseEnd_7719090] using wordTrace_append hprefix tailTrace_7719090
  have hstable : (prefixWord ++ tailWord_7719090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719090).length < 2 ^ (prefixWord ++ tailWord_7719090).sum := by decide
  have hdescent : baseEnd_7719090 < baseStart_7719090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719097 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 2, 2, 3]
def baseStart_7719097 : Nat := 118140960795 + 7719097 * 2 ^ 59
def prefixEnd_7719097 : Nat := 4983230072969 + 3 ^ 40 * 7719097 * 2
def baseEnd_7719097 : Nat := 3963606979678890731188025

theorem tailTrace_7719097 : CollatzResearch.WordTrace tailWord_7719097 prefixEnd_7719097 3963606979678890731188025 := by
  unfold tailWord_7719097
  simp only [CollatzResearch.WordTrace]
  refine ⟨281538596916037360656147545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187692397944024907104098363 281538596916037360656147545)
  ·
    refine ⟨211153947687028020492110659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281538596916037360656147545 211153947687028020492110659)
    ·
      refine ⟨316730921530542030738165989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211153947687028020492110659 316730921530542030738165989)
      ·
        refine ⟨59387047786976630763406123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316730921530542030738165989 59387047786976630763406123)
        ·
          refine ⟨89080571680464946145109185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59387047786976630763406123 89080571680464946145109185)
          ·
            refine ⟨66810428760348709608831889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89080571680464946145109185 66810428760348709608831889)
            ·
              refine ⟨50107821570261532206623917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66810428760348709608831889 50107821570261532206623917)
              ·
                refine ⟨18790433088848074577483969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50107821570261532206623917 18790433088848074577483969)
                ·
                  refine ⟨14092824816636055933112977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18790433088848074577483969 14092824816636055933112977)
                  ·
                    refine ⟨10569618612477041949834733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14092824816636055933112977 10569618612477041949834733)
                    ·
                      refine ⟨3963606979678890731188025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10569618612477041949834733 3963606979678890731188025)
                      ·
                        rfl

theorem cell23_7719097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_7719097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719097 prefixEnd_7719097 := by exact prefixLift 7719097
  have htrace : WordTrace (prefixWord ++ tailWord_7719097) baseStart_7719097 baseEnd_7719097 := by
    simpa [prefixWord, tailWord_7719097, baseEnd_7719097] using wordTrace_append hprefix tailTrace_7719097
  have hstable : (prefixWord ++ tailWord_7719097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719097).length < 2 ^ (prefixWord ++ tailWord_7719097).sum := by decide
  have hdescent : baseEnd_7719097 < baseStart_7719097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719178 : List Nat := [3, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3]
def baseStart_7719178 : Nat := 118140960795 + 7719178 * 2 ^ 59
def prefixEnd_7719178 : Nat := 4983230072969 + 3 ^ 40 * 7719178 * 2
def baseEnd_7719178 : Nat := 3963648571611904914275153

theorem tailTrace_7719178 : CollatzResearch.WordTrace tailWord_7719178 prefixEnd_7719178 3963648571611904914275153 := by
  unfold tailWord_7719178
  simp only [CollatzResearch.WordTrace]
  refine ⟨70385387807185977872461547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187694367485829274326564125 70385387807185977872461547)
  ·
    refine ⟨105578081710778966808692321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70385387807185977872461547 105578081710778966808692321)
    ·
      refine ⟨79183561283084225106519241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105578081710778966808692321 79183561283084225106519241)
      ·
        refine ⟨59387670962313168829889431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79183561283084225106519241 59387670962313168829889431)
        ·
          refine ⟨89081506443469753244834147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59387670962313168829889431 89081506443469753244834147)
          ·
            refine ⟨133622259665204629867251221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89081506443469753244834147 133622259665204629867251221)
            ·
              refine ⟨6263543421806467025027401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133622259665204629867251221 6263543421806467025027401)
              ·
                refine ⟨4697657566354850268770551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6263543421806467025027401 4697657566354850268770551)
                ·
                  refine ⟨7046486349532275403155827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697657566354850268770551 7046486349532275403155827)
                  ·
                    refine ⟨10569729524298413104733741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7046486349532275403155827 10569729524298413104733741)
                    ·
                      refine ⟨3963648571611904914275153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10569729524298413104733741 3963648571611904914275153)
                      ·
                        rfl

theorem cell23_7719178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_7719178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719178 prefixEnd_7719178 := by exact prefixLift 7719178
  have htrace : WordTrace (prefixWord ++ tailWord_7719178) baseStart_7719178 baseEnd_7719178 := by
    simpa [prefixWord, tailWord_7719178, baseEnd_7719178] using wordTrace_append hprefix tailTrace_7719178
  have hstable : (prefixWord ++ tailWord_7719178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719178).length < 2 ^ (prefixWord ++ tailWord_7719178).sum := by decide
  have hdescent : baseEnd_7719178 < baseStart_7719178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719194 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 1, 6]
def baseStart_7719194 : Nat := 118140960795 + 7719194 * 2 ^ 59
def prefixEnd_7719194 : Nat := 4983230072969 + 3 ^ 40 * 7719194 * 2
def baseEnd_7719194 : Nat := 1321218929100792283891693

theorem tailTrace_7719194 : CollatzResearch.WordTrace tailWord_7719194 prefixEnd_7719194 1321218929100792283891693 := by
  unfold tailWord_7719194
  simp only [CollatzResearch.WordTrace]
  refine ⟨70385533699171486555607159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187694756531123964148285757 70385533699171486555607159)
  ·
    refine ⟨105578300548757229833410739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70385533699171486555607159 105578300548757229833410739)
    ·
      refine ⟨158367450823135844750116109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105578300548757229833410739 158367450823135844750116109)
      ·
        refine ⟨59387794058675941781293541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158367450823135844750116109 59387794058675941781293541)
        ·
          refine ⟨11135211386001739083992539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59387794058675941781293541 11135211386001739083992539)
          ·
            refine ⟨16702817079002608625988809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11135211386001739083992539 16702817079002608625988809)
            ·
              refine ⟨12527112809251956469491607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16702817079002608625988809 12527112809251956469491607)
              ·
                refine ⟨18790669213877934704237411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12527112809251956469491607 18790669213877934704237411)
                ·
                  refine ⟨28186003820816902056356117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18790669213877934704237411 28186003820816902056356117)
                  ·
                    refine ⟨1321218929100792283891693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28186003820816902056356117 1321218929100792283891693)
                    ·
                      rfl

theorem cell23_7719194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_7719194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719194 prefixEnd_7719194 := by exact prefixLift 7719194
  have htrace : WordTrace (prefixWord ++ tailWord_7719194) baseStart_7719194 baseEnd_7719194 := by
    simpa [prefixWord, tailWord_7719194, baseEnd_7719194] using wordTrace_append hprefix tailTrace_7719194
  have hstable : (prefixWord ++ tailWord_7719194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719194).length < 2 ^ (prefixWord ++ tailWord_7719194).sum := by decide
  have hdescent : baseEnd_7719194 < baseStart_7719194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719204 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_7719204 : Nat := 118140960795 + 7719204 * 2 ^ 59
def prefixEnd_7719204 : Nat := 4983230072969 + 3 ^ 40 * 7719204 * 2
def baseEnd_7719204 : Nat := 3963661922108921812550033

theorem tailTrace_7719204 : CollatzResearch.WordTrace tailWord_7719204 prefixEnd_7719204 3963661922108921812550033 := by
  unfold tailWord_7719204
  simp only [CollatzResearch.WordTrace]
  refine ⟨140771249763324858965146333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187694999684433145286861777 140771249763324858965146333)
  ·
    refine ⟨52789218661246822111929875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140771249763324858965146333 52789218661246822111929875)
    ·
      refine ⟨79183827991870233167894813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52789218661246822111929875 79183827991870233167894813)
      ·
        refine ⟨29693935496951337437960555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79183827991870233167894813 29693935496951337437960555)
        ·
          refine ⟨44540903245427006156940833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29693935496951337437960555 44540903245427006156940833)
          ·
            refine ⟨33405677434070254617705625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44540903245427006156940833 33405677434070254617705625)
            ·
              refine ⟨25054258075552690963279219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33405677434070254617705625 25054258075552690963279219)
              ·
                refine ⟨37581387113329036444918829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25054258075552690963279219 37581387113329036444918829)
                ·
                  refine ⟨14093020167498388666844561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37581387113329036444918829 14093020167498388666844561)
                  ·
                    refine ⟨10569765125623791500133421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14093020167498388666844561 10569765125623791500133421)
                    ·
                      refine ⟨3963661922108921812550033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10569765125623791500133421 3963661922108921812550033)
                      ·
                        rfl

theorem cell23_7719204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_7719204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719204 prefixEnd_7719204 := by exact prefixLift 7719204
  have htrace : WordTrace (prefixWord ++ tailWord_7719204) baseStart_7719204 baseEnd_7719204 := by
    simpa [prefixWord, tailWord_7719204, baseEnd_7719204] using wordTrace_append hprefix tailTrace_7719204
  have hstable : (prefixWord ++ tailWord_7719204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719204).length < 2 ^ (prefixWord ++ tailWord_7719204).sum := by decide
  have hdescent : baseEnd_7719204 < baseStart_7719204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719218 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4]
def baseStart_7719218 : Nat := 118140960795 + 7719218 * 2 ^ 59
def prefixEnd_7719218 : Nat := 4983230072969 + 3 ^ 40 * 7719218 * 2
def baseEnd_7719218 : Nat := 3963669110838084757774969

theorem tailTrace_7719218 : CollatzResearch.WordTrace tailWord_7719218 prefixEnd_7719218 3963669110838084757774969 := by
  unfold tailWord_7719218
  simp only [CollatzResearch.WordTrace]
  refine ⟨70385752537149749580325577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187695340099065998880868205 70385752537149749580325577)
  ·
    refine ⟨52789314402862312185244183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70385752537149749580325577 52789314402862312185244183)
    ·
      refine ⟨79183971604293468277866275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52789314402862312185244183 79183971604293468277866275)
      ·
        refine ⟨118775957406440202416799413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79183971604293468277866275 118775957406440202416799413)
        ·
          refine ⟨11135246006853768976574945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118775957406440202416799413 11135246006853768976574945)
          ·
            refine ⟨8351434505140326732431209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11135246006853768976574945 8351434505140326732431209)
            ·
              refine ⟨6263575878855245049323407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8351434505140326732431209 6263575878855245049323407)
              ·
                refine ⟨9395363818282867573985111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6263575878855245049323407 9395363818282867573985111)
                ·
                  refine ⟨14093045727424301360977667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9395363818282867573985111 14093045727424301360977667)
                  ·
                    refine ⟨21139568591136452041466501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14093045727424301360977667 21139568591136452041466501)
                    ·
                      refine ⟨3963669110838084757774969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21139568591136452041466501 3963669110838084757774969)
                      ·
                        rfl

theorem cell23_7719218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_7719218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719218 prefixEnd_7719218 := by exact prefixLift 7719218
  have htrace : WordTrace (prefixWord ++ tailWord_7719218) baseStart_7719218 baseEnd_7719218 := by
    simpa [prefixWord, tailWord_7719218, baseEnd_7719218] using wordTrace_append hprefix tailTrace_7719218
  have hstable : (prefixWord ++ tailWord_7719218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719218).length < 2 ^ (prefixWord ++ tailWord_7719218).sum := by decide
  have hdescent : baseEnd_7719218 < baseStart_7719218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719287 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_7719287 : Nat := 118140960795 + 7719287 * 2 ^ 59
def prefixEnd_7719287 : Nat := 4983230072969 + 3 ^ 40 * 7719287 * 2
def baseEnd_7719287 : Nat := 3963704541003244987812151

theorem tailTrace_7719287 : CollatzResearch.WordTrace tailWord_7719287 prefixEnd_7719287 3963704541003244987812151 := by
  unfold tailWord_7719287
  simp only [CollatzResearch.WordTrace]
  refine ⟨281545526785349023105564115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187697017856899348737042743 281545526785349023105564115)
  ·
    refine ⟨422318290178023534658346173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281545526785349023105564115 422318290178023534658346173)
    ·
      refine ⟨158369358816758825496879815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422318290178023534658346173 158369358816758825496879815)
      ·
        refine ⟨237554038225138238245319723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158369358816758825496879815 237554038225138238245319723)
        ·
          refine ⟨356331057337707357367979585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237554038225138238245319723 356331057337707357367979585)
          ·
            refine ⟨267248293003280518025984689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356331057337707357367979585 267248293003280518025984689)
            ·
              refine ⟨200436219752460388519488517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267248293003280518025984689 200436219752460388519488517)
              ·
                refine ⟨37581791203586322847404097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200436219752460388519488517 37581791203586322847404097)
                ·
                  refine ⟨28186343402689742135553073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37581791203586322847404097 28186343402689742135553073)
                  ·
                    refine ⟨21139757552017306601664805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28186343402689742135553073 21139757552017306601664805)
                    ·
                      refine ⟨3963704541003244987812151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21139757552017306601664805 3963704541003244987812151)
                      ·
                        rfl

theorem cell23_7719287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_7719287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719287 prefixEnd_7719287 := by exact prefixLift 7719287
  have htrace : WordTrace (prefixWord ++ tailWord_7719287) baseStart_7719287 baseEnd_7719287 := by
    simpa [prefixWord, tailWord_7719287, baseEnd_7719287] using wordTrace_append hprefix tailTrace_7719287
  have hstable : (prefixWord ++ tailWord_7719287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719287).length < 2 ^ (prefixWord ++ tailWord_7719287).sum := by decide
  have hdescent : baseEnd_7719287 < baseStart_7719287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719291 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 4, 2, 2]
def baseStart_7719291 : Nat := 118140960795 + 7719291 * 2 ^ 59
def prefixEnd_7719291 : Nat := 4983230072969 + 3 ^ 40 * 7719291 * 2
def baseEnd_7719291 : Nat := 3963706594925862972162133

theorem tailTrace_7719291 : CollatzResearch.WordTrace tailWord_7719291 prefixEnd_7719291 3963706594925862972162133 := by
  unfold tailWord_7719291
  simp only [CollatzResearch.WordTrace]
  refine ⟨281545672677334531788709727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187697115118223021192473151 281545672677334531788709727)
  ·
    refine ⟨422318509016001797683064591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281545672677334531788709727 422318509016001797683064591)
    ·
      refine ⟨633477763524002696524596887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422318509016001797683064591 633477763524002696524596887)
      ·
        refine ⟨950216645286004044786895331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633477763524002696524596887 950216645286004044786895331)
        ·
          refine ⟨1425324967929006067180342997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950216645286004044786895331 1425324967929006067180342997)
          ·
            refine ⟨33406053935836079699539289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1425324967929006067180342997 33406053935836079699539289)
            ·
              refine ⟨25054540451877059774654467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33406053935836079699539289 25054540451877059774654467)
              ·
                refine ⟨37581810677815589661981701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25054540451877059774654467 37581810677815589661981701)
                ·
                  refine ⟨7046589502090423061621569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37581810677815589661981701 7046589502090423061621569)
                  ·
                    refine ⟨5284942126567817296216177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7046589502090423061621569 5284942126567817296216177)
                    ·
                      refine ⟨3963706594925862972162133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5284942126567817296216177 3963706594925862972162133)
                      ·
                        rfl

theorem cell23_7719291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 2, 2].length) (baseStart_7719291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719291 prefixEnd_7719291 := by exact prefixLift 7719291
  have htrace : WordTrace (prefixWord ++ tailWord_7719291) baseStart_7719291 baseEnd_7719291 := by
    simpa [prefixWord, tailWord_7719291, baseEnd_7719291] using wordTrace_append hprefix tailTrace_7719291
  have hstable : (prefixWord ++ tailWord_7719291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719291).length < 2 ^ (prefixWord ++ tailWord_7719291).sum := by decide
  have hdescent : baseEnd_7719291 < baseStart_7719291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719308 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 2, 2, 2]
def baseStart_7719308 : Nat := 118140960795 + 7719308 * 2 ^ 59
def prefixEnd_7719308 : Nat := 4983230072969 + 3 ^ 40 * 7719308 * 2
def baseEnd_7719308 : Nat := 3963715324096989405649555

theorem tailTrace_7719308 : CollatzResearch.WordTrace tailWord_7719308 prefixEnd_7719308 3963715324096989405649555 := by
  unfold tailWord_7719308
  simp only [CollatzResearch.WordTrace]
  refine ⟨140773146359136471846039289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187697528478848629128052385 140773146359136471846039289)
  ·
    refine ⟨105579859769352353884529467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140773146359136471846039289 105579859769352353884529467)
    ·
      refine ⟨158369789654028530826794201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105579859769352353884529467 158369789654028530826794201)
      ·
        refine ⟨118777342240521398120095651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158369789654028530826794201 118777342240521398120095651)
        ·
          refine ⟨178166013360782097180143477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118777342240521398120095651 178166013360782097180143477)
          ·
            refine ⟨16703063752573321610638451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178166013360782097180143477 16703063752573321610638451)
            ·
              refine ⟨25054595628859982415957677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16703063752573321610638451 25054595628859982415957677)
              ·
                refine ⟨9395473360822493405984129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25054595628859982415957677 9395473360822493405984129)
                ·
                  refine ⟨7046605020616870054488097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9395473360822493405984129 7046605020616870054488097)
                  ·
                    refine ⟨5284953765462652540866073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7046605020616870054488097 5284953765462652540866073)
                    ·
                      refine ⟨3963715324096989405649555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5284953765462652540866073 3963715324096989405649555)
                      ·
                        rfl

theorem cell23_7719308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_7719308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719308 prefixEnd_7719308 := by exact prefixLift 7719308
  have htrace : WordTrace (prefixWord ++ tailWord_7719308) baseStart_7719308 baseEnd_7719308 := by
    simpa [prefixWord, tailWord_7719308, baseEnd_7719308] using wordTrace_append hprefix tailTrace_7719308
  have hstable : (prefixWord ++ tailWord_7719308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719308).length < 2 ^ (prefixWord ++ tailWord_7719308).sum := by decide
  have hdescent : baseEnd_7719308 < baseStart_7719308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719347 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 4]
def baseStart_7719347 : Nat := 118140960795 + 7719347 * 2 ^ 59
def prefixEnd_7719347 : Nat := 4983230072969 + 3 ^ 40 * 7719347 * 2
def baseEnd_7719347 : Nat := 3963735349842514753061875

theorem tailTrace_7719347 : CollatzResearch.WordTrace tailWord_7719347 prefixEnd_7719347 3963735349842514753061875 := by
  unfold tailWord_7719347
  simp only [CollatzResearch.WordTrace]
  refine ⟨281547715165131653352748295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187698476776754435568498863 281547715165131653352748295)
  ·
    refine ⟨422321572747697480029122443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281547715165131653352748295 422321572747697480029122443)
    ·
      refine ⟨633482359121546220043683665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422321572747697480029122443 633482359121546220043683665)
      ·
        refine ⟨475111769341159665032762749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633482359121546220043683665 475111769341159665032762749)
        ·
          refine ⟨178166913502934874387286031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475111769341159665032762749 178166913502934874387286031)
          ·
            refine ⟨267250370254402311580929047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178166913502934874387286031 267250370254402311580929047)
            ·
              refine ⟨400875555381603467371393571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267250370254402311580929047 400875555381603467371393571)
              ·
                refine ⟨601313333072405201057090357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400875555381603467371393571 601313333072405201057090357)
                ·
                  refine ⟨56373124975537987599102221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 601313333072405201057090357 56373124975537987599102221)
                  ·
                    refine ⟨21139921865826745349663333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56373124975537987599102221 21139921865826745349663333)
                    ·
                      refine ⟨3963735349842514753061875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21139921865826745349663333 3963735349842514753061875)
                      ·
                        rfl

theorem cell23_7719347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_7719347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719347 prefixEnd_7719347 := by exact prefixLift 7719347
  have htrace : WordTrace (prefixWord ++ tailWord_7719347) baseStart_7719347 baseEnd_7719347 := by
    simpa [prefixWord, tailWord_7719347, baseEnd_7719347] using wordTrace_append hprefix tailTrace_7719347
  have hstable : (prefixWord ++ tailWord_7719347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719347).length < 2 ^ (prefixWord ++ tailWord_7719347).sum := by decide
  have hdescent : baseEnd_7719347 < baseStart_7719347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719377 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_7719377 : Nat := 118140960795 + 7719377 * 2 ^ 59
def prefixEnd_7719377 : Nat := 4983230072969 + 3 ^ 40 * 7719377 * 2
def baseEnd_7719377 : Nat := 3963750754262149635686737

theorem tailTrace_7719377 : CollatzResearch.WordTrace tailWord_7719377 prefixEnd_7719377 3963750754262149635686737 := by
  unfold tailWord_7719377
  simp only [CollatzResearch.WordTrace]
  refine ⟨281548809355022968476340385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187699206236681978984226923 281548809355022968476340385)
  ·
    refine ⟨211161607016267226357255289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281548809355022968476340385 211161607016267226357255289)
    ·
      refine ⟨158371205262200419767941467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211161607016267226357255289 158371205262200419767941467)
      ·
        refine ⟨237556807893300629651912201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158371205262200419767941467 237556807893300629651912201)
        ·
          refine ⟨178167605919975472238934151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237556807893300629651912201 178167605919975472238934151)
          ·
            refine ⟨267251408879963208358401227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178167605919975472238934151 267251408879963208358401227)
            ·
              refine ⟨400877113319944812537601841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267251408879963208358401227 400877113319944812537601841)
              ·
                refine ⟨300657834989958609403201381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400877113319944812537601841 300657834989958609403201381)
                ·
                  refine ⟨56373344060617239263100259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300657834989958609403201381 56373344060617239263100259)
                  ·
                    refine ⟨84560016090925858894650389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56373344060617239263100259 84560016090925858894650389)
                    ·
                      refine ⟨3963750754262149635686737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84560016090925858894650389 3963750754262149635686737)
                      ·
                        rfl

theorem cell23_7719377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_7719377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719377 prefixEnd_7719377 := by exact prefixLift 7719377
  have htrace : WordTrace (prefixWord ++ tailWord_7719377) baseStart_7719377 baseEnd_7719377 := by
    simpa [prefixWord, tailWord_7719377, baseEnd_7719377] using wordTrace_append hprefix tailTrace_7719377
  have hstable : (prefixWord ++ tailWord_7719377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719377).length < 2 ^ (prefixWord ++ tailWord_7719377).sum := by decide
  have hdescent : baseEnd_7719377 < baseStart_7719377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719381 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_7719381 : Nat := 118140960795 + 7719381 * 2 ^ 59
def prefixEnd_7719381 : Nat := 4983230072969 + 3 ^ 40 * 7719381 * 2
def baseEnd_7719381 : Nat := 3963752808184767620036719

theorem tailTrace_7719381 : CollatzResearch.WordTrace tailWord_7719381 prefixEnd_7719381 3963752808184767620036719 := by
  unfold tailWord_7719381
  simp only [CollatzResearch.WordTrace]
  refine ⟨281548955247008477159485997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187699303498005651439657331 281548955247008477159485997)
  ·
    refine ⟨105580858217628178934807249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281548955247008477159485997 105580858217628178934807249)
    ·
      refine ⟨79185643663221134201105437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105580858217628178934807249 79185643663221134201105437)
      ·
        refine ⟨29694616373707925325414539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79185643663221134201105437 29694616373707925325414539)
        ·
          refine ⟨44541924560561887988121809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29694616373707925325414539 44541924560561887988121809)
          ·
            refine ⟨33406443420421415991091357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44541924560561887988121809 33406443420421415991091357)
            ·
              refine ⟨12527416282658030996659259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33406443420421415991091357 12527416282658030996659259)
              ·
                refine ⟨18791124423987046494988889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12527416282658030996659259 18791124423987046494988889)
                ·
                  refine ⟨14093343317990284871241667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18791124423987046494988889 14093343317990284871241667)
                  ·
                    refine ⟨21140014976985427306862501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14093343317990284871241667 21140014976985427306862501)
                    ·
                      refine ⟨3963752808184767620036719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21140014976985427306862501 3963752808184767620036719)
                      ·
                        rfl

theorem cell23_7719381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_7719381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719381 prefixEnd_7719381 := by exact prefixLift 7719381
  have htrace : WordTrace (prefixWord ++ tailWord_7719381) baseStart_7719381 baseEnd_7719381 := by
    simpa [prefixWord, tailWord_7719381, baseEnd_7719381] using wordTrace_append hprefix tailTrace_7719381
  have hstable : (prefixWord ++ tailWord_7719381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719381).length < 2 ^ (prefixWord ++ tailWord_7719381).sum := by decide
  have hdescent : baseEnd_7719381 < baseStart_7719381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719421 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 6]
def baseStart_7719421 : Nat := 118140960795 + 7719421 * 2 ^ 59
def prefixEnd_7719421 : Nat := 4983230072969 + 3 ^ 40 * 7719421 * 2
def baseEnd_7719421 : Nat := 440419260823438607059615

theorem tailTrace_7719421 : CollatzResearch.WordTrace tailWord_7719421 prefixEnd_7719421 440419260823438607059615 := by
  unfold tailWord_7719421
  simp only [CollatzResearch.WordTrace]
  refine ⟨281550414166863563990942117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187700276111242375993961411 281550414166863563990942117)
  ·
    refine ⟨52790702656286918248301647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281550414166863563990942117 52790702656286918248301647)
    ·
      refine ⟨79186053984430377372452471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52790702656286918248301647 79186053984430377372452471)
      ·
        refine ⟨118779080976645566058678707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79186053984430377372452471 118779080976645566058678707)
        ·
          refine ⟨178168621464968349088018061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118779080976645566058678707 178168621464968349088018061)
          ·
            refine ⟨66813233049363130908006773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178168621464968349088018061 66813233049363130908006773)
            ·
              refine ⟨6263740598377793522625635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66813233049363130908006773 6263740598377793522625635)
              ·
                refine ⟨9395610897566690283938453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6263740598377793522625635 9395610897566690283938453)
                ·
                  refine ⟨440419260823438607059615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9395610897566690283938453 440419260823438607059615)
                  ·
                    rfl

theorem cell23_7719421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_7719421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719421 prefixEnd_7719421 := by exact prefixLift 7719421
  have htrace : WordTrace (prefixWord ++ tailWord_7719421) baseStart_7719421 baseEnd_7719421 := by
    simpa [prefixWord, tailWord_7719421, baseEnd_7719421] using wordTrace_append hprefix tailTrace_7719421
  have hstable : (prefixWord ++ tailWord_7719421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719421).length < 2 ^ (prefixWord ++ tailWord_7719421).sum := by decide
  have hdescent : baseEnd_7719421 < baseStart_7719421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719488 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 3, 2, 2]
def baseStart_7719488 : Nat := 118140960795 + 7719488 * 2 ^ 59
def prefixEnd_7719488 : Nat := 4983230072969 + 3 ^ 40 * 7719488 * 2
def baseEnd_7719488 : Nat := 3963807750614798701398727

theorem tailTrace_7719488 : CollatzResearch.WordTrace tailWord_7719488 prefixEnd_7719488 3963807750614798701398727 := by
  unfold tailWord_7719488
  simp only [CollatzResearch.WordTrace]
  refine ⟨140776428928810417216815559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187701905238413889622420745 140776428928810417216815559)
  ·
    refine ⟨211164643393215625825223339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140776428928810417216815559 211164643393215625825223339)
    ·
      refine ⟨316746965089823438737835009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211164643393215625825223339 316746965089823438737835009)
      ·
        refine ⟨237560223817367579053376257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316746965089823438737835009 237560223817367579053376257)
        ·
          refine ⟨178170167863025684290032193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237560223817367579053376257 178170167863025684290032193)
          ·
            refine ⟨133627625897269263217524145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178170167863025684290032193 133627625897269263217524145)
            ·
              refine ⟨100220719422951947413143109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133627625897269263217524145 100220719422951947413143109)
              ·
                refine ⟨18791384891803490139964333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100220719422951947413143109 18791384891803490139964333)
                ·
                  refine ⟨7046769334426308802486625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18791384891803490139964333 7046769334426308802486625)
                  ·
                    refine ⟨5285077000819731601864969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7046769334426308802486625 5285077000819731601864969)
                    ·
                      refine ⟨3963807750614798701398727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285077000819731601864969 3963807750614798701398727)
                      ·
                        rfl

theorem cell23_7719488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3, 2, 2].length) (baseStart_7719488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719488 prefixEnd_7719488 := by exact prefixLift 7719488
  have htrace : WordTrace (prefixWord ++ tailWord_7719488) baseStart_7719488 baseEnd_7719488 := by
    simpa [prefixWord, tailWord_7719488, baseEnd_7719488] using wordTrace_append hprefix tailTrace_7719488
  have hstable : (prefixWord ++ tailWord_7719488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719488).length < 2 ^ (prefixWord ++ tailWord_7719488).sum := by decide
  have hdescent : baseEnd_7719488 < baseStart_7719488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719508 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_7719508 : Nat := 118140960795 + 7719508 * 2 ^ 59
def prefixEnd_7719508 : Nat := 4983230072969 + 3 ^ 40 * 7719508 * 2
def baseEnd_7719508 : Nat := 3963818020227888623148635

theorem tailTrace_7719508 : CollatzResearch.WordTrace tailWord_7719508 prefixEnd_7719508 3963818020227888623148635 := by
  unfold tailWord_7719508
  simp only [CollatzResearch.WordTrace]
  refine ⟨140776793658774188924679589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187702391545032251899572785 140776793658774188924679589)
  ·
    refine ⟨26395648811020160423377423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140776793658774188924679589 26395648811020160423377423)
    ·
      refine ⟨39593473216530240635066135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26395648811020160423377423 39593473216530240635066135)
      ·
        refine ⟨59390209824795360952599203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39593473216530240635066135 59390209824795360952599203)
        ·
          refine ⟨89085314737193041428898805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59390209824795360952599203 89085314737193041428898805)
          ·
            refine ⟨8351748256611847633959263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89085314737193041428898805 8351748256611847633959263)
            ·
              refine ⟨12527622384917771450938895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8351748256611847633959263 12527622384917771450938895)
              ·
                refine ⟨18791433577376657176408343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12527622384917771450938895 18791433577376657176408343)
                ·
                  refine ⟨28187150366064985764612515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18791433577376657176408343 28187150366064985764612515)
                  ·
                    refine ⟨42280725549097478646918773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28187150366064985764612515 42280725549097478646918773)
                    ·
                      refine ⟨3963818020227888623148635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42280725549097478646918773 3963818020227888623148635)
                      ·
                        rfl

theorem cell23_7719508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_7719508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719508 prefixEnd_7719508 := by exact prefixLift 7719508
  have htrace : WordTrace (prefixWord ++ tailWord_7719508) baseStart_7719508 baseEnd_7719508 := by
    simpa [prefixWord, tailWord_7719508, baseEnd_7719508] using wordTrace_append hprefix tailTrace_7719508
  have hstable : (prefixWord ++ tailWord_7719508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719508).length < 2 ^ (prefixWord ++ tailWord_7719508).sum := by decide
  have hdescent : baseEnd_7719508 < baseStart_7719508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719516 : List Nat := [2, 2, 4, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_7719516 : Nat := 118140960795 + 7719516 * 2 ^ 59
def prefixEnd_7719516 : Nat := 4983230072969 + 3 ^ 40 * 7719516 * 2
def baseEnd_7719516 : Nat := 3963822128073124591848599

theorem tailTrace_7719516 : CollatzResearch.WordTrace tailWord_7719516 prefixEnd_7719516 3963822128073124591848599 := by
  unfold tailWord_7719516
  simp only [CollatzResearch.WordTrace]
  refine ⟨140776939550759697607825201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187702586067679596810433601 140776939550759697607825201)
  ·
    refine ⟨105582704663069773205868901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140776939550759697607825201 105582704663069773205868901)
    ·
      refine ⟨19796757124325582476100419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105582704663069773205868901 19796757124325582476100419)
      ·
        refine ⟨29695135686488373714150629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19796757124325582476100419 29695135686488373714150629)
        ·
          refine ⟨5567837941216570071403243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29695135686488373714150629 5567837941216570071403243)
          ·
            refine ⟨8351756911824855107104865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567837941216570071403243 8351756911824855107104865)
            ·
              refine ⟨6263817683868641330328649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8351756911824855107104865 6263817683868641330328649)
              ·
                refine ⟨4697863262901480997746487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6263817683868641330328649 4697863262901480997746487)
                ·
                  refine ⟨7046794894352221496619731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697863262901480997746487 7046794894352221496619731)
                  ·
                    refine ⟨10570192341528332244929597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7046794894352221496619731 10570192341528332244929597)
                    ·
                      refine ⟨3963822128073124591848599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10570192341528332244929597 3963822128073124591848599)
                      ·
                        rfl

theorem cell23_7719516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_7719516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719516 prefixEnd_7719516 := by exact prefixLift 7719516
  have htrace : WordTrace (prefixWord ++ tailWord_7719516) baseStart_7719516 baseEnd_7719516 := by
    simpa [prefixWord, tailWord_7719516, baseEnd_7719516] using wordTrace_append hprefix tailTrace_7719516
  have hstable : (prefixWord ++ tailWord_7719516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719516).length < 2 ^ (prefixWord ++ tailWord_7719516).sum := by decide
  have hdescent : baseEnd_7719516 < baseStart_7719516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719524 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_7719524 : Nat := 118140960795 + 7719524 * 2 ^ 59
def prefixEnd_7719524 : Nat := 4983230072969 + 3 ^ 40 * 7719524 * 2
def baseEnd_7719524 : Nat := 1321275411972786853516187

theorem tailTrace_7719524 : CollatzResearch.WordTrace tailWord_7719524 prefixEnd_7719524 1321275411972786853516187 := by
  unfold tailWord_7719524
  simp only [CollatzResearch.WordTrace]
  refine ⟨140777085442745206290970813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187702780590326941721294417 140777085442745206290970813)
  ·
    refine ⟨52791407041029452359114055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140777085442745206290970813 52791407041029452359114055)
    ·
      refine ⟨79187110561544178538671083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52791407041029452359114055 79187110561544178538671083)
      ·
        refine ⟨118780665842316267808006625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79187110561544178538671083 118780665842316267808006625)
        ·
          refine ⟨89085499381737200856004969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118780665842316267808006625 89085499381737200856004969)
          ·
            refine ⟨66814124536302900642003727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89085499381737200856004969 66814124536302900642003727)
            ·
              refine ⟨100221186804454350963005591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66814124536302900642003727 100221186804454350963005591)
              ·
                refine ⟨150331780206681526444508387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100221186804454350963005591 150331780206681526444508387)
                ·
                  refine ⟨225497670310022289666762581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150331780206681526444508387 225497670310022289666762581)
                  ·
                    refine ⟨1321275411972786853516187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 225497670310022289666762581 1321275411972786853516187)
                    ·
                      rfl

theorem cell23_7719524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_7719524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719524 prefixEnd_7719524 := by exact prefixLift 7719524
  have htrace : WordTrace (prefixWord ++ tailWord_7719524) baseStart_7719524 baseEnd_7719524 := by
    simpa [prefixWord, tailWord_7719524, baseEnd_7719524] using wordTrace_append hprefix tailTrace_7719524
  have hstable : (prefixWord ++ tailWord_7719524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719524).length < 2 ^ (prefixWord ++ tailWord_7719524).sum := by decide
  have hdescent : baseEnd_7719524 < baseStart_7719524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719528 : List Nat := [2, 1, 4, 3, 2, 2, 1, 8]
def baseStart_7719528 : Nat := 118140960795 + 7719528 * 2 ^ 59
def prefixEnd_7719528 : Nat := 4983230072969 + 3 ^ 40 * 7719528 * 2
def baseEnd_7719528 : Nat := 146808455179295501662909

theorem tailTrace_7719528 : CollatzResearch.WordTrace tailWord_7719528 prefixEnd_7719528 146808455179295501662909 := by
  unfold tailWord_7719528
  simp only [CollatzResearch.WordTrace]
  refine ⟨140777158388737960632543619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187702877851650614176724825 140777158388737960632543619)
  ·
    refine ⟨211165737583106940948815429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140777158388737960632543619 211165737583106940948815429)
    ·
      refine ⟨39593575796832551427902893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211165737583106940948815429 39593575796832551427902893)
      ·
        refine ⟨14847590923812206785463585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39593575796832551427902893 14847590923812206785463585)
        ·
          refine ⟨11135693192859155089097689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14847590923812206785463585 11135693192859155089097689)
          ·
            refine ⟨8351769894644366316823267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11135693192859155089097689 8351769894644366316823267)
            ·
              refine ⟨12527654841966549475234901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8351769894644366316823267 12527654841966549475234901)
              ·
                refine ⟨146808455179295501662909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12527654841966549475234901 146808455179295501662909)
                ·
                  rfl

theorem cell23_7719528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 8].length) (baseStart_7719528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719528 prefixEnd_7719528 := by exact prefixLift 7719528
  have htrace : WordTrace (prefixWord ++ tailWord_7719528) baseStart_7719528 baseEnd_7719528 := by
    simpa [prefixWord, tailWord_7719528, baseEnd_7719528] using wordTrace_append hprefix tailTrace_7719528
  have hstable : (prefixWord ++ tailWord_7719528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719528).length < 2 ^ (prefixWord ++ tailWord_7719528).sum := by decide
  have hdescent : baseEnd_7719528 < baseStart_7719528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719548 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 3, 3, 2]
def baseStart_7719548 : Nat := 118140960795 + 7719548 * 2 ^ 59
def prefixEnd_7719548 : Nat := 4983230072969 + 3 ^ 40 * 7719548 * 2
def baseEnd_7719548 : Nat := 3963838559454068466648451

theorem tailTrace_7719548 : CollatzResearch.WordTrace tailWord_7719548 prefixEnd_7719548 3963838559454068466648451 := by
  unfold tailWord_7719548
  simp only [CollatzResearch.WordTrace]
  refine ⟨140777523118701732340407649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187703364158268976453876865 140777523118701732340407649)
  ·
    refine ⟨105583142339026299255305737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140777523118701732340407649 105583142339026299255305737)
    ·
      refine ⟨79187356754269724441479303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105583142339026299255305737 79187356754269724441479303)
      ·
        refine ⟨118781035131404586662218955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79187356754269724441479303 118781035131404586662218955)
        ·
          refine ⟨178171552697106879993328433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118781035131404586662218955 178171552697106879993328433)
          ·
            refine ⟨133628664522830159994996325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178171552697106879993328433 133628664522830159994996325)
            ·
              refine ⟨25055374598030654999061811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133628664522830159994996325 25055374598030654999061811)
              ·
                refine ⟨37583061897045982498592717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25055374598030654999061811 37583061897045982498592717)
                ·
                  refine ⟨14093648211392243436972269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37583061897045982498592717 14093648211392243436972269)
                  ·
                    refine ⟨5285118079272091288864601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14093648211392243436972269 5285118079272091288864601)
                    ·
                      refine ⟨3963838559454068466648451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285118079272091288864601 3963838559454068466648451)
                      ·
                        rfl

theorem cell23_7719548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_7719548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719548 prefixEnd_7719548 := by exact prefixLift 7719548
  have htrace : WordTrace (prefixWord ++ tailWord_7719548) baseStart_7719548 baseEnd_7719548 := by
    simpa [prefixWord, tailWord_7719548, baseEnd_7719548] using wordTrace_append hprefix tailTrace_7719548
  have hstable : (prefixWord ++ tailWord_7719548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719548).length < 2 ^ (prefixWord ++ tailWord_7719548).sum := by decide
  have hdescent : baseEnd_7719548 < baseStart_7719548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719572 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_7719572 : Nat := 118140960795 + 7719572 * 2 ^ 59
def prefixEnd_7719572 : Nat := 4983230072969 + 3 ^ 40 * 7719572 * 2
def baseEnd_7719572 : Nat := 3963850882989776372748341

theorem tailTrace_7719572 : CollatzResearch.WordTrace tailWord_7719572 prefixEnd_7719572 3963850882989776372748341 := by
  unfold tailWord_7719572
  simp only [CollatzResearch.WordTrace]
  refine ⟨140777960794658258389844485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187703947726211011186459313 140777960794658258389844485)
  ·
    refine ⟨26395867648998423448095841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140777960794658258389844485 26395867648998423448095841)
    ·
      refine ⟨19796900736748817586071881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26395867648998423448095841 19796900736748817586071881)
      ·
        refine ⟨14847675552561613189553911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19796900736748817586071881 14847675552561613189553911)
        ·
          refine ⟨22271513328842419784330867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14847675552561613189553911 22271513328842419784330867)
          ·
            refine ⟨33407269993263629676496301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22271513328842419784330867 33407269993263629676496301)
            ·
              refine ⟨12527726247473861128686113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33407269993263629676496301 12527726247473861128686113)
              ·
                refine ⟨9395794685605395846514585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12527726247473861128686113 9395794685605395846514585)
                ·
                  refine ⟨7046846014204046884885939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9395794685605395846514585 7046846014204046884885939)
                  ·
                    refine ⟨10570269021306070327328909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7046846014204046884885939 10570269021306070327328909)
                    ·
                      refine ⟨3963850882989776372748341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10570269021306070327328909 3963850882989776372748341)
                      ·
                        rfl

theorem cell23_7719572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_7719572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719572 prefixEnd_7719572 := by exact prefixLift 7719572
  have htrace : WordTrace (prefixWord ++ tailWord_7719572) baseStart_7719572 baseEnd_7719572 := by
    simpa [prefixWord, tailWord_7719572, baseEnd_7719572] using wordTrace_append hprefix tailTrace_7719572
  have hstable : (prefixWord ++ tailWord_7719572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719572).length < 2 ^ (prefixWord ++ tailWord_7719572).sum := by decide
  have hdescent : baseEnd_7719572 < baseStart_7719572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719581 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_7719581 : Nat := 118140960795 + 7719581 * 2 ^ 59
def prefixEnd_7719581 : Nat := 4983230072969 + 3 ^ 40 * 7719581 * 2
def baseEnd_7719581 : Nat := 3963855504315666837535799

theorem tailTrace_7719581 : CollatzResearch.WordTrace tailWord_7719581 prefixEnd_7719581 3963855504315666837535799 := by
  unfold tailWord_7719581
  simp only [CollatzResearch.WordTrace]
  refine ⟨281556249846283911316766597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187704166564189274211177731 281556249846283911316766597)
  ·
    refine ⟨52791796846178233371893737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281556249846283911316766597 52791796846178233371893737)
    ·
      refine ⟨39593847634633675028920303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52791796846178233371893737 39593847634633675028920303)
      ·
        refine ⟨59390771451950512543380455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39593847634633675028920303 59390771451950512543380455)
        ·
          refine ⟨89086157177925768815070683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59390771451950512543380455 89086157177925768815070683)
          ·
            refine ⟨133629235766888653222606025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89086157177925768815070683 133629235766888653222606025)
            ·
              refine ⟨100221926825166489916954519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133629235766888653222606025 100221926825166489916954519)
              ·
                refine ⟨150332890237749734875431779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100221926825166489916954519 150332890237749734875431779)
                ·
                  refine ⟨225499335356624602313147669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150332890237749734875431779 225499335356624602313147669)
                  ·
                    refine ⟨10570281344841778233428797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 225499335356624602313147669 10570281344841778233428797)
                    ·
                      refine ⟨3963855504315666837535799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10570281344841778233428797 3963855504315666837535799)
                      ·
                        rfl

theorem cell23_7719581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_7719581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719581 prefixEnd_7719581 := by exact prefixLift 7719581
  have htrace : WordTrace (prefixWord ++ tailWord_7719581) baseStart_7719581 baseEnd_7719581 := by
    simpa [prefixWord, tailWord_7719581, baseEnd_7719581] using wordTrace_append hprefix tailTrace_7719581
  have hstable : (prefixWord ++ tailWord_7719581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719581).length < 2 ^ (prefixWord ++ tailWord_7719581).sum := by decide
  have hdescent : baseEnd_7719581 < baseStart_7719581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719641 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 5]
def baseStart_7719641 : Nat := 118140960795 + 7719641 * 2 ^ 59
def prefixEnd_7719641 : Nat := 4983230072969 + 3 ^ 40 * 7719641 * 2
def baseEnd_7719641 : Nat := 3963886313154936602785523

theorem tailTrace_7719641 : CollatzResearch.WordTrace tailWord_7719641 prefixEnd_7719641 3963886313154936602785523 := by
  unfold tailWord_7719641
  simp only [CollatzResearch.WordTrace]
  refine ⟨281558438226066541563950777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187705625484044361042633851 281558438226066541563950777)
  ·
    refine ⟨211168828669549906172963083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281558438226066541563950777 211168828669549906172963083)
    ·
      refine ⟨316753243004324859259444625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211168828669549906172963083 316753243004324859259444625)
      ·
        refine ⟨237564932253243644444583469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316753243004324859259444625 237564932253243644444583469)
        ·
          refine ⟨89086849594966366666718801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237564932253243644444583469 89086849594966366666718801)
          ·
            refine ⟨66815137196224775000039101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89086849594966366666718801 66815137196224775000039101)
            ·
              refine ⟨25055676448584290625014663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66815137196224775000039101 25055676448584290625014663)
              ·
                refine ⟨37583514672876435937521995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25055676448584290625014663 37583514672876435937521995)
                ·
                  refine ⟨56375272009314653906282993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37583514672876435937521995 56375272009314653906282993)
                  ·
                    refine ⟨42281454006985990429712245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56375272009314653906282993 42281454006985990429712245)
                    ·
                      refine ⟨3963886313154936602785523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42281454006985990429712245 3963886313154936602785523)
                      ·
                        rfl

theorem cell23_7719641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_7719641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719641 prefixEnd_7719641 := by exact prefixLift 7719641
  have htrace : WordTrace (prefixWord ++ tailWord_7719641) baseStart_7719641 baseEnd_7719641 := by
    simpa [prefixWord, tailWord_7719641, baseEnd_7719641] using wordTrace_append hprefix tailTrace_7719641
  have hstable : (prefixWord ++ tailWord_7719641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719641).length < 2 ^ (prefixWord ++ tailWord_7719641).sum := by decide
  have hdescent : baseEnd_7719641 < baseStart_7719641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719681 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_7719681 : Nat := 118140960795 + 7719681 * 2 ^ 59
def prefixEnd_7719681 : Nat := 4983230072969 + 3 ^ 40 * 7719681 * 2
def baseEnd_7719681 : Nat := 3963906852381116446285339

theorem tailTrace_7719681 : CollatzResearch.WordTrace tailWord_7719681 prefixEnd_7719681 3963906852381116446285339 := by
  unfold tailWord_7719681
  simp only [CollatzResearch.WordTrace]
  refine ⟨281559897145921628395406897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187706598097281085596937931 281559897145921628395406897)
  ·
    refine ⟨211169922859441221296555173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281559897145921628395406897 211169922859441221296555173)
    ·
      refine ⟨39594360536145228993104095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211169922859441221296555173 39594360536145228993104095)
      ·
        refine ⟨59391540804217843489656143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39594360536145228993104095 59391540804217843489656143)
        ·
          refine ⟨89087311206326765234484215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59391540804217843489656143 89087311206326765234484215)
          ·
            refine ⟨133630966809490147851726323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89087311206326765234484215 133630966809490147851726323)
            ·
              refine ⟨200446450214235221777589485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133630966809490147851726323 200446450214235221777589485)
              ·
                refine ⟨75167418830338208166596057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200446450214235221777589485 75167418830338208166596057)
                ·
                  refine ⟨56375564122753656124947043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75167418830338208166596057 56375564122753656124947043)
                  ·
                    refine ⟨84563346184130484187420565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56375564122753656124947043 84563346184130484187420565)
                    ·
                      refine ⟨3963906852381116446285339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84563346184130484187420565 3963906852381116446285339)
                      ·
                        rfl

theorem cell23_7719681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_7719681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719681 prefixEnd_7719681 := by exact prefixLift 7719681
  have htrace : WordTrace (prefixWord ++ tailWord_7719681) baseStart_7719681 baseEnd_7719681 := by
    simpa [prefixWord, tailWord_7719681, baseEnd_7719681] using wordTrace_append hprefix tailTrace_7719681
  have hstable : (prefixWord ++ tailWord_7719681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719681).length < 2 ^ (prefixWord ++ tailWord_7719681).sum := by decide
  have hdescent : baseEnd_7719681 < baseStart_7719681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719695 : List Nat := [1, 1, 2, 1, 1, 1, 7, 4, 1, 4]
def baseStart_7719695 : Nat := 118140960795 + 7719695 * 2 ^ 59
def prefixEnd_7719695 : Nat := 4983230072969 + 3 ^ 40 * 7719695 * 2
def baseEnd_7719695 : Nat := 1321304680370093130503425

theorem tailTrace_7719695 : CollatzResearch.WordTrace tailWord_7719695 prefixEnd_7719695 1321304680370093130503425 := by
  unfold tailWord_7719695
  simp only [CollatzResearch.WordTrace]
  refine ⟨281560407767870908786416539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187706938511913939190944359 281560407767870908786416539)
  ·
    refine ⟨422340611651806363179624809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281560407767870908786416539 422340611651806363179624809)
    ·
      refine ⟨316755458738854772384718607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422340611651806363179624809 316755458738854772384718607)
      ·
        refine ⟨475133188108282158577077911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316755458738854772384718607 475133188108282158577077911)
        ·
          refine ⟨712699782162423237865616867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475133188108282158577077911 712699782162423237865616867)
          ·
            refine ⟨1069049673243634856798425301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712699782162423237865616867 1069049673243634856798425301)
            ·
              refine ⟨25055851716647691956213093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1069049673243634856798425301 25055851716647691956213093)
              ·
                refine ⟨4697972196871442241789955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25055851716647691956213093 4697972196871442241789955)
                ·
                  refine ⟨7046958295307163362684933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697972196871442241789955 7046958295307163362684933)
                  ·
                    refine ⟨1321304680370093130503425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7046958295307163362684933 1321304680370093130503425)
                    ·
                      rfl

theorem cell23_7719695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 1, 4].length) (baseStart_7719695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719695 prefixEnd_7719695 := by exact prefixLift 7719695
  have htrace : WordTrace (prefixWord ++ tailWord_7719695) baseStart_7719695 baseEnd_7719695 := by
    simpa [prefixWord, tailWord_7719695, baseEnd_7719695] using wordTrace_append hprefix tailTrace_7719695
  have hstable : (prefixWord ++ tailWord_7719695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719695).length < 2 ^ (prefixWord ++ tailWord_7719695).sum := by decide
  have hdescent : baseEnd_7719695 < baseStart_7719695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719708 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 6]
def baseStart_7719708 : Nat := 118140960795 + 7719708 * 2 ^ 59
def prefixEnd_7719708 : Nat := 4983230072969 + 3 ^ 40 * 7719708 * 2
def baseEnd_7719708 : Nat := 440435635150976426738635

theorem tailTrace_7719708 : CollatzResearch.WordTrace tailWord_7719708 prefixEnd_7719708 440435635150976426738635 := by
  unfold tailWord_7719708
  simp only [CollatzResearch.WordTrace]
  refine ⟨140780440958411906003319889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187707254611215874671093185 140780440958411906003319889)
  ·
    refine ⟨105585330718808929502489917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140780440958411906003319889 105585330718808929502489917)
    ·
      refine ⟨39594499019553348563433719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105585330718808929502489917 39594499019553348563433719)
      ·
        refine ⟨59391748529330022845150579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39594499019553348563433719 59391748529330022845150579)
        ·
          refine ⟨89087622793995034267725869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59391748529330022845150579 89087622793995034267725869)
          ·
            refine ⟨33407858547748137850397201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89087622793995034267725869 33407858547748137850397201)
            ·
              refine ⟨25055893910811103387797901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33407858547748137850397201 25055893910811103387797901)
              ·
                refine ⟨9395960216554163770424213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25055893910811103387797901 9395960216554163770424213)
                ·
                  refine ⟨440435635150976426738635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9395960216554163770424213 440435635150976426738635)
                  ·
                    rfl

theorem cell23_7719708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_7719708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719708 prefixEnd_7719708 := by exact prefixLift 7719708
  have htrace : WordTrace (prefixWord ++ tailWord_7719708) baseStart_7719708 baseEnd_7719708 := by
    simpa [prefixWord, tailWord_7719708, baseEnd_7719708] using wordTrace_append hprefix tailTrace_7719708
  have hstable : (prefixWord ++ tailWord_7719708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719708).length < 2 ^ (prefixWord ++ tailWord_7719708).sum := by decide
  have hdescent : baseEnd_7719708 < baseStart_7719708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719722 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7719722 : Nat := 118140960795 + 7719722 * 2 ^ 59
def prefixEnd_7719722 : Nat := 4983230072969 + 3 ^ 40 * 7719722 * 2
def baseEnd_7719722 : Nat := 3963927905087950785872651

theorem tailTrace_7719722 : CollatzResearch.WordTrace tailWord_7719722 prefixEnd_7719722 3963927905087950785872651 := by
  unfold tailWord_7719722
  simp only [CollatzResearch.WordTrace]
  refine ⟨70390348134693273099412355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187707595025848728265099613 70390348134693273099412355)
  ·
    refine ⟨105585522202039909649118533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70390348134693273099412355 105585522202039909649118533)
    ·
      refine ⟨19797285412882483059209725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105585522202039909649118533 19797285412882483059209725)
      ·
        refine ⟨7423982029830931147203647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19797285412882483059209725 7423982029830931147203647)
        ·
          refine ⟨11135973044746396720805471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7423982029830931147203647 11135973044746396720805471)
          ·
            refine ⟨16703959567119595081208207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11135973044746396720805471 16703959567119595081208207)
            ·
              refine ⟨25055939350679392621812311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16703959567119595081208207 25055939350679392621812311)
              ·
                refine ⟨37583909026019088932718467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25055939350679392621812311 37583909026019088932718467)
                ·
                  refine ⟨56375863539028633399077701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37583909026019088932718467 56375863539028633399077701)
                  ·
                    refine ⟨10570474413567868762327069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56375863539028633399077701 10570474413567868762327069)
                    ·
                      refine ⟨3963927905087950785872651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10570474413567868762327069 3963927905087950785872651)
                      ·
                        rfl

theorem cell23_7719722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7719722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719722 prefixEnd_7719722 := by exact prefixLift 7719722
  have htrace : WordTrace (prefixWord ++ tailWord_7719722) baseStart_7719722 baseEnd_7719722 := by
    simpa [prefixWord, tailWord_7719722, baseEnd_7719722] using wordTrace_append hprefix tailTrace_7719722
  have hstable : (prefixWord ++ tailWord_7719722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719722).length < 2 ^ (prefixWord ++ tailWord_7719722).sum := by decide
  have hdescent : baseEnd_7719722 < baseStart_7719722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719742 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_7719742 : Nat := 118140960795 + 7719742 * 2 ^ 59
def prefixEnd_7719742 : Nat := 4983230072969 + 3 ^ 40 * 7719742 * 2
def baseEnd_7719742 : Nat := 440437574966782300846951

theorem tailTrace_7719742 : CollatzResearch.WordTrace tailWord_7719742 prefixEnd_7719742 440437574966782300846951 := by
  unfold tailWord_7719742
  simp only [CollatzResearch.WordTrace]
  refine ⟨35195265249837579476672185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187708081332467090542251653 35195265249837579476672185)
  ·
    refine ⟨26396448937378184607504139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35195265249837579476672185 26396448937378184607504139)
    ·
      refine ⟨39594673406067276911256209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26396448937378184607504139 39594673406067276911256209)
      ·
        refine ⟨29696005054550457683442157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39594673406067276911256209 29696005054550457683442157)
        ·
          refine ⟨11136001895456421631290809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29696005054550457683442157 11136001895456421631290809)
          ·
            refine ⟨8352001421592316223468107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11136001895456421631290809 8352001421592316223468107)
            ·
              refine ⟨12528002132388474335202161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8352001421592316223468107 12528002132388474335202161)
              ·
                refine ⟨9396001599291355751401621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12528002132388474335202161 9396001599291355751401621)
                ·
                  refine ⟨440437574966782300846951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9396001599291355751401621 440437574966782300846951)
                  ·
                    rfl

theorem cell23_7719742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_7719742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719742 prefixEnd_7719742 := by exact prefixLift 7719742
  have htrace : WordTrace (prefixWord ++ tailWord_7719742) baseStart_7719742 baseEnd_7719742 := by
    simpa [prefixWord, tailWord_7719742, baseEnd_7719742] using wordTrace_append hprefix tailTrace_7719742
  have hstable : (prefixWord ++ tailWord_7719742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719742).length < 2 ^ (prefixWord ++ tailWord_7719742).sum := by decide
  have hdescent : baseEnd_7719742 < baseStart_7719742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719752 : List Nat := [2, 1, 3, 1, 1, 3, 1, 6, 1, 1, 3]
def baseStart_7719752 : Nat := 118140960795 + 7719752 * 2 ^ 59
def prefixEnd_7719752 : Nat := 4983230072969 + 3 ^ 40 * 7719752 * 2
def baseEnd_7719752 : Nat := 3963943309507585668497513

theorem tailTrace_7719752 : CollatzResearch.WordTrace tailWord_7719752 prefixEnd_7719752 3963943309507585668497513 := by
  unfold tailWord_7719752
  simp only [CollatzResearch.WordTrace]
  refine ⟨140781243364332203760620755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187708324485776271680827673 140781243364332203760620755)
  ·
    refine ⟨211171865046498305640931133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140781243364332203760620755 211171865046498305640931133)
    ·
      refine ⟨79189449392436864615349175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211171865046498305640931133 79189449392436864615349175)
      ·
        refine ⟨118784174088655296923023763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79189449392436864615349175 118784174088655296923023763)
        ·
          refine ⟨178176261132982945384535645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118784174088655296923023763 178176261132982945384535645)
          ·
            refine ⟨66816097924868604519200867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178176261132982945384535645 66816097924868604519200867)
            ·
              refine ⟨100224146887302906778801301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66816097924868604519200867 100224146887302906778801301)
              ·
                refine ⟨4698006885342323755256311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100224146887302906778801301 4698006885342323755256311)
                ·
                  refine ⟨7047010328013485632884467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4698006885342323755256311 7047010328013485632884467)
                  ·
                    refine ⟨10570515492020228449326701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7047010328013485632884467 10570515492020228449326701)
                    ·
                      refine ⟨3963943309507585668497513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10570515492020228449326701 3963943309507585668497513)
                      ·
                        rfl

theorem cell23_7719752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_7719752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719752 prefixEnd_7719752 := by exact prefixLift 7719752
  have htrace : WordTrace (prefixWord ++ tailWord_7719752) baseStart_7719752 baseEnd_7719752 := by
    simpa [prefixWord, tailWord_7719752, baseEnd_7719752] using wordTrace_append hprefix tailTrace_7719752
  have hstable : (prefixWord ++ tailWord_7719752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719752).length < 2 ^ (prefixWord ++ tailWord_7719752).sum := by decide
  have hdescent : baseEnd_7719752 < baseStart_7719752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719758 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_7719758 : Nat := 118140960795 + 7719758 * 2 ^ 59
def prefixEnd_7719758 : Nat := 4983230072969 + 3 ^ 40 * 7719758 * 2
def baseEnd_7719758 : Nat := 3963946390391512645022485

theorem tailTrace_7719758 : CollatzResearch.WordTrace tailWord_7719758 prefixEnd_7719758 3963946390391512645022485 := by
  unfold tailWord_7719758
  simp only [CollatzResearch.WordTrace]
  refine ⟨35195338195830333818244991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187708470377761780363973285 35195338195830333818244991)
  ·
    refine ⟨52793007293745500727367487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35195338195830333818244991 52793007293745500727367487)
    ·
      refine ⟨79189510940618251091051231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52793007293745500727367487 79189510940618251091051231)
      ·
        refine ⟨118784266410927376636576847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79189510940618251091051231 118784266410927376636576847)
        ·
          refine ⟨178176399616391064954865271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118784266410927376636576847 178176399616391064954865271)
          ·
            refine ⟨267264599424586597432297907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178176399616391064954865271 267264599424586597432297907)
            ·
              refine ⟨400896899136879896148446861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267264599424586597432297907 400896899136879896148446861)
              ·
                refine ⟨150336337176329961055667573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400896899136879896148446861 150336337176329961055667573)
                ·
                  refine ⟨14094031610280933848968835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150336337176329961055667573 14094031610280933848968835)
                  ·
                    refine ⟨21141047415421400773453253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14094031610280933848968835 21141047415421400773453253)
                    ·
                      refine ⟨3963946390391512645022485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21141047415421400773453253 3963946390391512645022485)
                      ·
                        rfl

theorem cell23_7719758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_7719758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719758 prefixEnd_7719758 := by exact prefixLift 7719758
  have htrace : WordTrace (prefixWord ++ tailWord_7719758) baseStart_7719758 baseEnd_7719758 := by
    simpa [prefixWord, tailWord_7719758, baseEnd_7719758] using wordTrace_append hprefix tailTrace_7719758
  have hstable : (prefixWord ++ tailWord_7719758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719758).length < 2 ^ (prefixWord ++ tailWord_7719758).sum := by decide
  have hdescent : baseEnd_7719758 < baseStart_7719758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719772 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 1, 5]
def baseStart_7719772 : Nat := 118140960795 + 7719772 * 2 ^ 59
def prefixEnd_7719772 : Nat := 4983230072969 + 3 ^ 40 * 7719772 * 2
def baseEnd_7719772 : Nat := 1321317859706891863415807

theorem tailTrace_7719772 : CollatzResearch.WordTrace tailWord_7719772 prefixEnd_7719772 1321317859706891863415807 := by
  unfold tailWord_7719772
  simp only [CollatzResearch.WordTrace]
  refine ⟨140781608094295975468484785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187708810792394633957979713 140781608094295975468484785)
  ·
    refine ⟨105586206070721981601363589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140781608094295975468484785 105586206070721981601363589)
    ·
      refine ⟨19797413638260371550255673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105586206070721981601363589 19797413638260371550255673)
      ·
        refine ⟨14848060228695278662691755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19797413638260371550255673 14848060228695278662691755)
        ·
          refine ⟨22272090343042917994037633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14848060228695278662691755 22272090343042917994037633)
          ·
            refine ⟨16704067757282188495528225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22272090343042917994037633 16704067757282188495528225)
            ·
              refine ⟨12528050817961641371646169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16704067757282188495528225 12528050817961641371646169)
              ·
                refine ⟨9396038113471231028734627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12528050817961641371646169 9396038113471231028734627)
                ·
                  refine ⟨14094057170206846543101941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9396038113471231028734627 14094057170206846543101941)
                  ·
                    refine ⟨1321317859706891863415807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14094057170206846543101941 1321317859706891863415807)
                    ·
                      rfl

theorem cell23_7719772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_7719772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719772 prefixEnd_7719772 := by exact prefixLift 7719772
  have htrace : WordTrace (prefixWord ++ tailWord_7719772) baseStart_7719772 baseEnd_7719772 := by
    simpa [prefixWord, tailWord_7719772, baseEnd_7719772] using wordTrace_append hprefix tailTrace_7719772
  have hstable : (prefixWord ++ tailWord_7719772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719772).length < 2 ^ (prefixWord ++ tailWord_7719772).sum := by decide
  have hdescent : baseEnd_7719772 < baseStart_7719772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719775 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 4]
def baseStart_7719775 : Nat := 118140960795 + 7719775 * 2 ^ 59
def prefixEnd_7719775 : Nat := 4983230072969 + 3 ^ 40 * 7719775 * 2
def baseEnd_7719775 : Nat := 3963955119562639078509907

theorem tailTrace_7719775 : CollatzResearch.WordTrace tailWord_7719775 prefixEnd_7719775 3963955119562639078509907 := by
  unfold tailWord_7719775
  simp only [CollatzResearch.WordTrace]
  refine ⟨281563325607581082449328779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187708883738387388299552519 281563325607581082449328779)
  ·
    refine ⟨422344988411371623673993169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281563325607581082449328779 422344988411371623673993169)
    ·
      refine ⟨316758741308528717755494877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422344988411371623673993169 316758741308528717755494877)
      ·
        refine ⟨118784527990698269158310579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316758741308528717755494877 118784527990698269158310579)
        ·
          refine ⟨178176791986047403737465869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118784527990698269158310579 178176791986047403737465869)
          ·
            refine ⟨66816296994767776401549701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178176791986047403737465869 66816296994767776401549701)
            ·
              refine ⟨12528055686518958075290569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66816296994767776401549701 12528055686518958075290569)
              ·
                refine ⟨9396041764889218556467927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12528055686518958075290569 9396041764889218556467927)
                ·
                  refine ⟨14094062647333827834701891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9396041764889218556467927 14094062647333827834701891)
                  ·
                    refine ⟨21141093971000741752052837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14094062647333827834701891 21141093971000741752052837)
                    ·
                      refine ⟨3963955119562639078509907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21141093971000741752052837 3963955119562639078509907)
                      ·
                        rfl

theorem cell23_7719775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_7719775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719775 prefixEnd_7719775 := by exact prefixLift 7719775
  have htrace : WordTrace (prefixWord ++ tailWord_7719775) baseStart_7719775 baseEnd_7719775 := by
    simpa [prefixWord, tailWord_7719775, baseEnd_7719775] using wordTrace_append hprefix tailTrace_7719775
  have hstable : (prefixWord ++ tailWord_7719775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719775).length < 2 ^ (prefixWord ++ tailWord_7719775).sum := by decide
  have hdescent : baseEnd_7719775 < baseStart_7719775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719788 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_7719788 : Nat := 118140960795 + 7719788 * 2 ^ 59
def prefixEnd_7719788 : Nat := 4983230072969 + 3 ^ 40 * 7719788 * 2
def baseEnd_7719788 : Nat := 3963961794811147527647347

theorem tailTrace_7719788 : CollatzResearch.WordTrace tailWord_7719788 prefixEnd_7719788 3963961794811147527647347 := by
  unfold tailWord_7719788
  simp only [CollatzResearch.WordTrace]
  refine ⟨140781899878266992834776009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187709199837689323779701345 140781899878266992834776009)
  ·
    refine ⟨105586424908700244626082007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140781899878266992834776009 105586424908700244626082007)
    ·
      refine ⟨158379637363050366939123011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105586424908700244626082007 158379637363050366939123011)
      ·
        refine ⟨237569456044575550408684517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158379637363050366939123011 237569456044575550408684517)
        ·
          refine ⟨44544273008357915701628347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237569456044575550408684517 44544273008357915701628347)
          ·
            refine ⟨66816409512536873552442521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44544273008357915701628347 66816409512536873552442521)
            ·
              refine ⟨50112307134402655164331891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66816409512536873552442521 50112307134402655164331891)
              ·
                refine ⟨75168460701603982746497837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50112307134402655164331891 75168460701603982746497837)
                ·
                  refine ⟨28188172763101493529936689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75168460701603982746497837 28188172763101493529936689)
                  ·
                    refine ⟨21141129572326120147452517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28188172763101493529936689 21141129572326120147452517)
                    ·
                      refine ⟨3963961794811147527647347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21141129572326120147452517 3963961794811147527647347)
                      ·
                        rfl

theorem cell23_7719788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_7719788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719788 prefixEnd_7719788 := by exact prefixLift 7719788
  have htrace : WordTrace (prefixWord ++ tailWord_7719788) baseStart_7719788 baseEnd_7719788 := by
    simpa [prefixWord, tailWord_7719788, baseEnd_7719788] using wordTrace_append hprefix tailTrace_7719788
  have hstable : (prefixWord ++ tailWord_7719788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719788).length < 2 ^ (prefixWord ++ tailWord_7719788).sum := by decide
  have hdescent : baseEnd_7719788 < baseStart_7719788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719795 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 1, 2, 3]
def baseStart_7719795 : Nat := 118140960795 + 7719795 * 2 ^ 59
def prefixEnd_7719795 : Nat := 4983230072969 + 3 ^ 40 * 7719795 * 2
def baseEnd_7719795 : Nat := 3963965389175729000259815

theorem tailTrace_7719795 : CollatzResearch.WordTrace tailWord_7719795 prefixEnd_7719795 3963965389175729000259815 := by
  unfold tailWord_7719795
  simp only [CollatzResearch.WordTrace]
  refine ⟨281564055067508625865056839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187709370045005750576704559 281564055067508625865056839)
  ·
    refine ⟨422346082601262938797585259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281564055067508625865056839 422346082601262938797585259)
    ·
      refine ⟨633519123901894408196377889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422346082601262938797585259 633519123901894408196377889)
      ·
        refine ⟨475139342926420806147283417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633519123901894408196377889 475139342926420806147283417)
        ·
          refine ⟨356354507194815604610462563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475139342926420806147283417 356354507194815604610462563)
          ·
            refine ⟨534531760792223406915693845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356354507194815604610462563 534531760792223406915693845)
            ·
              refine ⟨25056176287135472199173149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 534531760792223406915693845 25056176287135472199173149)
              ·
                refine ⟨9396066107675802074689931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25056176287135472199173149 9396066107675802074689931)
                ·
                  refine ⟨14094099161513703112034897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9396066107675802074689931 14094099161513703112034897)
                  ·
                    refine ⟨10570574371135277334026173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14094099161513703112034897 10570574371135277334026173)
                    ·
                      refine ⟨3963965389175729000259815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10570574371135277334026173 3963965389175729000259815)
                      ·
                        rfl

theorem cell23_7719795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 2, 3].length) (baseStart_7719795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719795 prefixEnd_7719795 := by exact prefixLift 7719795
  have htrace : WordTrace (prefixWord ++ tailWord_7719795) baseStart_7719795 baseEnd_7719795 := by
    simpa [prefixWord, tailWord_7719795, baseEnd_7719795] using wordTrace_append hprefix tailTrace_7719795
  have hstable : (prefixWord ++ tailWord_7719795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719795).length < 2 ^ (prefixWord ++ tailWord_7719795).sum := by decide
  have hdescent : baseEnd_7719795 < baseStart_7719795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719808 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 3]
def baseStart_7719808 : Nat := 118140960795 + 7719808 * 2 ^ 59
def prefixEnd_7719808 : Nat := 4983230072969 + 3 ^ 40 * 7719808 * 2
def baseEnd_7719808 : Nat := 3963972064424237449397255

theorem tailTrace_7719808 : CollatzResearch.WordTrace tailWord_7719808 prefixEnd_7719808 3963972064424237449397255 := by
  unfold tailWord_7719808
  simp only [CollatzResearch.WordTrace]
  refine ⟨140782264608230764542640039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187709686144307686056853385 140782264608230764542640039)
  ·
    refine ⟨211173396912346146813960059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140782264608230764542640039 211173396912346146813960059)
    ·
      refine ⟨316760095368519220220940089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211173396912346146813960059 316760095368519220220940089)
      ·
        refine ⟨237570071526389415165705067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316760095368519220220940089 237570071526389415165705067)
        ·
          refine ⟨356355107289584122748557601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237570071526389415165705067 356355107289584122748557601)
          ·
            refine ⟨267266330467188092061418201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356355107289584122748557601 267266330467188092061418201)
            ·
              refine ⟨200449747850391069046063651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267266330467188092061418201 200449747850391069046063651)
              ·
                refine ⟨300674621775586603569095477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200449747850391069046063651 300674621775586603569095477)
                ·
                  refine ⟨28188245791461244084602701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300674621775586603569095477 28188245791461244084602701)
                  ·
                    refine ⟨10570592171797966531726013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28188245791461244084602701 10570592171797966531726013)
                    ·
                      refine ⟨3963972064424237449397255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10570592171797966531726013 3963972064424237449397255)
                      ·
                        rfl

theorem cell23_7719808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_7719808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719808 prefixEnd_7719808 := by exact prefixLift 7719808
  have htrace : WordTrace (prefixWord ++ tailWord_7719808) baseStart_7719808 baseEnd_7719808 := by
    simpa [prefixWord, tailWord_7719808, baseEnd_7719808] using wordTrace_append hprefix tailTrace_7719808
  have hstable : (prefixWord ++ tailWord_7719808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719808).length < 2 ^ (prefixWord ++ tailWord_7719808).sum := by decide
  have hdescent : baseEnd_7719808 < baseStart_7719808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719826 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_7719826 : Nat := 118140960795 + 7719826 * 2 ^ 59
def prefixEnd_7719826 : Nat := 4983230072969 + 3 ^ 40 * 7719826 * 2
def baseEnd_7719826 : Nat := 3963981307076018378972173

theorem tailTrace_7719826 : CollatzResearch.WordTrace tailWord_7719826 prefixEnd_7719826 3963981307076018378972173 := by
  unfold tailWord_7719826
  simp only [CollatzResearch.WordTrace]
  refine ⟨70391296432599079539858833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187710123820264212106290221 70391296432599079539858833)
  ·
    refine ⟨52793472324449309654894125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70391296432599079539858833 52793472324449309654894125)
    ·
      refine ⟨19797552121668491120585297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52793472324449309654894125 19797552121668491120585297)
      ·
        refine ⟨14848164091251368340438973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19797552121668491120585297 14848164091251368340438973)
        ·
          refine ⟨5568061534219263127664615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14848164091251368340438973 5568061534219263127664615)
          ·
            refine ⟨8352092301328894691496923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568061534219263127664615 8352092301328894691496923)
            ·
              refine ⟨12528138451993342037245385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8352092301328894691496923 12528138451993342037245385)
              ·
                refine ⟨9396103838995006527934039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12528138451993342037245385 9396103838995006527934039)
                ·
                  refine ⟨14094155758492509791901059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9396103838995006527934039 14094155758492509791901059)
                  ·
                    refine ⟨21141233637738764687851589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14094155758492509791901059 21141233637738764687851589)
                    ·
                      refine ⟨3963981307076018378972173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21141233637738764687851589 3963981307076018378972173)
                      ·
                        rfl

theorem cell23_7719826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_7719826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719826 prefixEnd_7719826 := by exact prefixLift 7719826
  have htrace : WordTrace (prefixWord ++ tailWord_7719826) baseStart_7719826 baseEnd_7719826 := by
    simpa [prefixWord, tailWord_7719826, baseEnd_7719826] using wordTrace_append hprefix tailTrace_7719826
  have hstable : (prefixWord ++ tailWord_7719826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719826).length < 2 ^ (prefixWord ++ tailWord_7719826).sum := by decide
  have hdescent : baseEnd_7719826 < baseStart_7719826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719842 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_7719842 : Nat := 118140960795 + 7719842 * 2 ^ 59
def prefixEnd_7719842 : Nat := 4983230072969 + 3 ^ 40 * 7719842 * 2
def baseEnd_7719842 : Nat := 3963989522766490316372099

theorem tailTrace_7719842 : CollatzResearch.WordTrace tailWord_7719842 prefixEnd_7719842 3963989522766490316372099 := by
  unfold tailWord_7719842
  simp only [CollatzResearch.WordTrace]
  refine ⟨70391442324584588223004445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187710512865558901928011853 70391442324584588223004445)
  ·
    refine ⟨26396790871719220583626667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70391442324584588223004445 26396790871719220583626667)
    ·
      refine ⟨39595186307578830875440001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26396790871719220583626667 39595186307578830875440001)
      ·
        refine ⟨29696389730684123156580001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39595186307578830875440001 29696389730684123156580001)
        ·
          refine ⟨22272292298013092367435001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29696389730684123156580001 22272292298013092367435001)
          ·
            refine ⟨16704219223509819275576251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22272292298013092367435001 16704219223509819275576251)
            ·
              refine ⟨25056328835264728913364377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16704219223509819275576251 25056328835264728913364377)
              ·
                refine ⟨18792246626448546685023283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25056328835264728913364377 18792246626448546685023283)
                ·
                  refine ⟨28188369939672820027534925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18792246626448546685023283 28188369939672820027534925)
                  ·
                    refine ⟨10570638727377307510325597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28188369939672820027534925 10570638727377307510325597)
                    ·
                      refine ⟨3963989522766490316372099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10570638727377307510325597 3963989522766490316372099)
                      ·
                        rfl

theorem cell23_7719842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_7719842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719842 prefixEnd_7719842 := by exact prefixLift 7719842
  have htrace : WordTrace (prefixWord ++ tailWord_7719842) baseStart_7719842 baseEnd_7719842 := by
    simpa [prefixWord, tailWord_7719842, baseEnd_7719842] using wordTrace_append hprefix tailTrace_7719842
  have hstable : (prefixWord ++ tailWord_7719842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719842).length < 2 ^ (prefixWord ++ tailWord_7719842).sum := by decide
  have hdescent : baseEnd_7719842 < baseStart_7719842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719860 : List Nat := [2, 5, 2, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_7719860 : Nat := 118140960795 + 7719860 * 2 ^ 59
def prefixEnd_7719860 : Nat := 4983230072969 + 3 ^ 40 * 7719860 * 2
def baseEnd_7719860 : Nat := 3963998765418271245947017

theorem tailTrace_7719860 : CollatzResearch.WordTrace tailWord_7719860 prefixEnd_7719860 3963998765418271245947017 := by
  unfold tailWord_7719860
  simp only [CollatzResearch.WordTrace]
  refine ⟨140783212906136570983086517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187710950541515427977448689 140783212906136570983086517)
  ·
    refine ⟨13198426209950303529664361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140783212906136570983086517 13198426209950303529664361)
    ·
      refine ⟨9898819657462727647248271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13198426209950303529664361 9898819657462727647248271)
      ·
        refine ⟨14848229486194091470872407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9898819657462727647248271 14848229486194091470872407)
        ·
          refine ⟨22272344229291137206308611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14848229486194091470872407 22272344229291137206308611)
          ·
            refine ⟨33408516343936705809462917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22272344229291137206308611 33408516343936705809462917)
            ·
              refine ⟨6264096814488132339274297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33408516343936705809462917 6264096814488132339274297)
              ·
                refine ⟨4698072610866099254455723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6264096814488132339274297 4698072610866099254455723)
                ·
                  refine ⟨7047108916299148881683585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4698072610866099254455723 7047108916299148881683585)
                  ·
                    refine ⟨5285331687224361661262689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7047108916299148881683585 5285331687224361661262689)
                    ·
                      refine ⟨3963998765418271245947017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285331687224361661262689 3963998765418271245947017)
                      ·
                        rfl

theorem cell23_7719860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_7719860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719860 prefixEnd_7719860 := by exact prefixLift 7719860
  have htrace : WordTrace (prefixWord ++ tailWord_7719860) baseStart_7719860 baseEnd_7719860 := by
    simpa [prefixWord, tailWord_7719860, baseEnd_7719860] using wordTrace_append hprefix tailTrace_7719860
  have hstable : (prefixWord ++ tailWord_7719860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719860).length < 2 ^ (prefixWord ++ tailWord_7719860).sum := by decide
  have hdescent : baseEnd_7719860 < baseStart_7719860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719882 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2]
def baseStart_7719882 : Nat := 118140960795 + 7719882 * 2 ^ 59
def prefixEnd_7719882 : Nat := 4983230072969 + 3 ^ 40 * 7719882 * 2
def baseEnd_7719882 : Nat := 3964010061992670159871915

theorem tailTrace_7719882 : CollatzResearch.WordTrace tailWord_7719882 prefixEnd_7719882 3964010061992670159871915 := by
  unfold tailWord_7719882
  simp only [CollatzResearch.WordTrace]
  refine ⟨70391807054548359930868475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187711485478795626482315933 70391807054548359930868475)
  ·
    refine ⟨105587710581822539896302713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70391807054548359930868475 105587710581822539896302713)
    ·
      refine ⟨79190782936366904922227035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105587710581822539896302713 79190782936366904922227035)
      ·
        refine ⟨118786174404550357383340553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79190782936366904922227035 118786174404550357383340553)
        ·
          refine ⟨89089630803412768037505415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118786174404550357383340553 89089630803412768037505415)
          ·
            refine ⟨133634446205119152056258123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89089630803412768037505415 133634446205119152056258123)
            ·
              refine ⟨200451669307678728084387185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133634446205119152056258123 200451669307678728084387185)
              ·
                refine ⟨150338751980759046063290389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200451669307678728084387185 150338751980759046063290389)
                ·
                  refine ⟨7047128999098080284216737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150338751980759046063290389 7047128999098080284216737)
                  ·
                    refine ⟨5285346749323560213162553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7047128999098080284216737 5285346749323560213162553)
                    ·
                      refine ⟨3964010061992670159871915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285346749323560213162553 3964010061992670159871915)
                      ·
                        rfl

theorem cell23_7719882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_7719882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719882 prefixEnd_7719882 := by exact prefixLift 7719882
  have htrace : WordTrace (prefixWord ++ tailWord_7719882) baseStart_7719882 baseEnd_7719882 := by
    simpa [prefixWord, tailWord_7719882, baseEnd_7719882] using wordTrace_append hprefix tailTrace_7719882
  have hstable : (prefixWord ++ tailWord_7719882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719882).length < 2 ^ (prefixWord ++ tailWord_7719882).sum := by decide
  have hdescent : baseEnd_7719882 < baseStart_7719882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719903 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 1, 3, 2]
def baseStart_7719903 : Nat := 118140960795 + 7719903 * 2 ^ 59
def prefixEnd_7719903 : Nat := 4983230072969 + 3 ^ 40 * 7719903 * 2
def baseEnd_7719903 : Nat := 3964020845086414577709319

theorem tailTrace_7719903 : CollatzResearch.WordTrace tailWord_7719903 prefixEnd_7719903 3964020845086414577709319 := by
  unfold tailWord_7719903
  simp only [CollatzResearch.WordTrace]
  refine ⟨281567994151117360309988363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187711996100744906873325575 281567994151117360309988363)
  ·
    refine ⟨422351991226676040464982545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281567994151117360309988363 422351991226676040464982545)
    ·
      refine ⟨316763993420007030348736909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422351991226676040464982545 316763993420007030348736909)
      ·
        refine ⟨118786497532502636380776341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316763993420007030348736909 118786497532502636380776341)
        ·
          refine ⟨5568117071836061080348891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118786497532502636380776341 5568117071836061080348891)
          ·
            refine ⟨8352175607754091620523337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568117071836061080348891 8352175607754091620523337)
            ·
              refine ⟨6264131705815568715392503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8352175607754091620523337 6264131705815568715392503)
              ·
                refine ⟨9396197558723353073088755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6264131705815568715392503 9396197558723353073088755)
                ·
                  refine ⟨14094296338085029609633133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9396197558723353073088755 14094296338085029609633133)
                  ·
                    refine ⟨5285361126781886103612425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14094296338085029609633133 5285361126781886103612425)
                    ·
                      refine ⟨3964020845086414577709319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285361126781886103612425 3964020845086414577709319)
                      ·
                        rfl

theorem cell23_7719903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_7719903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719903 prefixEnd_7719903 := by exact prefixLift 7719903
  have htrace : WordTrace (prefixWord ++ tailWord_7719903) baseStart_7719903 baseEnd_7719903 := by
    simpa [prefixWord, tailWord_7719903, baseEnd_7719903] using wordTrace_append hprefix tailTrace_7719903
  have hstable : (prefixWord ++ tailWord_7719903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719903).length < 2 ^ (prefixWord ++ tailWord_7719903).sum := by decide
  have hdescent : baseEnd_7719903 < baseStart_7719903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719928 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_7719928 : Nat := 118140960795 + 7719928 * 2 ^ 59
def prefixEnd_7719928 : Nat := 4983230072969 + 3 ^ 40 * 7719928 * 2
def baseEnd_7719928 : Nat := 3964033682102776979896703

theorem tailTrace_7719928 : CollatzResearch.WordTrace tailWord_7719928 prefixEnd_7719928 3964033682102776979896703 := by
  unfold tailWord_7719928
  simp only [CollatzResearch.WordTrace]
  refine ⟨140784452988013394789824219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187712603984017859719765625 140784452988013394789824219)
  ·
    refine ⟨211176679482020092184736329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140784452988013394789824219 211176679482020092184736329)
    ·
      refine ⟨158382509611515069138552247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211176679482020092184736329 158382509611515069138552247)
      ·
        refine ⟨237573764417272603707828371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158382509611515069138552247 237573764417272603707828371)
        ·
          refine ⟨356360646625908905561742557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237573764417272603707828371 356360646625908905561742557)
          ·
            refine ⟨133635242484715839585653459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356360646625908905561742557 133635242484715839585653459)
            ·
              refine ⟨200452863727073759378480189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133635242484715839585653459 200452863727073759378480189)
              ·
                refine ⟨75169823897652659766930071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200452863727073759378480189 75169823897652659766930071)
                ·
                  refine ⟨112754735846478989650395107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75169823897652659766930071 112754735846478989650395107)
                  ·
                    refine ⟨169132103769718484475592661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112754735846478989650395107 169132103769718484475592661)
                    ·
                      refine ⟨3964033682102776979896703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169132103769718484475592661 3964033682102776979896703)
                      ·
                        rfl

theorem cell23_7719928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_7719928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719928 prefixEnd_7719928 := by exact prefixLift 7719928
  have htrace : WordTrace (prefixWord ++ tailWord_7719928) baseStart_7719928 baseEnd_7719928 := by
    simpa [prefixWord, tailWord_7719928, baseEnd_7719928] using wordTrace_append hprefix tailTrace_7719928
  have hstable : (prefixWord ++ tailWord_7719928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719928).length < 2 ^ (prefixWord ++ tailWord_7719928).sum := by decide
  have hdescent : baseEnd_7719928 < baseStart_7719928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719955 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 4]
def baseStart_7719955 : Nat := 118140960795 + 7719955 * 2 ^ 59
def prefixEnd_7719955 : Nat := 4983230072969 + 3 ^ 40 * 7719955 * 2
def baseEnd_7719955 : Nat := 3964047546080448374259079

theorem tailTrace_7719955 : CollatzResearch.WordTrace tailWord_7719955 prefixEnd_7719955 3964047546080448374259079 := by
  unfold tailWord_7719955
  simp only [CollatzResearch.WordTrace]
  refine ⟨281569890746928973190881319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187713260497952648793920879 281569890746928973190881319)
  ·
    refine ⟨422354836120393459786321979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281569890746928973190881319 422354836120393459786321979)
    ·
      refine ⟨633532254180590189679482969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422354836120393459786321979 633532254180590189679482969)
      ·
        refine ⟨475149190635442642259612227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633532254180590189679482969 475149190635442642259612227)
        ·
          refine ⟨712723785953163963389418341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475149190635442642259612227 712723785953163963389418341)
          ·
            refine ⟨133635709866218243135515939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 712723785953163963389418341 133635709866218243135515939)
            ·
              refine ⟨200453564799327364703273909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133635709866218243135515939 200453564799327364703273909)
              ·
                refine ⟨18792521699936940440931929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200453564799327364703273909 18792521699936940440931929)
                ·
                  refine ⟨14094391274952705330698947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18792521699936940440931929 14094391274952705330698947)
                  ·
                    refine ⟨21141586912429057996048421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14094391274952705330698947 21141586912429057996048421)
                    ·
                      refine ⟨3964047546080448374259079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21141586912429057996048421 3964047546080448374259079)
                      ·
                        rfl

theorem cell23_7719955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_7719955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719955 prefixEnd_7719955 := by exact prefixLift 7719955
  have htrace : WordTrace (prefixWord ++ tailWord_7719955) baseStart_7719955 baseEnd_7719955 := by
    simpa [prefixWord, tailWord_7719955, baseEnd_7719955] using wordTrace_append hprefix tailTrace_7719955
  have hstable : (prefixWord ++ tailWord_7719955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719955).length < 2 ^ (prefixWord ++ tailWord_7719955).sum := by decide
  have hdescent : baseEnd_7719955 < baseStart_7719955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7719972 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7719972 : Nat := 118140960795 + 7719972 * 2 ^ 59
def prefixEnd_7719972 : Nat := 4983230072969 + 3 ^ 40 * 7719972 * 2
def baseEnd_7719972 : Nat := 3964056275251574807746501

theorem tailTrace_7719972 : CollatzResearch.WordTrace tailWord_7719972 prefixEnd_7719972 3964056275251574807746501 := by
  unfold tailWord_7719972
  simp only [CollatzResearch.WordTrace]
  refine ⟨140785255393933692547125085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187713673858578256729500113 140785255393933692547125085)
  ·
    refine ⟨52794470772725134705171907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140785255393933692547125085 52794470772725134705171907)
    ·
      refine ⟨79191706159087702057757861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52794470772725134705171907 79191706159087702057757861)
      ·
        refine ⟨14848444904828944135829599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79191706159087702057757861 14848444904828944135829599)
        ·
          refine ⟨22272667357243416203744399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14848444904828944135829599 22272667357243416203744399)
          ·
            refine ⟨33409001035865124305616599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22272667357243416203744399 33409001035865124305616599)
            ·
              refine ⟨50113501553797686458424899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33409001035865124305616599 50113501553797686458424899)
              ·
                refine ⟨75170252330696529687637349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50113501553797686458424899 75170252330696529687637349)
                ·
                  refine ⟨14094422312005599316432003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75170252330696529687637349 14094422312005599316432003)
                  ·
                    refine ⟨21141633468008398974648005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14094422312005599316432003 21141633468008398974648005)
                    ·
                      refine ⟨3964056275251574807746501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21141633468008398974648005 3964056275251574807746501)
                      ·
                        rfl

theorem cell23_7719972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7719972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7719972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7719972 prefixEnd_7719972 := by exact prefixLift 7719972
  have htrace : WordTrace (prefixWord ++ tailWord_7719972) baseStart_7719972 baseEnd_7719972 := by
    simpa [prefixWord, tailWord_7719972, baseEnd_7719972] using wordTrace_append hprefix tailTrace_7719972
  have hstable : (prefixWord ++ tailWord_7719972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7719972).length < 2 ^ (prefixWord ++ tailWord_7719972).sum := by decide
  have hdescent : baseEnd_7719972 < baseStart_7719972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7719972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720005 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 2, 5, 3]
def baseStart_7720005 : Nat := 118140960795 + 7720005 * 2 ^ 59
def prefixEnd_7720005 : Nat := 4983230072969 + 3 ^ 40 * 7720005 * 2
def baseEnd_7720005 : Nat := 3964073220113173178633849

theorem tailTrace_7720005 : CollatzResearch.WordTrace tailWord_7720005 prefixEnd_7720005 3964073220113173178633849 := by
  unfold tailWord_7720005
  simp only [CollatzResearch.WordTrace]
  refine ⟨281571714396747831730201469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187714476264498554486800979 281571714396747831730201469)
  ·
    refine ⟨105589392898780436898825551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281571714396747831730201469 105589392898780436898825551)
    ·
      refine ⟨158384089348170655348238327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105589392898780436898825551 158384089348170655348238327)
      ·
        refine ⟨237576134022255983022357491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158384089348170655348238327 237576134022255983022357491)
        ·
          refine ⟨356364201033383974533536237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237576134022255983022357491 356364201033383974533536237)
          ·
            refine ⟨133636575387518990450076089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356364201033383974533536237 133636575387518990450076089)
            ·
              refine ⟨100227431540639242837557067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133636575387518990450076089 100227431540639242837557067)
              ·
                refine ⟨150341147310958864256335601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100227431540639242837557067 150341147310958864256335601)
                ·
                  refine ⟨112755860483219148192251701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150341147310958864256335601 112755860483219148192251701)
                  ·
                    refine ⟨10570861920301795143023597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112755860483219148192251701 10570861920301795143023597)
                    ·
                      refine ⟨3964073220113173178633849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10570861920301795143023597 3964073220113173178633849)
                      ·
                        rfl

theorem cell23_7720005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_7720005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720005 prefixEnd_7720005 := by exact prefixLift 7720005
  have htrace : WordTrace (prefixWord ++ tailWord_7720005) baseStart_7720005 baseEnd_7720005 := by
    simpa [prefixWord, tailWord_7720005, baseEnd_7720005] using wordTrace_append hprefix tailTrace_7720005
  have hstable : (prefixWord ++ tailWord_7720005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720005).length < 2 ^ (prefixWord ++ tailWord_7720005).sum := by decide
  have hdescent : baseEnd_7720005 < baseStart_7720005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720006 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_7720006 : Nat := 118140960795 + 7720006 * 2 ^ 59
def prefixEnd_7720006 : Nat := 4983230072969 + 3 ^ 40 * 7720006 * 2
def baseEnd_7720006 : Nat := 3964073733593827674721345

theorem tailTrace_7720006 : CollatzResearch.WordTrace tailWord_7720006 prefixEnd_7720006 3964073733593827674721345 := by
  unfold tailWord_7720006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8799117214679506528155871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187714500579829472600658581 8799117214679506528155871)
  ·
    refine ⟨13198675822019259792233807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8799117214679506528155871 13198675822019259792233807)
    ·
      refine ⟨19798013733028889688350711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13198675822019259792233807 19798013733028889688350711)
      ·
        refine ⟨29697020599543334532526067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19798013733028889688350711 29697020599543334532526067)
        ·
          refine ⟨44545530899315001798789101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29697020599543334532526067 44545530899315001798789101)
          ·
            refine ⟨16704574087243125674545913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44545530899315001798789101 16704574087243125674545913)
            ·
              refine ⟨12528430565432344255909435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16704574087243125674545913 12528430565432344255909435)
              ·
                refine ⟨18792645848148516383864153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12528430565432344255909435 18792645848148516383864153)
                ·
                  refine ⟨14094484386111387287898115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18792645848148516383864153 14094484386111387287898115)
                  ·
                    refine ⟨21141726579167080931847173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14094484386111387287898115 21141726579167080931847173)
                    ·
                      refine ⟨3964073733593827674721345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21141726579167080931847173 3964073733593827674721345)
                      ·
                        rfl

theorem cell23_7720006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_7720006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720006 prefixEnd_7720006 := by exact prefixLift 7720006
  have htrace : WordTrace (prefixWord ++ tailWord_7720006) baseStart_7720006 baseEnd_7720006 := by
    simpa [prefixWord, tailWord_7720006, baseEnd_7720006] using wordTrace_append hprefix tailTrace_7720006
  have hstable : (prefixWord ++ tailWord_7720006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720006).length < 2 ^ (prefixWord ++ tailWord_7720006).sum := by decide
  have hdescent : baseEnd_7720006 < baseStart_7720006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720042 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_7720042 : Nat := 118140960795 + 7720042 * 2 ^ 59
def prefixEnd_7720042 : Nat := 4983230072969 + 3 ^ 40 * 7720042 * 2
def baseEnd_7720042 : Nat := 1321364072965796511290393

theorem tailTrace_7720042 : CollatzResearch.WordTrace tailWord_7720042 prefixEnd_7720042 1321364072965796511290393 := by
  unfold tailWord_7720042
  simp only [CollatzResearch.WordTrace]
  refine ⟨70393265974403446762324595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187715375931742524699532253 70393265974403446762324595)
  ·
    refine ⟨105589898961605170143486893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70393265974403446762324595 105589898961605170143486893)
    ·
      refine ⟨39596212110601938803807585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105589898961605170143486893 39596212110601938803807585)
      ·
        refine ⟨29697159082951454102855689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39596212110601938803807585 29697159082951454102855689)
        ·
          refine ⟨22272869312213590577141767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29697159082951454102855689 22272869312213590577141767)
          ·
            refine ⟨33409303968320385865712651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22272869312213590577141767 33409303968320385865712651)
            ·
              refine ⟨50113955952480578798568977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33409303968320385865712651 50113955952480578798568977)
              ·
                refine ⟨37585466964360434098926733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50113955952480578798568977 37585466964360434098926733)
                ·
                  refine ⟨14094550111635162787097525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37585466964360434098926733 14094550111635162787097525)
                  ·
                    refine ⟨1321364072965796511290393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14094550111635162787097525 1321364072965796511290393)
                    ·
                      rfl

theorem cell23_7720042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_7720042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720042 prefixEnd_7720042 := by exact prefixLift 7720042
  have htrace : WordTrace (prefixWord ++ tailWord_7720042) baseStart_7720042 baseEnd_7720042 := by
    simpa [prefixWord, tailWord_7720042, baseEnd_7720042] using wordTrace_append hprefix tailTrace_7720042
  have hstable : (prefixWord ++ tailWord_7720042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720042).length < 2 ^ (prefixWord ++ tailWord_7720042).sum := by decide
  have hdescent : baseEnd_7720042 < baseStart_7720042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720096 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 3, 2, 2]
def baseStart_7720096 : Nat := 118140960795 + 7720096 * 2 ^ 59
def prefixEnd_7720096 : Nat := 4983230072969 + 3 ^ 40 * 7720096 * 2
def baseEnd_7720096 : Nat := 3964119946852732322595931

theorem tailTrace_7720096 : CollatzResearch.WordTrace tailWord_7720096 prefixEnd_7720096 3964119946852732322595931 := by
  unfold tailWord_7720096
  simp only [CollatzResearch.WordTrace]
  refine ⟨140787516719709077135882071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187716688959612102847842761 140787516719709077135882071)
  ·
    refine ⟨211181275079563615703823107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140787516719709077135882071 211181275079563615703823107)
    ·
      refine ⟨316771912619345423555734661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211181275079563615703823107 316771912619345423555734661)
      ·
        refine ⟨59394733616127266916700249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316771912619345423555734661 59394733616127266916700249)
        ·
          refine ⟨44546050212095450187525187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59394733616127266916700249 44546050212095450187525187)
          ·
            refine ⟨66819075318143175281287781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44546050212095450187525187 66819075318143175281287781)
            ·
              refine ⟨12528576622151845365241459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66819075318143175281287781 12528576622151845365241459)
              ·
                refine ⟨18792864933227768047862189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12528576622151845365241459 18792864933227768047862189)
                ·
                  refine ⟨7047324349960413017948321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18792864933227768047862189 7047324349960413017948321)
                  ·
                    refine ⟨5285493262470309763461241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7047324349960413017948321 5285493262470309763461241)
                    ·
                      refine ⟨3964119946852732322595931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285493262470309763461241 3964119946852732322595931)
                      ·
                        rfl

theorem cell23_7720096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_7720096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720096 prefixEnd_7720096 := by exact prefixLift 7720096
  have htrace : WordTrace (prefixWord ++ tailWord_7720096) baseStart_7720096 baseEnd_7720096 := by
    simpa [prefixWord, tailWord_7720096, baseEnd_7720096] using wordTrace_append hprefix tailTrace_7720096
  have hstable : (prefixWord ++ tailWord_7720096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720096).length < 2 ^ (prefixWord ++ tailWord_7720096).sum := by decide
  have hdescent : baseEnd_7720096 < baseStart_7720096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720106 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 1, 6]
def baseStart_7720106 : Nat := 118140960795 + 7720106 * 2 ^ 59
def prefixEnd_7720106 : Nat := 4983230072969 + 3 ^ 40 * 7720106 * 2
def baseEnd_7720106 : Nat := 1321375027219759094490295

theorem tailTrace_7720106 : CollatzResearch.WordTrace tailWord_7720106 prefixEnd_7720106 1321375027219759094490295 := by
  unfold tailWord_7720106
  simp only [CollatzResearch.WordTrace]
  refine ⟨70393849542345481494907043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187716932112921283986418781 70393849542345481494907043)
  ·
    refine ⟨105590774313518222242360565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70393849542345481494907043 105590774313518222242360565)
    ·
      refine ⟨9899135091892333335221303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105590774313518222242360565 9899135091892333335221303)
      ·
        refine ⟨14848702637838500002831955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9899135091892333335221303 14848702637838500002831955)
        ·
          refine ⟨22273053956757750004247933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14848702637838500002831955 22273053956757750004247933)
          ·
            refine ⟨8352395233784156251592975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22273053956757750004247933 8352395233784156251592975)
            ·
              refine ⟨12528592850676234377389463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8352395233784156251592975 12528592850676234377389463)
              ·
                refine ⟨18792889276014351566084195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12528592850676234377389463 18792889276014351566084195)
                ·
                  refine ⟨28189333914021527349126293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18792889276014351566084195 28189333914021527349126293)
                  ·
                    refine ⟨1321375027219759094490295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28189333914021527349126293 1321375027219759094490295)
                    ·
                      rfl

theorem cell23_7720106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_7720106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720106 prefixEnd_7720106 := by exact prefixLift 7720106
  have htrace : WordTrace (prefixWord ++ tailWord_7720106) baseStart_7720106 baseEnd_7720106 := by
    simpa [prefixWord, tailWord_7720106, baseEnd_7720106] using wordTrace_append hprefix tailTrace_7720106
  have hstable : (prefixWord ++ tailWord_7720106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720106).length < 2 ^ (prefixWord ++ tailWord_7720106).sum := by decide
  have hdescent : baseEnd_7720106 < baseStart_7720106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720109 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_7720109 : Nat := 118140960795 + 7720109 * 2 ^ 59
def prefixEnd_7720109 : Nat := 4983230072969 + 3 ^ 40 * 7720109 * 2
def baseEnd_7720109 : Nat := 3964126622101240771733371

theorem tailTrace_7720109 : CollatzResearch.WordTrace tailWord_7720109 prefixEnd_7720109 3964126622101240771733371 := by
  unfold tailWord_7720109
  simp only [CollatzResearch.WordTrace]
  refine ⟨281575507588371057491987381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187717005058914038327991587 281575507588371057491987381)
  ·
    refine ⟨26397703836409786639873817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281575507588371057491987381 26397703836409786639873817)
    ·
      refine ⟨19798277877307339979905363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26397703836409786639873817 19798277877307339979905363)
      ·
        refine ⟨29697416815961009969858045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19798277877307339979905363 29697416815961009969858045)
        ·
          refine ⟨11136531305985378738696767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29697416815961009969858045 11136531305985378738696767)
          ·
            refine ⟨16704796958978068108045151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11136531305985378738696767 16704796958978068108045151)
            ·
              refine ⟨25057195438467102162067727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16704796958978068108045151 25057195438467102162067727)
              ·
                refine ⟨37585793157700653243101591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25057195438467102162067727 37585793157700653243101591)
                ·
                  refine ⟨56378689736550979864652387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37585793157700653243101591 56378689736550979864652387)
                  ·
                    refine ⟨84568034604826469796978581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56378689736550979864652387 84568034604826469796978581)
                    ·
                      refine ⟨3964126622101240771733371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84568034604826469796978581 3964126622101240771733371)
                      ·
                        rfl

theorem cell23_7720109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_7720109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720109 prefixEnd_7720109 := by exact prefixLift 7720109
  have htrace : WordTrace (prefixWord ++ tailWord_7720109) baseStart_7720109 baseEnd_7720109 := by
    simpa [prefixWord, tailWord_7720109, baseEnd_7720109] using wordTrace_append hprefix tailTrace_7720109
  have hstable : (prefixWord ++ tailWord_7720109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720109).length < 2 ^ (prefixWord ++ tailWord_7720109).sum := by decide
  have hdescent : baseEnd_7720109 < baseStart_7720109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720115 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 2, 7]
def baseStart_7720115 : Nat := 118140960795 + 7720115 * 2 ^ 59
def prefixEnd_7720115 : Nat := 4983230072969 + 3 ^ 40 * 7720115 * 2
def baseEnd_7720115 : Nat := 1321376567661722582752781

theorem tailTrace_7720115 : CollatzResearch.WordTrace tailWord_7720115 prefixEnd_7720115 1321376567661722582752781 := by
  unfold tailWord_7720115
  simp only [CollatzResearch.WordTrace]
  refine ⟨281575726426349320516705799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187717150950899547011137199 281575726426349320516705799)
  ·
    refine ⟨422363589639523980775058699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281575726426349320516705799 422363589639523980775058699)
    ·
      refine ⟨633545384459285971162588049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422363589639523980775058699 633545384459285971162588049)
      ·
        refine ⟨475159038344464478371941037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633545384459285971162588049 475159038344464478371941037)
        ·
          refine ⟨178184639379174179389477889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475159038344464478371941037 178184639379174179389477889)
          ·
            refine ⟨133638479534380634542108417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178184639379174179389477889 133638479534380634542108417)
            ·
              refine ⟨100228859650785475906581313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133638479534380634542108417 100228859650785475906581313)
              ·
                refine ⟨75171644738089106929935985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100228859650785475906581313 75171644738089106929935985)
                ·
                  refine ⟨56378733553566830197451989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75171644738089106929935985 56378733553566830197451989)
                  ·
                    refine ⟨1321376567661722582752781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56378733553566830197451989 1321376567661722582752781)
                    ·
                      rfl

theorem cell23_7720115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 7].length) (baseStart_7720115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720115 prefixEnd_7720115 := by exact prefixLift 7720115
  have htrace : WordTrace (prefixWord ++ tailWord_7720115) baseStart_7720115 baseEnd_7720115 := by
    simpa [prefixWord, tailWord_7720115, baseEnd_7720115] using wordTrace_append hprefix tailTrace_7720115
  have hstable : (prefixWord ++ tailWord_7720115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720115).length < 2 ^ (prefixWord ++ tailWord_7720115).sum := by decide
  have hdescent : baseEnd_7720115 < baseStart_7720115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720135 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_7720135 : Nat := 118140960795 + 7720135 * 2 ^ 59
def prefixEnd_7720135 : Nat := 4983230072969 + 3 ^ 40 * 7720135 * 2
def baseEnd_7720135 : Nat := 3964139972598257670008251

theorem tailTrace_7720135 : CollatzResearch.WordTrace tailWord_7720135 prefixEnd_7720135 3964139972598257670008251 := by
  unfold tailWord_7720135
  simp only [CollatzResearch.WordTrace]
  refine ⟨281576455886276863932433859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187717637257517909288289239 281576455886276863932433859)
  ·
    refine ⟨422364683829415295898650789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281576455886276863932433859 422364683829415295898650789)
    ·
      refine ⟨79193378218015367980997023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422364683829415295898650789 79193378218015367980997023)
      ·
        refine ⟨118790067327023051971495535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79193378218015367980997023 118790067327023051971495535)
        ·
          refine ⟨178185100990534577957243303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118790067327023051971495535 178185100990534577957243303)
          ·
            refine ⟨267277651485801866935864955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178185100990534577957243303 267277651485801866935864955)
            ·
              refine ⟨400916477228702800403797433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267277651485801866935864955 400916477228702800403797433)
              ·
                refine ⟨300687357921527100302848075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400916477228702800403797433 300687357921527100302848075)
                ·
                  refine ⟨451031036882290650454272113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300687357921527100302848075 451031036882290650454272113)
                  ·
                    refine ⟨338273277661717987840704085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 451031036882290650454272113 338273277661717987840704085)
                    ·
                      refine ⟨3964139972598257670008251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 338273277661717987840704085 3964139972598257670008251)
                      ·
                        rfl

theorem cell23_7720135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_7720135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720135 prefixEnd_7720135 := by exact prefixLift 7720135
  have htrace : WordTrace (prefixWord ++ tailWord_7720135) baseStart_7720135 baseEnd_7720135 := by
    simpa [prefixWord, tailWord_7720135, baseEnd_7720135] using wordTrace_append hprefix tailTrace_7720135
  have hstable : (prefixWord ++ tailWord_7720135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720135).length < 2 ^ (prefixWord ++ tailWord_7720135).sum := by decide
  have hdescent : baseEnd_7720135 < baseStart_7720135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720146 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_7720146 : Nat := 118140960795 + 7720146 * 2 ^ 59
def prefixEnd_7720146 : Nat := 4983230072969 + 3 ^ 40 * 7720146 * 2
def baseEnd_7720146 : Nat := 3964145620885457126970701

theorem tailTrace_7720146 : CollatzResearch.WordTrace tailWord_7720146 prefixEnd_7720146 3964145620885457126970701 := by
  unfold tailWord_7720146
  simp only [CollatzResearch.WordTrace]
  refine ⟨70394214272309253202771073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187717904726158008540722861 70394214272309253202771073)
  ·
    refine ⟨52795660704231939902078305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70394214272309253202771073 52795660704231939902078305)
    ·
      refine ⟨39596745528173954926558729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52795660704231939902078305 39596745528173954926558729)
      ·
        refine ⟨29697559146130466194919047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39596745528173954926558729 29697559146130466194919047)
        ·
          refine ⟨44546338719195699292378571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29697559146130466194919047 44546338719195699292378571)
          ·
            refine ⟨66819508078793548938567857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44546338719195699292378571 66819508078793548938567857)
            ·
              refine ⟨50114631059095161703925893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66819508078793548938567857 50114631059095161703925893)
              ·
                refine ⟨9396493323580342819486105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50114631059095161703925893 9396493323580342819486105)
                ·
                  refine ⟨7047369992685257114614579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9396493323580342819486105 7047369992685257114614579)
                  ·
                    refine ⟨10571054989027885671921869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7047369992685257114614579 10571054989027885671921869)
                    ·
                      refine ⟨3964145620885457126970701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10571054989027885671921869 3964145620885457126970701)
                      ·
                        rfl

theorem cell23_7720146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_7720146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720146 prefixEnd_7720146 := by exact prefixLift 7720146
  have htrace : WordTrace (prefixWord ++ tailWord_7720146) baseStart_7720146 baseEnd_7720146 := by
    simpa [prefixWord, tailWord_7720146, baseEnd_7720146] using wordTrace_append hprefix tailTrace_7720146
  have hstable : (prefixWord ++ tailWord_7720146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720146).length < 2 ^ (prefixWord ++ tailWord_7720146).sum := by decide
  have hdescent : baseEnd_7720146 < baseStart_7720146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720172 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_7720172 : Nat := 118140960795 + 7720172 * 2 ^ 59
def prefixEnd_7720172 : Nat := 4983230072969 + 3 ^ 40 * 7720172 * 2
def baseEnd_7720172 : Nat := 3964158971382474025245581

theorem tailTrace_7720172 : CollatzResearch.WordTrace tailWord_7720172 prefixEnd_7720172 3964158971382474025245581 := by
  unfold tailWord_7720172
  simp only [CollatzResearch.WordTrace]
  refine ⟨140788902693571409625765385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187718536924761879501020513 140788902693571409625765385)
  ·
    refine ⟨105591677020178557219324039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140788902693571409625765385 105591677020178557219324039)
    ·
      refine ⟨158387515530267835828986059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105591677020178557219324039 158387515530267835828986059)
      ·
        refine ⟨237581273295401753743479089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158387515530267835828986059 237581273295401753743479089)
        ·
          refine ⟨178185954971551315307609317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237581273295401753743479089 178185954971551315307609317)
          ·
            refine ⟨33409866557165871620176747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178185954971551315307609317 33409866557165871620176747)
            ·
              refine ⟨50114799835748807430265121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33409866557165871620176747 50114799835748807430265121)
              ·
                refine ⟨37586099876811605572698841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50114799835748807430265121 37586099876811605572698841)
                ·
                  refine ⟨28189574907608704179524131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37586099876811605572698841 28189574907608704179524131)
                  ·
                    refine ⟨42284362361413056269286197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28189574907608704179524131 42284362361413056269286197)
                    ·
                      refine ⟨3964158971382474025245581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42284362361413056269286197 3964158971382474025245581)
                      ·
                        rfl

theorem cell23_7720172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_7720172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720172 prefixEnd_7720172 := by exact prefixLift 7720172
  have htrace : WordTrace (prefixWord ++ tailWord_7720172) baseStart_7720172 baseEnd_7720172 := by
    simpa [prefixWord, tailWord_7720172, baseEnd_7720172] using wordTrace_append hprefix tailTrace_7720172
  have hstable : (prefixWord ++ tailWord_7720172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720172).length < 2 ^ (prefixWord ++ tailWord_7720172).sum := by decide
  have hdescent : baseEnd_7720172 < baseStart_7720172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720173 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_7720173 : Nat := 118140960795 + 7720173 * 2 ^ 59
def prefixEnd_7720173 : Nat := 4983230072969 + 3 ^ 40 * 7720173 * 2
def baseEnd_7720173 : Nat := 3964159484863128521333077

theorem tailTrace_7720173 : CollatzResearch.WordTrace tailWord_7720173 prefixEnd_7720173 3964159484863128521333077 := by
  unfold tailWord_7720173
  simp only [CollatzResearch.WordTrace]
  refine ⟨281577841860139196422317173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187718561240092797614878115 281577841860139196422317173)
  ·
    refine ⟨26397922674388049664592235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281577841860139196422317173 26397922674388049664592235)
    ·
      refine ⟨39596884011582074496888353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26397922674388049664592235 39596884011582074496888353)
      ·
        refine ⟨29697663008686555872666265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39596884011582074496888353 29697663008686555872666265)
        ·
          refine ⟨22273247256514916904499699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29697663008686555872666265 22273247256514916904499699)
          ·
            refine ⟨33409870884772375356749549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22273247256514916904499699 33409870884772375356749549)
            ·
              refine ⟨12528701581789640758781081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33409870884772375356749549 12528701581789640758781081)
              ·
                refine ⟨9396526186342230569085811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12528701581789640758781081 9396526186342230569085811)
                ·
                  refine ⟨14094789279513345853628717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9396526186342230569085811 14094789279513345853628717)
                  ·
                    refine ⟨5285545979817504695110769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14094789279513345853628717 5285545979817504695110769)
                    ·
                      refine ⟨3964159484863128521333077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285545979817504695110769 3964159484863128521333077)
                      ·
                        rfl

theorem cell23_7720173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_7720173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720173 prefixEnd_7720173 := by exact prefixLift 7720173
  have htrace : WordTrace (prefixWord ++ tailWord_7720173) baseStart_7720173 baseEnd_7720173 := by
    simpa [prefixWord, tailWord_7720173, baseEnd_7720173] using wordTrace_append hprefix tailTrace_7720173
  have hstable : (prefixWord ++ tailWord_7720173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720173).length < 2 ^ (prefixWord ++ tailWord_7720173).sum := by decide
  have hdescent : baseEnd_7720173 < baseStart_7720173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720180 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7720180 : Nat := 118140960795 + 7720180 * 2 ^ 59
def prefixEnd_7720180 : Nat := 4983230072969 + 3 ^ 40 * 7720180 * 2
def baseEnd_7720180 : Nat := 3964163079227709993945545

theorem tailTrace_7720180 : CollatzResearch.WordTrace tailWord_7720180 prefixEnd_7720180 3964163079227709993945545 := by
  unfold tailWord_7720180
  simp only [CollatzResearch.WordTrace]
  refine ⟨140789048585556918308910997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187718731447409224411881329 140789048585556918308910997)
  ·
    refine ⟨6599486652447980545730203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140789048585556918308910997 6599486652447980545730203)
    ·
      refine ⟨9899229978671970818595305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6599486652447980545730203 9899229978671970818595305)
      ·
        refine ⟨7424422484003978113946479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9899229978671970818595305 7424422484003978113946479)
        ·
          refine ⟨11136633726005967170919719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7424422484003978113946479 11136633726005967170919719)
          ·
            refine ⟨16704950589008950756379579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11136633726005967170919719 16704950589008950756379579)
            ·
              refine ⟨25057425883513426134569369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16704950589008950756379579 25057425883513426134569369)
              ·
                refine ⟨18793069412635069600927027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25057425883513426134569369 18793069412635069600927027)
                ·
                  refine ⟨28189604118952604401390541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18793069412635069600927027 28189604118952604401390541)
                  ·
                    refine ⟨10571101544607226650521453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28189604118952604401390541 10571101544607226650521453)
                    ·
                      refine ⟨3964163079227709993945545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10571101544607226650521453 3964163079227709993945545)
                      ·
                        rfl

theorem cell23_7720180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7720180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720180 prefixEnd_7720180 := by exact prefixLift 7720180
  have htrace : WordTrace (prefixWord ++ tailWord_7720180) baseStart_7720180 baseEnd_7720180 := by
    simpa [prefixWord, tailWord_7720180, baseEnd_7720180] using wordTrace_append hprefix tailTrace_7720180
  have hstable : (prefixWord ++ tailWord_7720180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720180).length < 2 ^ (prefixWord ++ tailWord_7720180).sum := by decide
  have hdescent : baseEnd_7720180 < baseStart_7720180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720190 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_7720190 : Nat := 118140960795 + 7720190 * 2 ^ 59
def prefixEnd_7720190 : Nat := 4983230072969 + 3 ^ 40 * 7720190 * 2
def baseEnd_7720190 : Nat := 3964168214034254954820499

theorem tailTrace_7720190 : CollatzResearch.WordTrace tailWord_7720190 prefixEnd_7720190 3964168214034254954820499 := by
  unfold tailWord_7720190
  simp only [CollatzResearch.WordTrace]
  refine ⟨35197307737634701040710753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187718974600718405550457349 35197307737634701040710753)
  ·
    refine ⟨26397980803226025780533065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35197307737634701040710753 26397980803226025780533065)
    ·
      refine ⟨19798485602419519335399799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26397980803226025780533065 19798485602419519335399799)
      ·
        refine ⟨29697728403629279003099699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19798485602419519335399799 29697728403629279003099699)
        ·
          refine ⟨44546592605443918504649549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29697728403629279003099699 44546592605443918504649549)
          ·
            refine ⟨16704972227041469439243581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44546592605443918504649549 16704972227041469439243581)
            ·
              refine ⟨6264364585140551039716343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16704972227041469439243581 6264364585140551039716343)
              ·
                refine ⟨9396546877710826559574515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6264364585140551039716343 9396546877710826559574515)
                ·
                  refine ⟨14094820316566239839361773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9396546877710826559574515 14094820316566239839361773)
                  ·
                    refine ⟨5285557618712339939760665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14094820316566239839361773 5285557618712339939760665)
                    ·
                      refine ⟨3964168214034254954820499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285557618712339939760665 3964168214034254954820499)
                      ·
                        rfl

theorem cell23_7720190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_7720190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720190 prefixEnd_7720190 := by exact prefixLift 7720190
  have htrace : WordTrace (prefixWord ++ tailWord_7720190) baseStart_7720190 baseEnd_7720190 := by
    simpa [prefixWord, tailWord_7720190, baseEnd_7720190] using wordTrace_append hprefix tailTrace_7720190
  have hstable : (prefixWord ++ tailWord_7720190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720190).length < 2 ^ (prefixWord ++ tailWord_7720190).sum := by decide
  have hdescent : baseEnd_7720190 < baseStart_7720190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720203 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 2, 2, 2]
def baseStart_7720203 : Nat := 118140960795 + 7720203 * 2 ^ 59
def prefixEnd_7720203 : Nat := 4983230072969 + 3 ^ 40 * 7720203 * 2
def baseEnd_7720203 : Nat := 3964174889282763403957939

theorem tailTrace_7720203 : CollatzResearch.WordTrace tailWord_7720203 prefixEnd_7720203 3964174889282763403957939 := by
  unfold tailWord_7720203
  simp only [CollatzResearch.WordTrace]
  refine ⟨281578936050030511545909263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187719290700020341030606175 281578936050030511545909263)
  ·
    refine ⟨422368404075045767318863895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281578936050030511545909263 422368404075045767318863895)
    ·
      refine ⟨633552606112568650978295843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422368404075045767318863895 633552606112568650978295843)
      ·
        refine ⟨950328909168852976467443765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633552606112568650978295843 950328909168852976467443765)
        ·
          refine ⟨89093335234579966543822853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 950328909168852976467443765 89093335234579966543822853)
          ·
            refine ⟨16705000356483743726966785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89093335234579966543822853 16705000356483743726966785)
            ·
              refine ⟨12528750267362807795225089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16705000356483743726966785 12528750267362807795225089)
              ·
                refine ⟨9396562700522105846418817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12528750267362807795225089 9396562700522105846418817)
                ·
                  refine ⟨7047422025391579384814113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9396562700522105846418817 7047422025391579384814113)
                  ·
                    refine ⟨5285566519043684538610585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7047422025391579384814113 5285566519043684538610585)
                    ·
                      refine ⟨3964174889282763403957939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285566519043684538610585 3964174889282763403957939)
                      ·
                        rfl

theorem cell23_7720203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 2, 2].length) (baseStart_7720203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720203 prefixEnd_7720203 := by exact prefixLift 7720203
  have htrace : WordTrace (prefixWord ++ tailWord_7720203) baseStart_7720203 baseEnd_7720203 := by
    simpa [prefixWord, tailWord_7720203, baseEnd_7720203] using wordTrace_append hprefix tailTrace_7720203
  have hstable : (prefixWord ++ tailWord_7720203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720203).length < 2 ^ (prefixWord ++ tailWord_7720203).sum := by decide
  have hdescent : baseEnd_7720203 < baseStart_7720203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720209 : List Nat := [1, 2, 2, 1, 1, 4, 3, 4, 5]
def baseStart_7720209 : Nat := 118140960795 + 7720209 * 2 ^ 59
def prefixEnd_7720209 : Nat := 4983230072969 + 3 ^ 40 * 7720209 * 2
def baseEnd_7720209 : Nat := 440464218907410042275879

theorem tailTrace_7720209 : CollatzResearch.WordTrace tailWord_7720209 prefixEnd_7720209 440464218907410042275879 := by
  unfold tailWord_7720209
  simp only [CollatzResearch.WordTrace]
  refine ⟨281579154888008774570627681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187719436592005849713751787 281579154888008774570627681)
  ·
    refine ⟨211184366166006580927970761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281579154888008774570627681 211184366166006580927970761)
    ·
      refine ⟨158388274624504935695978071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211184366166006580927970761 158388274624504935695978071)
      ·
        refine ⟨237582411936757403543967107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158388274624504935695978071 237582411936757403543967107)
        ·
          refine ⟨356373617905136105315950661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237582411936757403543967107 356373617905136105315950661)
          ·
            refine ⟨66820053357213019746740749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356373617905136105315950661 66820053357213019746740749)
            ·
              refine ⟨25057520008954882405027781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66820053357213019746740749 25057520008954882405027781)
              ·
                refine ⟨4698285001679040450942709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25057520008954882405027781 4698285001679040450942709)
                ·
                  refine ⟨440464218907410042275879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4698285001679040450942709 440464218907410042275879)
                  ·
                    rfl

theorem cell23_7720209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 5].length) (baseStart_7720209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720209 prefixEnd_7720209 := by exact prefixLift 7720209
  have htrace : WordTrace (prefixWord ++ tailWord_7720209) baseStart_7720209 baseEnd_7720209 := by
    simpa [prefixWord, tailWord_7720209, baseEnd_7720209] using wordTrace_append hprefix tailTrace_7720209
  have hstable : (prefixWord ++ tailWord_7720209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720209).length < 2 ^ (prefixWord ++ tailWord_7720209).sum := by decide
  have hdescent : baseEnd_7720209 < baseStart_7720209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720272 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_7720272 : Nat := 118140960795 + 7720272 * 2 ^ 59
def prefixEnd_7720272 : Nat := 4983230072969 + 3 ^ 40 * 7720272 * 2
def baseEnd_7720272 : Nat := 3964210319447923633995121

theorem tailTrace_7720272 : CollatzResearch.WordTrace tailWord_7720272 prefixEnd_7720272 3964210319447923633995121 := by
  unfold tailWord_7720272
  simp only [CollatzResearch.WordTrace]
  refine ⟨140790726343390268165085535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187720968457853690886780713 140790726343390268165085535)
  ·
    refine ⟨211186089515085402247628303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140790726343390268165085535 211186089515085402247628303)
    ·
      refine ⟨316779134272628103371442455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211186089515085402247628303 316779134272628103371442455)
      ·
        refine ⟨475168701408942155057163683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316779134272628103371442455 475168701408942155057163683)
        ·
          refine ⟨712753052113413232585745525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475168701408942155057163683 712753052113413232585745525)
          ·
            refine ⟨66820598635632490554913643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 712753052113413232585745525 66820598635632490554913643)
            ·
              refine ⟨100230897953448735832370465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66820598635632490554913643 100230897953448735832370465)
              ·
                refine ⟨75173173465086551874277849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100230897953448735832370465 75173173465086551874277849)
                ·
                  refine ⟨56379880098814913905708387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75173173465086551874277849 56379880098814913905708387)
                  ·
                    refine ⟨84569820148222370858562581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56379880098814913905708387 84569820148222370858562581)
                    ·
                      refine ⟨3964210319447923633995121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84569820148222370858562581 3964210319447923633995121)
                      ·
                        rfl

theorem cell23_7720272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_7720272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720272 prefixEnd_7720272 := by exact prefixLift 7720272
  have htrace : WordTrace (prefixWord ++ tailWord_7720272) baseStart_7720272 baseEnd_7720272 := by
    simpa [prefixWord, tailWord_7720272, baseEnd_7720272] using wordTrace_append hprefix tailTrace_7720272
  have hstable : (prefixWord ++ tailWord_7720272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720272).length < 2 ^ (prefixWord ++ tailWord_7720272).sum := by decide
  have hdescent : baseEnd_7720272 < baseStart_7720272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720276 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_7720276 : Nat := 118140960795 + 7720276 * 2 ^ 59
def prefixEnd_7720276 : Nat := 4983230072969 + 3 ^ 40 * 7720276 * 2
def baseEnd_7720276 : Nat := 3964212373370541618345103

theorem tailTrace_7720276 : CollatzResearch.WordTrace tailWord_7720276 prefixEnd_7720276 3964212373370541618345103 := by
  unfold tailWord_7720276
  simp only [CollatzResearch.WordTrace]
  refine ⟨140790799289383022506658341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187721065719177363342211121 140790799289383022506658341)
  ·
    refine ⟨26398274866759316719998439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140790799289383022506658341 26398274866759316719998439)
    ·
      refine ⟨39597412300138975079997659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26398274866759316719998439 39597412300138975079997659)
      ·
        refine ⟨59396118450208462619996489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39597412300138975079997659 59396118450208462619996489)
        ·
          refine ⟨44547088837656346964997367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59396118450208462619996489 44547088837656346964997367)
          ·
            refine ⟨66820633256484520447496051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44547088837656346964997367 66820633256484520447496051)
            ·
              refine ⟨100230949884726780671244077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66820633256484520447496051 100230949884726780671244077)
              ·
                refine ⟨37586606206772542751716529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100230949884726780671244077 37586606206772542751716529)
                ·
                  refine ⟨28189954655079407063787397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37586606206772542751716529 28189954655079407063787397)
                  ·
                    refine ⟨5285616497827388824460137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28189954655079407063787397 5285616497827388824460137)
                    ·
                      refine ⟨3964212373370541618345103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285616497827388824460137 3964212373370541618345103)
                      ·
                        rfl

theorem cell23_7720276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_7720276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720276 prefixEnd_7720276 := by exact prefixLift 7720276
  have htrace : WordTrace (prefixWord ++ tailWord_7720276) baseStart_7720276 baseEnd_7720276 := by
    simpa [prefixWord, tailWord_7720276, baseEnd_7720276] using wordTrace_append hprefix tailTrace_7720276
  have hstable : (prefixWord ++ tailWord_7720276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720276).length < 2 ^ (prefixWord ++ tailWord_7720276).sum := by decide
  have hdescent : baseEnd_7720276 < baseStart_7720276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720279 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 3]
def baseStart_7720279 : Nat := 118140960795 + 7720279 * 2 ^ 59
def prefixEnd_7720279 : Nat := 4983230072969 + 3 ^ 40 * 7720279 * 2
def baseEnd_7720279 : Nat := 3964213913812505106607589

theorem tailTrace_7720279 : CollatzResearch.WordTrace tailWord_7720279 prefixEnd_7720279 3964213913812505106607589 := by
  unfold tailWord_7720279
  simp only [CollatzResearch.WordTrace]
  refine ⟨281581707997755176525675891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187721138665170117683783927 281581707997755176525675891)
  ·
    refine ⟨422372561996632764788513837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281581707997755176525675891 422372561996632764788513837)
    ·
      refine ⟨158389710748737286795692689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422372561996632764788513837 158389710748737286795692689)
      ·
        refine ⟨118792283061552965096769517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158389710748737286795692689 118792283061552965096769517)
        ·
          refine ⟨44547106148082361911288569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118792283061552965096769517 44547106148082361911288569)
          ·
            refine ⟨33410329611061771433466427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44547106148082361911288569 33410329611061771433466427)
            ·
              refine ⟨50115494416592657150199641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33410329611061771433466427 50115494416592657150199641)
              ·
                refine ⟨37586620812444492862649731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50115494416592657150199641 37586620812444492862649731)
                ·
                  refine ⟨56379931218666739293974597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37586620812444492862649731 56379931218666739293974597)
                  ·
                    refine ⟨10571237103500013617620237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56379931218666739293974597 10571237103500013617620237)
                    ·
                      refine ⟨3964213913812505106607589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10571237103500013617620237 3964213913812505106607589)
                      ·
                        rfl

theorem cell23_7720279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_7720279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720279 prefixEnd_7720279 := by exact prefixLift 7720279
  have htrace : WordTrace (prefixWord ++ tailWord_7720279) baseStart_7720279 baseEnd_7720279 := by
    simpa [prefixWord, tailWord_7720279, baseEnd_7720279] using wordTrace_append hprefix tailTrace_7720279
  have hstable : (prefixWord ++ tailWord_7720279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720279).length < 2 ^ (prefixWord ++ tailWord_7720279).sum := by decide
  have hdescent : baseEnd_7720279 < baseStart_7720279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720376 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 2, 4]
def baseStart_7720376 : Nat := 118140960795 + 7720376 * 2 ^ 59
def prefixEnd_7720376 : Nat := 4983230072969 + 3 ^ 40 * 7720376 * 2
def baseEnd_7720376 : Nat := 1321421240478663742364881

theorem tailTrace_7720376 : CollatzResearch.WordTrace tailWord_7720376 prefixEnd_7720376 1321421240478663742364881 := by
  unfold tailWord_7720376
  simp only [CollatzResearch.WordTrace]
  refine ⟨140792622939201881045978491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187723497252269174727971321 140792622939201881045978491)
  ·
    refine ⟨211188934408802821568967737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140792622939201881045978491 211188934408802821568967737)
    ·
      refine ⟨158391700806602116176725803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211188934408802821568967737 158391700806602116176725803)
      ·
        refine ⟨237587551209903174265088705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158391700806602116176725803 237587551209903174265088705)
        ·
          refine ⟨178190663407427380698816529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237587551209903174265088705 178190663407427380698816529)
          ·
            refine ⟨133642997555570535524112397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178190663407427380698816529 133642997555570535524112397)
            ·
              refine ⟨50116124083338950821542149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133642997555570535524112397 50116124083338950821542149)
              ·
                refine ⟨9396773265626053279039153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50116124083338950821542149 9396773265626053279039153)
                ·
                  refine ⟨7047579949219539959279365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9396773265626053279039153 7047579949219539959279365)
                  ·
                    refine ⟨1321421240478663742364881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7047579949219539959279365 1321421240478663742364881)
                    ·
                      rfl

theorem cell23_7720376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_7720376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720376 prefixEnd_7720376 := by exact prefixLift 7720376
  have htrace : WordTrace (prefixWord ++ tailWord_7720376) baseStart_7720376 baseEnd_7720376 := by
    simpa [prefixWord, tailWord_7720376, baseEnd_7720376] using wordTrace_append hprefix tailTrace_7720376
  have hstable : (prefixWord ++ tailWord_7720376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720376).length < 2 ^ (prefixWord ++ tailWord_7720376).sum := by decide
  have hdescent : baseEnd_7720376 < baseStart_7720376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720396 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_7720396 : Nat := 118140960795 + 7720396 * 2 ^ 59
def prefixEnd_7720396 : Nat := 4983230072969 + 3 ^ 40 * 7720396 * 2
def baseEnd_7720396 : Nat := 3964273991049081148844551

theorem tailTrace_7720396 : CollatzResearch.WordTrace tailWord_7720396 prefixEnd_7720396 3964273991049081148844551 := by
  unfold tailWord_7720396
  simp only [CollatzResearch.WordTrace]
  refine ⟨140792987669165652753842521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187723983558887537005123361 140792987669165652753842521)
  ·
    refine ⟨105594740751874239565381891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140792987669165652753842521 105594740751874239565381891)
    ·
      refine ⟨158392111127811359348072837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105594740751874239565381891 158392111127811359348072837)
      ·
        refine ⟨29698520836464629877763657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158392111127811359348072837 29698520836464629877763657)
        ·
          refine ⟨22273890627348472408322743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29698520836464629877763657 22273890627348472408322743)
          ·
            refine ⟨33410835941022708612484115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22273890627348472408322743 33410835941022708612484115)
            ·
              refine ⟨50116253911534062918726173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33410835941022708612484115 50116253911534062918726173)
              ·
                refine ⟨18793595216825273594522315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50116253911534062918726173 18793595216825273594522315)
                ·
                  refine ⟨28190392825237910391783473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18793595216825273594522315 28190392825237910391783473)
                  ·
                    refine ⟨21142794618928432793837605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28190392825237910391783473 21142794618928432793837605)
                    ·
                      refine ⟨3964273991049081148844551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21142794618928432793837605 3964273991049081148844551)
                      ·
                        rfl

theorem cell23_7720396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_7720396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720396 prefixEnd_7720396 := by exact prefixLift 7720396
  have htrace : WordTrace (prefixWord ++ tailWord_7720396) baseStart_7720396 baseEnd_7720396 := by
    simpa [prefixWord, tailWord_7720396, baseEnd_7720396] using wordTrace_append hprefix tailTrace_7720396
  have hstable : (prefixWord ++ tailWord_7720396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720396).length < 2 ^ (prefixWord ++ tailWord_7720396).sum := by decide
  have hdescent : baseEnd_7720396 < baseStart_7720396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720417 : List Nat := [1, 2, 3, 1, 2, 4, 2, 3, 1, 2, 2]
def baseStart_7720417 : Nat := 118140960795 + 7720417 * 2 ^ 59
def prefixEnd_7720417 : Nat := 4983230072969 + 3 ^ 40 * 7720417 * 2
def baseEnd_7720417 : Nat := 3964284774142825566681955

theorem tailTrace_7720417 : CollatzResearch.WordTrace tailWord_7720417 prefixEnd_7720417 3964284774142825566681955 := by
  unfold tailWord_7720417
  simp only [CollatzResearch.WordTrace]
  refine ⟨281586741271255226094199505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187724494180836817396133003 281586741271255226094199505)
  ·
    refine ⟨211190055953441419570649629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281586741271255226094199505 211190055953441419570649629)
    ·
      refine ⟨79196270982540532338993611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211190055953441419570649629 79196270982540532338993611)
      ·
        refine ⟨118794406473810798508490417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79196270982540532338993611 118794406473810798508490417)
        ·
          refine ⟨89095804855358098881367813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118794406473810798508490417 89095804855358098881367813)
          ·
            refine ⟨16705463410379643540256465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89095804855358098881367813 16705463410379643540256465)
            ·
              refine ⟨12529097557784732655192349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16705463410379643540256465 12529097557784732655192349)
              ·
                refine ⟨4698411584169274745697131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12529097557784732655192349 4698411584169274745697131)
                ·
                  refine ⟨7047617376253912118545697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4698411584169274745697131 7047617376253912118545697)
                  ·
                    refine ⟨5285713032190434088909273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7047617376253912118545697 5285713032190434088909273)
                    ·
                      refine ⟨3964284774142825566681955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285713032190434088909273 3964284774142825566681955)
                      ·
                        rfl

theorem cell23_7720417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_7720417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720417 prefixEnd_7720417 := by exact prefixLift 7720417
  have htrace : WordTrace (prefixWord ++ tailWord_7720417) baseStart_7720417 baseEnd_7720417 := by
    simpa [prefixWord, tailWord_7720417, baseEnd_7720417] using wordTrace_append hprefix tailTrace_7720417
  have hstable : (prefixWord ++ tailWord_7720417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720417).length < 2 ^ (prefixWord ++ tailWord_7720417).sum := by decide
  have hdescent : baseEnd_7720417 < baseStart_7720417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720433 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 4, 1, 3]
def baseStart_7720433 : Nat := 118140960795 + 7720433 * 2 ^ 59
def prefixEnd_7720433 : Nat := 4983230072969 + 3 ^ 40 * 7720433 * 2
def baseEnd_7720433 : Nat := 3964292989833297504081881

theorem tailTrace_7720433 : CollatzResearch.WordTrace tailWord_7720433 prefixEnd_7720433 3964292989833297504081881 := by
  unfold tailWord_7720433
  simp only [CollatzResearch.WordTrace]
  refine ⟨281587324839197260826781953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187724883226131507217854635 281587324839197260826781953)
  ·
    refine ⟨211190493629397945620086465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281587324839197260826781953 211190493629397945620086465)
    ·
      refine ⟨158392870222048459215064849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211190493629397945620086465 158392870222048459215064849)
      ·
        refine ⟨118794652666536344411298637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158392870222048459215064849 118794652666536344411298637)
        ·
          refine ⟨44547994749951129154236989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118794652666536344411298637 44547994749951129154236989)
          ·
            refine ⟨16705498031231673432838871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44547994749951129154236989 16705498031231673432838871)
            ·
              refine ⟨25058247046847510149258307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16705498031231673432838871 25058247046847510149258307)
              ·
                refine ⟨37587370570271265223887461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25058247046847510149258307 37587370570271265223887461)
                ·
                  refine ⟨7047631981925862229478899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37587370570271265223887461 7047631981925862229478899)
                  ·
                    refine ⟨10571447972888793344218349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7047631981925862229478899 10571447972888793344218349)
                    ·
                      refine ⟨3964292989833297504081881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10571447972888793344218349 3964292989833297504081881)
                      ·
                        rfl

theorem cell23_7720433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_7720433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720433 prefixEnd_7720433 := by exact prefixLift 7720433
  have htrace : WordTrace (prefixWord ++ tailWord_7720433) baseStart_7720433 baseEnd_7720433 := by
    simpa [prefixWord, tailWord_7720433, baseEnd_7720433] using wordTrace_append hprefix tailTrace_7720433
  have hstable : (prefixWord ++ tailWord_7720433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720433).length < 2 ^ (prefixWord ++ tailWord_7720433).sum := by decide
  have hdescent : baseEnd_7720433 < baseStart_7720433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720439 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_7720439 : Nat := 118140960795 + 7720439 * 2 ^ 59
def prefixEnd_7720439 : Nat := 4983230072969 + 3 ^ 40 * 7720439 * 2
def baseEnd_7720439 : Nat := 3964296070717224480606853

theorem tailTrace_7720439 : CollatzResearch.WordTrace tailWord_7720439 prefixEnd_7720439 3964296070717224480606853 := by
  unfold tailWord_7720439
  simp only [CollatzResearch.WordTrace]
  refine ⟨281587543677175523851500371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187725029118117015901000247 281587543677175523851500371)
  ·
    refine ⟨422381315515763285777250557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281587543677175523851500371 422381315515763285777250557)
    ·
      refine ⟨158392993318411232166468959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422381315515763285777250557 158392993318411232166468959)
      ·
        refine ⟨237589489977616848249703439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158392993318411232166468959 237589489977616848249703439)
        ·
          refine ⟨356384234966425272374555159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237589489977616848249703439 356384234966425272374555159)
          ·
            refine ⟨534576352449637908561832739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356384234966425272374555159 534576352449637908561832739)
            ·
              refine ⟨801864528674456862842749109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534576352449637908561832739 801864528674456862842749109)
              ·
                refine ⟨75174799563230330891507729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 801864528674456862842749109 75174799563230330891507729)
                ·
                  refine ⟨56381099672422748168630797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75174799563230330891507729 56381099672422748168630797)
                  ·
                    refine ⟨21142912377158530563236549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56381099672422748168630797 21142912377158530563236549)
                    ·
                      refine ⟨3964296070717224480606853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21142912377158530563236549 3964296070717224480606853)
                      ·
                        rfl

theorem cell23_7720439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_7720439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720439 prefixEnd_7720439 := by exact prefixLift 7720439
  have htrace : WordTrace (prefixWord ++ tailWord_7720439) baseStart_7720439 baseEnd_7720439 := by
    simpa [prefixWord, tailWord_7720439, baseEnd_7720439] using wordTrace_append hprefix tailTrace_7720439
  have hstable : (prefixWord ++ tailWord_7720439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720439).length < 2 ^ (prefixWord ++ tailWord_7720439).sum := by decide
  have hdescent : baseEnd_7720439 < baseStart_7720439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720450 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_7720450 : Nat := 118140960795 + 7720450 * 2 ^ 59
def prefixEnd_7720450 : Nat := 4983230072969 + 3 ^ 40 * 7720450 * 2
def baseEnd_7720450 : Nat := 3964301719004423937569303

theorem tailTrace_7720450 : CollatzResearch.WordTrace tailWord_7720450 prefixEnd_7720450 3964301719004423937569303 := by
  unfold tailWord_7720450
  simp only [CollatzResearch.WordTrace]
  refine ⟨70396986220033918182537701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187725296586757115153433869 70396986220033918182537701)
  ·
    refine ⟨13199434916256359659225819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70396986220033918182537701 13199434916256359659225819)
    ·
      refine ⟨19799152374384539488838729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13199434916256359659225819 19799152374384539488838729)
      ·
        refine ⟨14849364280788404616629047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19799152374384539488838729 14849364280788404616629047)
        ·
          refine ⟨22274046421182606924943571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14849364280788404616629047 22274046421182606924943571)
          ·
            refine ⟨33411069631773910387415357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22274046421182606924943571 33411069631773910387415357)
            ·
              refine ⟨12529151111915216395280759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33411069631773910387415357 12529151111915216395280759)
              ·
                refine ⟨18793726667872824592921139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12529151111915216395280759 18793726667872824592921139)
                ·
                  refine ⟨28190590001809236889381709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18793726667872824592921139 28190590001809236889381709)
                  ·
                    refine ⟨10571471250678463833518141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28190590001809236889381709 10571471250678463833518141)
                    ·
                      refine ⟨3964301719004423937569303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10571471250678463833518141 3964301719004423937569303)
                      ·
                        rfl

theorem cell23_7720450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_7720450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720450 prefixEnd_7720450 := by exact prefixLift 7720450
  have htrace : WordTrace (prefixWord ++ tailWord_7720450) baseStart_7720450 baseEnd_7720450 := by
    simpa [prefixWord, tailWord_7720450, baseEnd_7720450] using wordTrace_append hprefix tailTrace_7720450
  have hstable : (prefixWord ++ tailWord_7720450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720450).length < 2 ^ (prefixWord ++ tailWord_7720450).sum := by decide
  have hdescent : baseEnd_7720450 < baseStart_7720450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720468 : List Nat := [2, 4, 3, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_7720468 : Nat := 118140960795 + 7720468 * 2 ^ 59
def prefixEnd_7720468 : Nat := 4983230072969 + 3 ^ 40 * 7720468 * 2
def baseEnd_7720468 : Nat := 3964310961656204867144221

theorem tailTrace_7720468 : CollatzResearch.WordTrace tailWord_7720468 prefixEnd_7720468 3964310961656204867144221 := by
  unfold tailWord_7720468
  simp only [CollatzResearch.WordTrace]
  refine ⟨140794300697035230902153029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187725734262713641202870705 140794300697035230902153029)
  ·
    refine ⟨26398931380694105794153693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140794300697035230902153029 26398931380694105794153693)
    ·
      refine ⟨9899599267760289672807635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26398931380694105794153693 9899599267760289672807635)
      ·
        refine ⟨14849398901640434509211453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9899599267760289672807635 14849398901640434509211453)
        ·
          refine ⟨5568524588115162940954295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14849398901640434509211453 5568524588115162940954295)
          ·
            refine ⟨8352786882172744411431443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568524588115162940954295 8352786882172744411431443)
            ·
              refine ⟨12529180323259116617147165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8352786882172744411431443 12529180323259116617147165)
              ·
                refine ⟨4698442621222168731430187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12529180323259116617147165 4698442621222168731430187)
                ·
                  refine ⟨7047663931833253097145281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4698442621222168731430187 7047663931833253097145281)
                  ·
                    refine ⟨5285747948874939822858961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7047663931833253097145281 5285747948874939822858961)
                    ·
                      refine ⟨3964310961656204867144221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285747948874939822858961 3964310961656204867144221)
                      ·
                        rfl

theorem cell23_7720468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_7720468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720468 prefixEnd_7720468 := by exact prefixLift 7720468
  have htrace : WordTrace (prefixWord ++ tailWord_7720468) baseStart_7720468 baseEnd_7720468 := by
    simpa [prefixWord, tailWord_7720468, baseEnd_7720468] using wordTrace_append hprefix tailTrace_7720468
  have hstable : (prefixWord ++ tailWord_7720468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720468).length < 2 ^ (prefixWord ++ tailWord_7720468).sum := by decide
  have hdescent : baseEnd_7720468 < baseStart_7720468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720476 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_7720476 : Nat := 118140960795 + 7720476 * 2 ^ 59
def prefixEnd_7720476 : Nat := 4983230072969 + 3 ^ 40 * 7720476 * 2
def baseEnd_7720476 : Nat := 3964315069501440835844183

theorem tailTrace_7720476 : CollatzResearch.WordTrace tailWord_7720476 prefixEnd_7720476 3964315069501440835844183 := by
  unfold tailWord_7720476
  simp only [CollatzResearch.WordTrace]
  refine ⟨140794446589020739585298641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187725928785360986113731521 140794446589020739585298641)
  ·
    refine ⟨105595834941765554688973981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140794446589020739585298641 105595834941765554688973981)
    ·
      refine ⟨39598438103162083008365243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105595834941765554688973981 39598438103162083008365243)
      ·
        refine ⟨59397657154743124512547865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39598438103162083008365243 59397657154743124512547865)
        ·
          refine ⟨44548242866057343384410899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59397657154743124512547865 44548242866057343384410899)
          ·
            refine ⟨66822364299086015076616349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44548242866057343384410899 66822364299086015076616349)
            ·
              refine ⟨25058386612157255653731131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66822364299086015076616349 25058386612157255653731131)
              ·
                refine ⟨37587579918235883480596697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25058386612157255653731131 37587579918235883480596697)
                ·
                  refine ⟨28190684938676912610447523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37587579918235883480596697 28190684938676912610447523)
                  ·
                    refine ⟨42286027408015368915671285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28190684938676912610447523 42286027408015368915671285)
                    ·
                      refine ⟨3964315069501440835844183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42286027408015368915671285 3964315069501440835844183)
                      ·
                        rfl

theorem cell23_7720476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_7720476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720476 prefixEnd_7720476 := by exact prefixLift 7720476
  have htrace : WordTrace (prefixWord ++ tailWord_7720476) baseStart_7720476 baseEnd_7720476 := by
    simpa [prefixWord, tailWord_7720476, baseEnd_7720476] using wordTrace_append hprefix tailTrace_7720476
  have hstable : (prefixWord ++ tailWord_7720476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720476).length < 2 ^ (prefixWord ++ tailWord_7720476).sum := by decide
  have hdescent : baseEnd_7720476 < baseStart_7720476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720479 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 9]
def baseStart_7720479 : Nat := 118140960795 + 7720479 * 2 ^ 59
def prefixEnd_7720479 : Nat := 4983230072969 + 3 ^ 40 * 7720479 * 2
def baseEnd_7720479 : Nat := 440479623327044924900741

theorem tailTrace_7720479 : CollatzResearch.WordTrace tailWord_7720479 prefixEnd_7720479 440479623327044924900741 := by
  unfold tailWord_7720479
  simp only [CollatzResearch.WordTrace]
  refine ⟨281589002597030610682956491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187726001731353740455304327 281589002597030610682956491)
  ·
    refine ⟨422383503895545916024434737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281589002597030610682956491 422383503895545916024434737)
    ·
      refine ⟨316787627921659437018326053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422383503895545916024434737 316787627921659437018326053)
      ·
        refine ⟨59397680235311144440936135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316787627921659437018326053 59397680235311144440936135)
        ·
          refine ⟨89096520352966716661404203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59397680235311144440936135 89096520352966716661404203)
          ·
            refine ⟨133644780529450074992106305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89096520352966716661404203 133644780529450074992106305)
            ·
              refine ⟨100233585397087556244079729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133644780529450074992106305 100233585397087556244079729)
              ·
                refine ⟨75175189047815667183059797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100233585397087556244079729 75175189047815667183059797)
                ·
                  refine ⟨440479623327044924900741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75175189047815667183059797 440479623327044924900741)
                  ·
                    rfl

theorem cell23_7720479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 9].length) (baseStart_7720479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720479 prefixEnd_7720479 := by exact prefixLift 7720479
  have htrace : WordTrace (prefixWord ++ tailWord_7720479) baseStart_7720479 baseEnd_7720479 := by
    simpa [prefixWord, tailWord_7720479, baseEnd_7720479] using wordTrace_append hprefix tailTrace_7720479
  have hstable : (prefixWord ++ tailWord_7720479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720479).length < 2 ^ (prefixWord ++ tailWord_7720479).sum := by decide
  have hdescent : baseEnd_7720479 < baseStart_7720479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720490 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_7720490 : Nat := 118140960795 + 7720490 * 2 ^ 59
def prefixEnd_7720490 : Nat := 4983230072969 + 3 ^ 40 * 7720490 * 2
def baseEnd_7720490 : Nat := 3964322258230603781069119

theorem tailTrace_7720490 : CollatzResearch.WordTrace tailWord_7720490 prefixEnd_7720490 3964322258230603781069119 := by
  unfold tailWord_7720490
  simp only [CollatzResearch.WordTrace]
  refine ⟨70397350949997689890401731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187726269199993839707737949 70397350949997689890401731)
  ·
    refine ⟨105596026424996534835602597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70397350949997689890401731 105596026424996534835602597)
    ·
      refine ⟨19799254954686850281675487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105596026424996534835602597 19799254954686850281675487)
      ·
        refine ⟨29698882432030275422513231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19799254954686850281675487 29698882432030275422513231)
        ·
          refine ⟨44548323648045413133769847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29698882432030275422513231 44548323648045413133769847)
          ·
            refine ⟨66822485472068119700654771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44548323648045413133769847 66822485472068119700654771)
            ·
              refine ⟨100233728208102179550982157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66822485472068119700654771 100233728208102179550982157)
              ·
                refine ⟨37587648078038317331618309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100233728208102179550982157 37587648078038317331618309)
                ·
                  refine ⟨7047684014632184499678433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37587648078038317331618309 7047684014632184499678433)
                  ·
                    refine ⟨5285763010974138374758825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7047684014632184499678433 5285763010974138374758825)
                    ·
                      refine ⟨3964322258230603781069119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285763010974138374758825 3964322258230603781069119)
                      ·
                        rfl

theorem cell23_7720490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_7720490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720490 prefixEnd_7720490 := by exact prefixLift 7720490
  have htrace : WordTrace (prefixWord ++ tailWord_7720490) baseStart_7720490 baseEnd_7720490 := by
    simpa [prefixWord, tailWord_7720490, baseEnd_7720490] using wordTrace_append hprefix tailTrace_7720490
  have hstable : (prefixWord ++ tailWord_7720490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720490).length < 2 ^ (prefixWord ++ tailWord_7720490).sum := by decide
  have hdescent : baseEnd_7720490 < baseStart_7720490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720506 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3]
def baseStart_7720506 : Nat := 118140960795 + 7720506 * 2 ^ 59
def prefixEnd_7720506 : Nat := 4983230072969 + 3 ^ 40 * 7720506 * 2
def baseEnd_7720506 : Nat := 3964330473921075718469045

theorem tailTrace_7720506 : CollatzResearch.WordTrace tailWord_7720506 prefixEnd_7720506 3964330473921075718469045 := by
  unfold tailWord_7720506
  simp only [CollatzResearch.WordTrace]
  refine ⟨70397496841983198573547343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187726658245288529529459581 70397496841983198573547343)
  ·
    refine ⟨105596245262974797860321015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70397496841983198573547343 105596245262974797860321015)
    ·
      refine ⟨158394367894462196790481523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105596245262974797860321015 158394367894462196790481523)
      ·
        refine ⟨237591551841693295185722285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158394367894462196790481523 237591551841693295185722285)
        ·
          refine ⟨89096831940634985694645857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237591551841693295185722285 89096831940634985694645857)
          ·
            refine ⟨66822623955476239270984393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89096831940634985694645857 66822623955476239270984393)
            ·
              refine ⟨50116967966607179453238295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66822623955476239270984393 50116967966607179453238295)
              ·
                refine ⟨75175451949910769179857443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50116967966607179453238295 75175451949910769179857443)
                ·
                  refine ⟨112763177924866153769786165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75175451949910769179857443 112763177924866153769786165)
                  ·
                    refine ⟨10571547930456201915917453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112763177924866153769786165 10571547930456201915917453)
                    ·
                      refine ⟨3964330473921075718469045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10571547930456201915917453 3964330473921075718469045)
                      ·
                        rfl

theorem cell23_7720506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_7720506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720506 prefixEnd_7720506 := by exact prefixLift 7720506
  have htrace : WordTrace (prefixWord ++ tailWord_7720506) baseStart_7720506 baseEnd_7720506 := by
    simpa [prefixWord, tailWord_7720506, baseEnd_7720506] using wordTrace_append hprefix tailTrace_7720506
  have hstable : (prefixWord ++ tailWord_7720506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720506).length < 2 ^ (prefixWord ++ tailWord_7720506).sum := by decide
  have hdescent : baseEnd_7720506 < baseStart_7720506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720541 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7720541 : Nat := 118140960795 + 7720541 * 2 ^ 59
def prefixEnd_7720541 : Nat := 4983230072969 + 3 ^ 40 * 7720541 * 2
def baseEnd_7720541 : Nat := 3964348445743983081531385

theorem tailTrace_7720541 : CollatzResearch.WordTrace tailWord_7720541 prefixEnd_7720541 3964348445743983081531385 := by
  unfold tailWord_7720541
  simp only [CollatzResearch.WordTrace]
  refine ⟨281591263922805995271713477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187727509281870663514475651 281591263922805995271713477)
  ·
    refine ⟨52798361985526124113446277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281591263922805995271713477 52798361985526124113446277)
    ·
      refine ⟨9899692872286148271271177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52798361985526124113446277 9899692872286148271271177)
      ·
        refine ⟨7424769654214611203453383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9899692872286148271271177 7424769654214611203453383)
        ·
          refine ⟨11137154481321916805180075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7424769654214611203453383 11137154481321916805180075)
          ·
            refine ⟨16705731721982875207770113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11137154481321916805180075 16705731721982875207770113)
            ·
              refine ⟨12529298791487156405827585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16705731721982875207770113 12529298791487156405827585)
              ·
                refine ⟨9396974093615367304370689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12529298791487156405827585 9396974093615367304370689)
                ·
                  refine ⟨7047730570211525478278017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9396974093615367304370689 7047730570211525478278017)
                  ·
                    refine ⟨5285797927658644108708513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7047730570211525478278017 5285797927658644108708513)
                    ·
                      refine ⟨3964348445743983081531385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285797927658644108708513 3964348445743983081531385)
                      ·
                        rfl

theorem cell23_7720541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7720541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720541 prefixEnd_7720541 := by exact prefixLift 7720541
  have htrace : WordTrace (prefixWord ++ tailWord_7720541) baseStart_7720541 baseEnd_7720541 := by
    simpa [prefixWord, tailWord_7720541, baseEnd_7720541] using wordTrace_append hprefix tailTrace_7720541
  have hstable : (prefixWord ++ tailWord_7720541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720541).length < 2 ^ (prefixWord ++ tailWord_7720541).sum := by decide
  have hdescent : baseEnd_7720541 < baseStart_7720541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720573 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_7720573 : Nat := 118140960795 + 7720573 * 2 ^ 59
def prefixEnd_7720573 : Nat := 4983230072969 + 3 ^ 40 * 7720573 * 2
def baseEnd_7720573 : Nat := 1321454959041642318777079

theorem tailTrace_7720573 : CollatzResearch.WordTrace tailWord_7720573 prefixEnd_7720573 1321454959041642318777079 := by
  unfold tailWord_7720573
  simp only [CollatzResearch.WordTrace]
  refine ⟨281592431058690064736878373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187728287372460043157918915 281592431058690064736878373)
  ·
    refine ⟨52798580823504387138164695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281592431058690064736878373 52798580823504387138164695)
    ·
      refine ⟨79197871235256580707247043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52798580823504387138164695 79197871235256580707247043)
      ·
        refine ⟨118796806852884871060870565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79197871235256580707247043 118796806852884871060870565)
        ·
          refine ⟨22274401284915913323913231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118796806852884871060870565 22274401284915913323913231)
          ·
            refine ⟨33411601927373869985869847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22274401284915913323913231 33411601927373869985869847)
            ·
              refine ⟨50117402891060804978804771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33411601927373869985869847 50117402891060804978804771)
              ·
                refine ⟨75176104336591207468207157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50117402891060804978804771 75176104336591207468207157)
                ·
                  refine ⟨7047759781555425700144421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75176104336591207468207157 7047759781555425700144421)
                  ·
                    refine ⟨1321454959041642318777079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7047759781555425700144421 1321454959041642318777079)
                    ·
                      rfl

theorem cell23_7720573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_7720573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720573 prefixEnd_7720573 := by exact prefixLift 7720573
  have htrace : WordTrace (prefixWord ++ tailWord_7720573) baseStart_7720573 baseEnd_7720573 := by
    simpa [prefixWord, tailWord_7720573, baseEnd_7720573] using wordTrace_append hprefix tailTrace_7720573
  have hstable : (prefixWord ++ tailWord_7720573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720573).length < 2 ^ (prefixWord ++ tailWord_7720573).sum := by decide
  have hdescent : baseEnd_7720573 < baseStart_7720573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720583 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_7720583 : Nat := 118140960795 + 7720583 * 2 ^ 59
def prefixEnd_7720583 : Nat := 4983230072969 + 3 ^ 40 * 7720583 * 2
def baseEnd_7720583 : Nat := 3964370011931471917206191

theorem tailTrace_7720583 : CollatzResearch.WordTrace tailWord_7720583 prefixEnd_7720583 3964370011931471917206191 := by
  unfold tailWord_7720583
  simp only [CollatzResearch.WordTrace]
  refine ⟨281592795788653836444742403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187728530525769224296494935 281592795788653836444742403)
  ·
    refine ⟨422389193682980754667113605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281592795788653836444742403 422389193682980754667113605)
    ·
      refine ⟨79197973815558891500083801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422389193682980754667113605 79197973815558891500083801)
      ·
        refine ⟨59398480361669168625062851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79197973815558891500083801 59398480361669168625062851)
        ·
          refine ⟨89097720542503752937594277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59398480361669168625062851 89097720542503752937594277)
          ·
            refine ⟨16705822601719453675798927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89097720542503752937594277 16705822601719453675798927)
            ·
              refine ⟨25058733902579180513698391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16705822601719453675798927 25058733902579180513698391)
              ·
                refine ⟨37588100853868770770547587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25058733902579180513698391 37588100853868770770547587)
                ·
                  refine ⟨56382151280803156155821381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37588100853868770770547587 56382151280803156155821381)
                  ·
                    refine ⟨10571653365150591779216509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56382151280803156155821381 10571653365150591779216509)
                    ·
                      refine ⟨3964370011931471917206191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10571653365150591779216509 3964370011931471917206191)
                      ·
                        rfl

theorem cell23_7720583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_7720583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720583 prefixEnd_7720583 := by exact prefixLift 7720583
  have htrace : WordTrace (prefixWord ++ tailWord_7720583) baseStart_7720583 baseEnd_7720583 := by
    simpa [prefixWord, tailWord_7720583, baseEnd_7720583] using wordTrace_append hprefix tailTrace_7720583
  have hstable : (prefixWord ++ tailWord_7720583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720583).length < 2 ^ (prefixWord ++ tailWord_7720583).sum := by decide
  have hdescent : baseEnd_7720583 < baseStart_7720583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720607 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 3, 4]
def baseStart_7720607 : Nat := 118140960795 + 7720607 * 2 ^ 59
def prefixEnd_7720607 : Nat := 4983230072969 + 3 ^ 40 * 7720607 * 2
def baseEnd_7720607 : Nat := 1321460778489059941102027

theorem tailTrace_7720607 : CollatzResearch.WordTrace tailWord_7720607 prefixEnd_7720607 1321460778489059941102027 := by
  unfold tailWord_7720607
  simp only [CollatzResearch.WordTrace]
  refine ⟨281593671140566888543616075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187729114093711259029077383 281593671140566888543616075)
  ·
    refine ⟨422390506710850332815424113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281593671140566888543616075 422390506710850332815424113)
    ·
      refine ⟨316792880033137749611568085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422390506710850332815424113 316792880033137749611568085)
      ·
        refine ⟨7424833125776666006521127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 316792880033137749611568085 7424833125776666006521127)
        ·
          refine ⟨11137249688664999009781691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7424833125776666006521127 11137249688664999009781691)
          ·
            refine ⟨16705874532997498514672537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11137249688664999009781691 16705874532997498514672537)
            ·
              refine ⟨12529405899748123886004403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16705874532997498514672537 12529405899748123886004403)
              ·
                refine ⟨18794108849622185829006605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12529405899748123886004403 18794108849622185829006605)
                ·
                  refine ⟨7047790818608319685877477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18794108849622185829006605 7047790818608319685877477)
                  ·
                    refine ⟨1321460778489059941102027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7047790818608319685877477 1321460778489059941102027)
                    ·
                      rfl

theorem cell23_7720607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 4].length) (baseStart_7720607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720607 prefixEnd_7720607 := by exact prefixLift 7720607
  have htrace : WordTrace (prefixWord ++ tailWord_7720607) baseStart_7720607 baseEnd_7720607 := by
    simpa [prefixWord, tailWord_7720607, baseEnd_7720607] using wordTrace_append hprefix tailTrace_7720607
  have hstable : (prefixWord ++ tailWord_7720607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720607).length < 2 ^ (prefixWord ++ tailWord_7720607).sum := by decide
  have hdescent : baseEnd_7720607 < baseStart_7720607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720623 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 3, 5, 2]
def baseStart_7720623 : Nat := 118140960795 + 7720623 * 2 ^ 59
def prefixEnd_7720623 : Nat := 4983230072969 + 3 ^ 40 * 7720623 * 2
def baseEnd_7720623 : Nat := 3964390551157651760706007

theorem tailTrace_7720623 : CollatzResearch.WordTrace tailWord_7720623 prefixEnd_7720623 3964390551157651760706007 := by
  unfold tailWord_7720623
  simp only [CollatzResearch.WordTrace]
  refine ⟨281594254708508923276198523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187729503139005948850799015 281594254708508923276198523)
  ·
    refine ⟨422391382062763384914297785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281594254708508923276198523 422391382062763384914297785)
    ·
      refine ⟨316793536547072538685723339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422391382062763384914297785 316793536547072538685723339)
      ·
        refine ⟨475190304820608808028585009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316793536547072538685723339 475190304820608808028585009)
        ·
          refine ⟨356392728615456606021438757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475190304820608808028585009 356392728615456606021438757)
          ·
            refine ⟨66823636615398113629019767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356392728615456606021438757 66823636615398113629019767)
            ·
              refine ⟨100235454923097170443529651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66823636615398113629019767 100235454923097170443529651)
              ·
                refine ⟨150353182384645755665294477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100235454923097170443529651 150353182384645755665294477)
                ·
                  refine ⟨56382443394242158374485429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150353182384645755665294477 56382443394242158374485429)
                  ·
                    refine ⟨5285854068210202347608009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56382443394242158374485429 5285854068210202347608009)
                    ·
                      refine ⟨3964390551157651760706007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285854068210202347608009 3964390551157651760706007)
                      ·
                        rfl

theorem cell23_7720623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 5, 2].length) (baseStart_7720623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720623 prefixEnd_7720623 := by exact prefixLift 7720623
  have htrace : WordTrace (prefixWord ++ tailWord_7720623) baseStart_7720623 baseEnd_7720623 := by
    simpa [prefixWord, tailWord_7720623, baseEnd_7720623] using wordTrace_append hprefix tailTrace_7720623
  have hstable : (prefixWord ++ tailWord_7720623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720623).length < 2 ^ (prefixWord ++ tailWord_7720623).sum := by decide
  have hdescent : baseEnd_7720623 < baseStart_7720623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720626 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_7720626 : Nat := 118140960795 + 7720626 * 2 ^ 59
def prefixEnd_7720626 : Nat := 4983230072969 + 3 ^ 40 * 7720626 * 2
def baseEnd_7720626 : Nat := 3964392091599615248968493

theorem tailTrace_7720626 : CollatzResearch.WordTrace tailWord_7720626 prefixEnd_7720626 3964392091599615248968493 := by
  unfold tailWord_7720626
  simp only [CollatzResearch.WordTrace]
  refine ⟨70398591031874513697139433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187729576084998703192371821 70398591031874513697139433)
  ·
    refine ⟨52798943273905885272854575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70398591031874513697139433 52798943273905885272854575)
    ·
      refine ⟨79198414910858827909281863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52798943273905885272854575 79198414910858827909281863)
      ·
        refine ⟨118797622366288241863922795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79198414910858827909281863 118797622366288241863922795)
        ·
          refine ⟨178196433549432362795884193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118797622366288241863922795 178196433549432362795884193)
          ·
            refine ⟨133647325162074272096913145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178196433549432362795884193 133647325162074272096913145)
            ·
              refine ⟨100235493871555704072684859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133647325162074272096913145 100235493871555704072684859)
              ·
                refine ⟨150353240807333556109027289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100235493871555704072684859 150353240807333556109027289)
                ·
                  refine ⟨112764930605500167081770467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150353240807333556109027289 112764930605500167081770467)
                  ·
                    refine ⟨169147395908250250622655701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112764930605500167081770467 169147395908250250622655701)
                    ·
                      refine ⟨3964392091599615248968493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169147395908250250622655701 3964392091599615248968493)
                      ·
                        rfl

theorem cell23_7720626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_7720626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720626 prefixEnd_7720626 := by exact prefixLift 7720626
  have htrace : WordTrace (prefixWord ++ tailWord_7720626) baseStart_7720626 baseEnd_7720626 := by
    simpa [prefixWord, tailWord_7720626, baseEnd_7720626] using wordTrace_append hprefix tailTrace_7720626
  have hstable : (prefixWord ++ tailWord_7720626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720626).length < 2 ^ (prefixWord ++ tailWord_7720626).sum := by decide
  have hdescent : baseEnd_7720626 < baseStart_7720626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720633 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 1, 5]
def baseStart_7720633 : Nat := 118140960795 + 7720633 * 2 ^ 59
def prefixEnd_7720633 : Nat := 4983230072969 + 3 ^ 40 * 7720633 * 2
def baseEnd_7720633 : Nat := 1321465228654732240526987

theorem tailTrace_7720633 : CollatzResearch.WordTrace tailWord_7720633 prefixEnd_7720633 1321465228654732240526987 := by
  unfold tailWord_7720633
  simp only [CollatzResearch.WordTrace]
  refine ⟨281594619438472694984062553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187729746292315129989375035 281594619438472694984062553)
  ·
    refine ⟨211195964578854521238046915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281594619438472694984062553 211195964578854521238046915)
    ·
      refine ⟨316793946868281781857070373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211195964578854521238046915 316793946868281781857070373)
      ·
        refine ⟨59398865037802834098200695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316793946868281781857070373 59398865037802834098200695)
        ·
          refine ⟨89098297556704251147301043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59398865037802834098200695 89098297556704251147301043)
          ·
            refine ⟨133647446335056376720951565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89098297556704251147301043 133647446335056376720951565)
            ·
              refine ⟨50117792375646141270356837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133647446335056376720951565 50117792375646141270356837)
              ·
                refine ⟨9397086070433651488191907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50117792375646141270356837 9397086070433651488191907)
                ·
                  refine ⟨14095629105650477232287861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9397086070433651488191907 14095629105650477232287861)
                  ·
                    refine ⟨1321465228654732240526987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14095629105650477232287861 1321465228654732240526987)
                    ·
                      rfl

theorem cell23_7720633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 5].length) (baseStart_7720633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720633 prefixEnd_7720633 := by exact prefixLift 7720633
  have htrace : WordTrace (prefixWord ++ tailWord_7720633) baseStart_7720633 baseEnd_7720633 := by
    simpa [prefixWord, tailWord_7720633, baseEnd_7720633] using wordTrace_append hprefix tailTrace_7720633
  have hstable : (prefixWord ++ tailWord_7720633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720633).length < 2 ^ (prefixWord ++ tailWord_7720633).sum := by decide
  have hdescent : baseEnd_7720633 < baseStart_7720633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720640 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 2, 3, 2]
def baseStart_7720640 : Nat := 118140960795 + 7720640 * 2 ^ 59
def prefixEnd_7720640 : Nat := 4983230072969 + 3 ^ 40 * 7720640 * 2
def baseEnd_7720640 : Nat := 3964399280328778194193429

theorem tailTrace_7720640 : CollatzResearch.WordTrace tailWord_7720640 prefixEnd_7720640 3964399280328778194193429 := by
  unfold tailWord_7720640
  simp only [CollatzResearch.WordTrace]
  refine ⟨140797437374723667589783687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187729916499631556786378249 140797437374723667589783687)
  ·
    refine ⟨211196156062085501384675531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140797437374723667589783687 211196156062085501384675531)
    ·
      refine ⟨316794234093128252077013297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211196156062085501384675531 316794234093128252077013297)
      ·
        refine ⟨237595675569846189057759973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316794234093128252077013297 237595675569846189057759973)
        ·
          refine ⟨44549189169346160448329995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237595675569846189057759973 44549189169346160448329995)
          ·
            refine ⟨66823783754019240672494993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44549189169346160448329995 66823783754019240672494993)
            ·
              refine ⟨50117837815514430504371245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66823783754019240672494993 50117837815514430504371245)
              ·
                refine ⟨18794189180817911439139217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50117837815514430504371245 18794189180817911439139217)
                ·
                  refine ⟨14095641885613433579354413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18794189180817911439139217 14095641885613433579354413)
                  ·
                    refine ⟨5285865707105037592257905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14095641885613433579354413 5285865707105037592257905)
                    ·
                      refine ⟨3964399280328778194193429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285865707105037592257905 3964399280328778194193429)
                      ·
                        rfl

theorem cell23_7720640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 3, 2].length) (baseStart_7720640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720640 prefixEnd_7720640 := by exact prefixLift 7720640
  have htrace : WordTrace (prefixWord ++ tailWord_7720640) baseStart_7720640 baseEnd_7720640 := by
    simpa [prefixWord, tailWord_7720640, baseEnd_7720640] using wordTrace_append hprefix tailTrace_7720640
  have hstable : (prefixWord ++ tailWord_7720640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720640).length < 2 ^ (prefixWord ++ tailWord_7720640).sum := by decide
  have hdescent : baseEnd_7720640 < baseStart_7720640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720663 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 4, 4]
def baseStart_7720663 : Nat := 118140960795 + 7720663 * 2 ^ 59
def prefixEnd_7720663 : Nat := 4983230072969 + 3 ^ 40 * 7720663 * 2
def baseEnd_7720663 : Nat := 1321470363461277201401941

theorem tailTrace_7720663 : CollatzResearch.WordTrace tailWord_7720663 prefixEnd_7720663 1321470363461277201401941 := by
  unfold tailWord_7720663
  simp only [CollatzResearch.WordTrace]
  refine ⟨281595713628364010107654643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187730475752242673405103095 281595713628364010107654643)
  ·
    refine ⟨422393570442546015161481965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281595713628364010107654643 422393570442546015161481965)
    ·
      refine ⟨158397588915954755685555737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422393570442546015161481965 158397588915954755685555737)
      ·
        refine ⟨118798191686966066764166803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158397588915954755685555737 118798191686966066764166803)
        ·
          refine ⟨178197287530449100146250205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118798191686966066764166803 178197287530449100146250205)
          ·
            refine ⟨66823982823918412554843827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178197287530449100146250205 66823982823918412554843827)
            ·
              refine ⟨100235974235877618832265741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66823982823918412554843827 100235974235877618832265741)
              ·
                refine ⟨37588490338454107062099653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100235974235877618832265741 37588490338454107062099653)
                ·
                  refine ⟨7047841938460145074143685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37588490338454107062099653 7047841938460145074143685)
                  ·
                    refine ⟨1321470363461277201401941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7047841938460145074143685 1321470363461277201401941)
                    ·
                      rfl

theorem cell23_7720663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_7720663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720663 prefixEnd_7720663 := by exact prefixLift 7720663
  have htrace : WordTrace (prefixWord ++ tailWord_7720663) baseStart_7720663 baseEnd_7720663 := by
    simpa [prefixWord, tailWord_7720663, baseEnd_7720663] using wordTrace_append hprefix tailTrace_7720663
  have hstable : (prefixWord ++ tailWord_7720663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720663).length < 2 ^ (prefixWord ++ tailWord_7720663).sum := by decide
  have hdescent : baseEnd_7720663 < baseStart_7720663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720664 : List Nat := [2, 1, 2, 2, 3, 1, 5, 2, 1, 1, 3]
def baseStart_7720664 : Nat := 118140960795 + 7720664 * 2 ^ 59
def prefixEnd_7720664 : Nat := 4983230072969 + 3 ^ 40 * 7720664 * 2
def baseEnd_7720664 : Nat := 3964411603864486100293319

theorem tailTrace_7720664 : CollatzResearch.WordTrace tailWord_7720664 prefixEnd_7720664 3964411603864486100293319 := by
  unfold tailWord_7720664
  simp only [CollatzResearch.WordTrace]
  refine ⟨140797875050680193639220523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187730500067573591518960697 140797875050680193639220523)
  ·
    refine ⟨211196812576020290458830785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140797875050680193639220523 211196812576020290458830785)
    ·
      refine ⟨158397609432015217844123089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211196812576020290458830785 158397609432015217844123089)
      ·
        refine ⟨118798207074011413383092317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158397609432015217844123089 118798207074011413383092317)
        ·
          refine ⟨44549327652754280018659619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118798207074011413383092317 44549327652754280018659619)
          ·
            refine ⟨66823991479131420027989429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44549327652754280018659619 66823991479131420027989429)
            ·
              refine ⟨6264749201168570627624009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66823991479131420027989429 6264749201168570627624009)
              ·
                refine ⟨4698561900876427970718007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6264749201168570627624009 4698561900876427970718007)
                ·
                  refine ⟨7047842851314641956077011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4698561900876427970718007 7047842851314641956077011)
                  ·
                    refine ⟨10571764276971962934115517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7047842851314641956077011 10571764276971962934115517)
                    ·
                      refine ⟨3964411603864486100293319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10571764276971962934115517 3964411603864486100293319)
                      ·
                        rfl

theorem cell23_7720664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_7720664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720664 prefixEnd_7720664 := by exact prefixLift 7720664
  have htrace : WordTrace (prefixWord ++ tailWord_7720664) baseStart_7720664 baseEnd_7720664 := by
    simpa [prefixWord, tailWord_7720664, baseEnd_7720664] using wordTrace_append hprefix tailTrace_7720664
  have hstable : (prefixWord ++ tailWord_7720664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720664).length < 2 ^ (prefixWord ++ tailWord_7720664).sum := by decide
  have hdescent : baseEnd_7720664 < baseStart_7720664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720690 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_7720690 : Nat := 118140960795 + 7720690 * 2 ^ 59
def prefixEnd_7720690 : Nat := 4983230072969 + 3 ^ 40 * 7720690 * 2
def baseEnd_7720690 : Nat := 3964424954361502998568199

theorem tailTrace_7720690 : CollatzResearch.WordTrace tailWord_7720690 prefixEnd_7720690 3964424954361502998568199 := by
  unfold tailWord_7720690
  simp only [CollatzResearch.WordTrace]
  refine ⟨70399174599816548429721881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187731132266177462479258349 70399174599816548429721881)
  ·
    refine ⟨52799380949862411322291411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70399174599816548429721881 52799380949862411322291411)
    ·
      refine ⟨79199071424793616983437117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52799380949862411322291411 79199071424793616983437117)
      ·
        refine ⟨29699651784297606368788919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79199071424793616983437117 29699651784297606368788919)
        ·
          refine ⟨44549477676446409553183379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29699651784297606368788919 44549477676446409553183379)
          ·
            refine ⟨66824216514669614329775069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44549477676446409553183379 66824216514669614329775069)
            ·
              refine ⟨25059081193001105373665651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66824216514669614329775069 25059081193001105373665651)
              ·
                refine ⟨37588621789501658060498477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25059081193001105373665651 37588621789501658060498477)
                ·
                  refine ⟨14095733171063121772686929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37588621789501658060498477 14095733171063121772686929)
                  ·
                    refine ⟨10571799878297341329515197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14095733171063121772686929 10571799878297341329515197)
                    ·
                      refine ⟨3964424954361502998568199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10571799878297341329515197 3964424954361502998568199)
                      ·
                        rfl

theorem cell23_7720690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_7720690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720690 prefixEnd_7720690 := by exact prefixLift 7720690
  have htrace : WordTrace (prefixWord ++ tailWord_7720690) baseStart_7720690 baseEnd_7720690 := by
    simpa [prefixWord, tailWord_7720690, baseEnd_7720690] using wordTrace_append hprefix tailTrace_7720690
  have hstable : (prefixWord ++ tailWord_7720690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720690).length < 2 ^ (prefixWord ++ tailWord_7720690).sum := by decide
  have hdescent : baseEnd_7720690 < baseStart_7720690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720703 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 3]
def baseStart_7720703 : Nat := 118140960795 + 7720703 * 2 ^ 59
def prefixEnd_7720703 : Nat := 4983230072969 + 3 ^ 40 * 7720703 * 2
def baseEnd_7720703 : Nat := 3964431629610011447705639

theorem tailTrace_7720703 : CollatzResearch.WordTrace tailWord_7720703 prefixEnd_7720703 3964431629610011447705639 := by
  unfold tailWord_7720703
  simp only [CollatzResearch.WordTrace]
  refine ⟨281597172548219096939110763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187731448365479397959407175 281597172548219096939110763)
  ·
    refine ⟨422395758822328645408666145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281597172548219096939110763 422395758822328645408666145)
    ·
      refine ⟨316796819116746484056499609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422395758822328645408666145 316796819116746484056499609)
      ·
        refine ⟨237597614337559863042374707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316796819116746484056499609 237597614337559863042374707)
        ·
          refine ⟨356396421506339794563562061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237597614337559863042374707 356396421506339794563562061)
          ·
            refine ⟨133648658064877422961335773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356396421506339794563562061 133648658064877422961335773)
            ·
              refine ⟨50118246774329033610500915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133648658064877422961335773 50118246774329033610500915)
              ·
                refine ⟨75177370161493550415751373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50118246774329033610500915 75177370161493550415751373)
                ·
                  refine ⟨28191513810560081405906765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75177370161493550415751373 28191513810560081405906765)
                  ·
                    refine ⟨10571817678960030527215037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28191513810560081405906765 10571817678960030527215037)
                    ·
                      refine ⟨3964431629610011447705639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10571817678960030527215037 3964431629610011447705639)
                      ·
                        rfl

theorem cell23_7720703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_7720703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720703 prefixEnd_7720703 := by exact prefixLift 7720703
  have htrace : WordTrace (prefixWord ++ tailWord_7720703) baseStart_7720703 baseEnd_7720703 := by
    simpa [prefixWord, tailWord_7720703, baseEnd_7720703] using wordTrace_append hprefix tailTrace_7720703
  have hstable : (prefixWord ++ tailWord_7720703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720703).length < 2 ^ (prefixWord ++ tailWord_7720703).sum := by decide
  have hdescent : baseEnd_7720703 < baseStart_7720703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720737 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_7720737 : Nat := 118140960795 + 7720737 * 2 ^ 59
def prefixEnd_7720737 : Nat := 4983230072969 + 3 ^ 40 * 7720737 * 2
def baseEnd_7720737 : Nat := 3964449087952264314680483

theorem tailTrace_7720737 : CollatzResearch.WordTrace tailWord_7720737 prefixEnd_7720737 3964449087952264314680483 := by
  unfold tailWord_7720737
  simp only [CollatzResearch.WordTrace]
  refine ⟨281598412630095920745848465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187732275086730613830565643 281598412630095920745848465)
  ·
    refine ⟨211198809472571940559386349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281598412630095920745848465 211198809472571940559386349)
    ·
      refine ⟨79199553552214477709769881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211198809472571940559386349 79199553552214477709769881)
      ·
        refine ⟨59399665164160858282327411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79199553552214477709769881 59399665164160858282327411)
        ·
          refine ⟨89099497746241287423491117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59399665164160858282327411 89099497746241287423491117)
          ·
            refine ⟨33412311654840482783809169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89099497746241287423491117 33412311654840482783809169)
            ·
              refine ⟨25059233741130362087856877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33412311654840482783809169 25059233741130362087856877)
              ·
                refine ⟨9397212652923885782946329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25059233741130362087856877 9397212652923885782946329)
                ·
                  refine ⟨7047909489692914337209747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9397212652923885782946329 7047909489692914337209747)
                  ·
                    refine ⟨10571864234539371505814621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7047909489692914337209747 10571864234539371505814621)
                    ·
                      refine ⟨3964449087952264314680483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10571864234539371505814621 3964449087952264314680483)
                      ·
                        rfl

theorem cell23_7720737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_7720737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720737 prefixEnd_7720737 := by exact prefixLift 7720737
  have htrace : WordTrace (prefixWord ++ tailWord_7720737) baseStart_7720737 baseEnd_7720737 := by
    simpa [prefixWord, tailWord_7720737, baseEnd_7720737] using wordTrace_append hprefix tailTrace_7720737
  have hstable : (prefixWord ++ tailWord_7720737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720737).length < 2 ^ (prefixWord ++ tailWord_7720737).sum := by decide
  have hdescent : baseEnd_7720737 < baseStart_7720737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720764 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 1, 3, 2]
def baseStart_7720764 : Nat := 118140960795 + 7720764 * 2 ^ 59
def prefixEnd_7720764 : Nat := 4983230072969 + 3 ^ 40 * 7720764 * 2
def baseEnd_7720764 : Nat := 3964462951929935709042859

theorem tailTrace_7720764 : CollatzResearch.WordTrace tailWord_7720764 prefixEnd_7720764 3964462951929935709042859 := by
  unfold tailWord_7720764
  simp only [CollatzResearch.WordTrace]
  refine ⟨140799698700499052178540673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187732931600665402904720897 140799698700499052178540673)
  ·
    refine ⟨105599774025374289133905505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140799698700499052178540673 105599774025374289133905505)
    ·
      refine ⟨79199830519030716850429129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105599774025374289133905505 79199830519030716850429129)
      ·
        refine ⟨59399872889273037637821847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79199830519030716850429129 59399872889273037637821847)
        ·
          refine ⟨89099809333909556456732771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59399872889273037637821847 89099809333909556456732771)
          ·
            refine ⟨133649714000864334685099157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89099809333909556456732771 133649714000864334685099157)
            ·
              refine ⟨6264830343790515688364023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133649714000864334685099157 6264830343790515688364023)
              ·
                refine ⟨9397245515685773532546035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6264830343790515688364023 9397245515685773532546035)
                ·
                  refine ⟨14095868273528660298819053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9397245515685773532546035 14095868273528660298819053)
                  ·
                    refine ⟨5285950602573247612057145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14095868273528660298819053 5285950602573247612057145)
                    ·
                      refine ⟨3964462951929935709042859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285950602573247612057145 3964462951929935709042859)
                      ·
                        rfl

theorem cell23_7720764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_7720764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720764 prefixEnd_7720764 := by exact prefixLift 7720764
  have htrace : WordTrace (prefixWord ++ tailWord_7720764) baseStart_7720764 baseEnd_7720764 := by
    simpa [prefixWord, tailWord_7720764, baseEnd_7720764] using wordTrace_append hprefix tailTrace_7720764
  have hstable : (prefixWord ++ tailWord_7720764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720764).length < 2 ^ (prefixWord ++ tailWord_7720764).sum := by decide
  have hdescent : baseEnd_7720764 < baseStart_7720764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720773 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_7720773 : Nat := 118140960795 + 7720773 * 2 ^ 59
def prefixEnd_7720773 : Nat := 4983230072969 + 3 ^ 40 * 7720773 * 2
def baseEnd_7720773 : Nat := 3964467573255826173830317

theorem tailTrace_7720773 : CollatzResearch.WordTrace tailWord_7720773 prefixEnd_7720773 3964467573255826173830317 := by
  unfold tailWord_7720773
  simp only [CollatzResearch.WordTrace]
  refine ⟨281599725657965498894158973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187733150438643665929439315 281599725657965498894158973)
  ·
    refine ⟨105599897121737062085309615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281599725657965498894158973 105599897121737062085309615)
    ·
      refine ⟨158399845682605593127964423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105599897121737062085309615 158399845682605593127964423)
      ·
        refine ⟨237599768523908389691946635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158399845682605593127964423 237599768523908389691946635)
        ·
          refine ⟨356399652785862584537919953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237599768523908389691946635 356399652785862584537919953)
          ·
            refine ⟨267299739589396938403439965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356399652785862584537919953 267299739589396938403439965)
            ·
              refine ⟨100237402346023851901289987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267299739589396938403439965 100237402346023851901289987)
              ·
                refine ⟨150356103519035777851934981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100237402346023851901289987 150356103519035777851934981)
                ·
                  refine ⟨28191769409819208347237809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150356103519035777851934981 28191769409819208347237809)
                  ·
                    refine ⟨21143827057364406260428357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28191769409819208347237809 21143827057364406260428357)
                    ·
                      refine ⟨3964467573255826173830317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21143827057364406260428357 3964467573255826173830317)
                      ·
                        rfl

theorem cell23_7720773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_7720773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720773 prefixEnd_7720773 := by exact prefixLift 7720773
  have htrace : WordTrace (prefixWord ++ tailWord_7720773) baseStart_7720773 baseEnd_7720773 := by
    simpa [prefixWord, tailWord_7720773, baseEnd_7720773] using wordTrace_append hprefix tailTrace_7720773
  have hstable : (prefixWord ++ tailWord_7720773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720773).length < 2 ^ (prefixWord ++ tailWord_7720773).sum := by decide
  have hdescent : baseEnd_7720773 < baseStart_7720773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720777 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 4, 2, 2]
def baseStart_7720777 : Nat := 118140960795 + 7720777 * 2 ^ 59
def prefixEnd_7720777 : Nat := 4983230072969 + 3 ^ 40 * 7720777 * 2
def baseEnd_7720777 : Nat := 3964469627178444158180299

theorem tailTrace_7720777 : CollatzResearch.WordTrace tailWord_7720777 prefixEnd_7720777 3964469627178444158180299 := by
  unfold tailWord_7720777
  simp only [CollatzResearch.WordTrace]
  refine ⟨281599871549951007577304585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187733247699967338384869723 281599871549951007577304585)
  ·
    refine ⟨211199903662463255682978439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281599871549951007577304585 211199903662463255682978439)
    ·
      refine ⟨316799855493694883524467659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211199903662463255682978439 316799855493694883524467659)
      ·
        refine ⟨475199783240542325286701489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316799855493694883524467659 475199783240542325286701489)
        ·
          refine ⟨356399837430406743965026117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475199783240542325286701489 356399837430406743965026117)
          ·
            refine ⟨66824969518201264493442397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356399837430406743965026117 66824969518201264493442397)
            ·
              refine ⟨25059363569325474185040899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66824969518201264493442397 25059363569325474185040899)
              ·
                refine ⟨37589045353988211277561349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25059363569325474185040899 37589045353988211277561349)
                ·
                  refine ⟨7047946003872789614542753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37589045353988211277561349 7047946003872789614542753)
                  ·
                    refine ⟨5285959502904592210907065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7047946003872789614542753 5285959502904592210907065)
                    ·
                      refine ⟨3964469627178444158180299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5285959502904592210907065 3964469627178444158180299)
                      ·
                        rfl

theorem cell23_7720777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 2, 2].length) (baseStart_7720777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720777 prefixEnd_7720777 := by exact prefixLift 7720777
  have htrace : WordTrace (prefixWord ++ tailWord_7720777) baseStart_7720777 baseEnd_7720777 := by
    simpa [prefixWord, tailWord_7720777, baseEnd_7720777] using wordTrace_append hprefix tailTrace_7720777
  have hstable : (prefixWord ++ tailWord_7720777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720777).length < 2 ^ (prefixWord ++ tailWord_7720777).sum := by decide
  have hdescent : baseEnd_7720777 < baseStart_7720777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720873 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 8]
def baseStart_7720873 : Nat := 118140960795 + 7720873 * 2 ^ 59
def prefixEnd_7720873 : Nat := 4983230072969 + 3 ^ 40 * 7720873 * 2
def baseEnd_7720873 : Nat := 440502102369030642508873

theorem tailTrace_7720873 : CollatzResearch.WordTrace tailWord_7720873 prefixEnd_7720873 440502102369030642508873 := by
  unfold tailWord_7720873
  simp only [CollatzResearch.WordTrace]
  refine ⟨281603372957603215972799273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187735581971735477315199515 281603372957603215972799273)
  ·
    refine ⟨211202529718202411979599455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281603372957603215972799273 211202529718202411979599455)
    ·
      refine ⟨316803794577303617969399183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211202529718202411979599455 316803794577303617969399183)
      ·
        refine ⟨475205691865955426954098775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316803794577303617969399183 475205691865955426954098775)
        ·
          refine ⟨712808537798933140431148163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475205691865955426954098775 712808537798933140431148163)
          ·
            refine ⟨1069212806698399710646722245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712808537798933140431148163 1069212806698399710646722245)
            ·
              refine ⟨200477401255949945746260421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1069212806698399710646722245 200477401255949945746260421)
              ·
                refine ⟨37589512735490614827423829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200477401255949945746260421 37589512735490614827423829)
                ·
                  refine ⟨440502102369030642508873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37589512735490614827423829 440502102369030642508873)
                  ·
                    rfl

theorem cell23_7720873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 8].length) (baseStart_7720873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720873 prefixEnd_7720873 := by exact prefixLift 7720873
  have htrace : WordTrace (prefixWord ++ tailWord_7720873) baseStart_7720873 baseEnd_7720873 := by
    simpa [prefixWord, tailWord_7720873, baseEnd_7720873] using wordTrace_append hprefix tailTrace_7720873
  have hstable : (prefixWord ++ tailWord_7720873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720873).length < 2 ^ (prefixWord ++ tailWord_7720873).sum := by decide
  have hdescent : baseEnd_7720873 < baseStart_7720873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720918 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_7720918 : Nat := 118140960795 + 7720918 * 2 ^ 59
def prefixEnd_7720918 : Nat := 4983230072969 + 3 ^ 40 * 7720918 * 2
def baseEnd_7720918 : Nat := 3964542027950728106517151

theorem tailTrace_7720918 : CollatzResearch.WordTrace tailWord_7720918 prefixEnd_7720918 3964542027950728106517151 := by
  unfold tailWord_7720918
  simp only [CollatzResearch.WordTrace]
  refine ⟨17600313390152511791136713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187736676161626792438791605 17600313390152511791136713)
  ·
    refine ⟨13200235042614383843352535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17600313390152511791136713 13200235042614383843352535)
    ·
      refine ⟨19800352563921575765028803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13200235042614383843352535 19800352563921575765028803)
      ·
        refine ⟨29700528845882363647543205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19800352563921575765028803 29700528845882363647543205)
        ·
          refine ⟨5568849158602943183914351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29700528845882363647543205 5568849158602943183914351)
          ·
            refine ⟨8353273737904414775871527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568849158602943183914351 8353273737904414775871527)
            ·
              refine ⟨12529910606856622163807291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353273737904414775871527 12529910606856622163807291)
              ·
                refine ⟨18794865910284933245710937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12529910606856622163807291 18794865910284933245710937)
                ·
                  refine ⟨14096149432713699934283203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18794865910284933245710937 14096149432713699934283203)
                  ·
                    refine ⟨21144224149070549901424805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14096149432713699934283203 21144224149070549901424805)
                    ·
                      refine ⟨3964542027950728106517151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21144224149070549901424805 3964542027950728106517151)
                      ·
                        rfl

theorem cell23_7720918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_7720918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720918 prefixEnd_7720918 := by exact prefixLift 7720918
  have htrace : WordTrace (prefixWord ++ tailWord_7720918) baseStart_7720918 baseEnd_7720918 := by
    simpa [prefixWord, tailWord_7720918, baseEnd_7720918] using wordTrace_append hprefix tailTrace_7720918
  have hstable : (prefixWord ++ tailWord_7720918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720918).length < 2 ^ (prefixWord ++ tailWord_7720918).sum := by decide
  have hdescent : baseEnd_7720918 < baseStart_7720918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720920 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 3, 5]
def baseStart_7720920 : Nat := 118140960795 + 7720920 * 2 ^ 59
def prefixEnd_7720920 : Nat := 4983230072969 + 3 ^ 40 * 7720920 * 2
def baseEnd_7720920 : Nat := 1321514351637345699564047

theorem tailTrace_7720920 : CollatzResearch.WordTrace tailWord_7720920 prefixEnd_7720920 1321514351637345699564047 := by
  unfold tailWord_7720920
  simp only [CollatzResearch.WordTrace]
  refine ⟨140802543594216471499880107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187736724792288628666506809 140802543594216471499880107)
  ·
    refine ⟨211203815391324707249820161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140802543594216471499880107 211203815391324707249820161)
    ·
      refine ⟨158402861543493530437365121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211203815391324707249820161 158402861543493530437365121)
      ·
        refine ⟨118802146157620147828023841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158402861543493530437365121 118802146157620147828023841)
        ·
          refine ⟨89101609618215110871017881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118802146157620147828023841 89101609618215110871017881)
          ·
            refine ⟨66826207213661333153263411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89101609618215110871017881 66826207213661333153263411)
            ·
              refine ⟨100239310820491999729895117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66826207213661333153263411 100239310820491999729895117)
              ·
                refine ⟨37589741557684499898710669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100239310820491999729895117 37589741557684499898710669)
                ·
                  refine ⟨14096153084131687462016501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37589741557684499898710669 14096153084131687462016501)
                  ·
                    refine ⟨1321514351637345699564047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14096153084131687462016501 1321514351637345699564047)
                    ·
                      rfl

theorem cell23_7720920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_7720920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720920 prefixEnd_7720920 := by exact prefixLift 7720920
  have htrace : WordTrace (prefixWord ++ tailWord_7720920) baseStart_7720920 baseEnd_7720920 := by
    simpa [prefixWord, tailWord_7720920, baseEnd_7720920] using wordTrace_append hprefix tailTrace_7720920
  have hstable : (prefixWord ++ tailWord_7720920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720920).length < 2 ^ (prefixWord ++ tailWord_7720920).sum := by decide
  have hdescent : baseEnd_7720920 < baseStart_7720920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720921 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 2, 2, 3]
def baseStart_7720921 : Nat := 118140960795 + 7720921 * 2 ^ 59
def prefixEnd_7720921 : Nat := 4983230072969 + 3 ^ 40 * 7720921 * 2
def baseEnd_7720921 : Nat := 3964543568392691594779637

theorem tailTrace_7720921 : CollatzResearch.WordTrace tailWord_7720921 prefixEnd_7720921 3964543568392691594779637 := by
  unfold tailWord_7720921
  simp only [CollatzResearch.WordTrace]
  refine ⟨281605123661429320170546617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187736749107619546780364411 281605123661429320170546617)
  ·
    refine ⟨211203842746071990127909963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281605123661429320170546617 211203842746071990127909963)
    ·
      refine ⟨316805764119107985191864945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211203842746071990127909963 316805764119107985191864945)
      ·
        refine ⟨237604323089330988893898709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316805764119107985191864945 237604323089330988893898709)
        ·
          refine ⟨5568851322406195052200751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 237604323089330988893898709 5568851322406195052200751)
          ·
            refine ⟨8353276983609292578301127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568851322406195052200751 8353276983609292578301127)
            ·
              refine ⟨12529915475413938867451691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353276983609292578301127 12529915475413938867451691)
              ·
                refine ⟨18794873213120908301177537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12529915475413938867451691 18794873213120908301177537)
                ·
                  refine ⟨14096154909840681225883153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18794873213120908301177537 14096154909840681225883153)
                  ·
                    refine ⟨10572116182380510919412365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14096154909840681225883153 10572116182380510919412365)
                    ·
                      refine ⟨3964543568392691594779637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10572116182380510919412365 3964543568392691594779637)
                      ·
                        rfl

theorem cell23_7720921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 2, 3].length) (baseStart_7720921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720921 prefixEnd_7720921 := by exact prefixLift 7720921
  have htrace : WordTrace (prefixWord ++ tailWord_7720921) baseStart_7720921 baseEnd_7720921 := by
    simpa [prefixWord, tailWord_7720921, baseEnd_7720921] using wordTrace_append hprefix tailTrace_7720921
  have hstable : (prefixWord ++ tailWord_7720921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720921).length < 2 ^ (prefixWord ++ tailWord_7720921).sum := by decide
  have hdescent : baseEnd_7720921 < baseStart_7720921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720941 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 6]
def baseStart_7720941 : Nat := 118140960795 + 7720941 * 2 ^ 59
def prefixEnd_7720941 : Nat := 4983230072969 + 3 ^ 40 * 7720941 * 2
def baseEnd_7720941 : Nat := 440505982000642390725505

theorem tailTrace_7720941 : CollatzResearch.WordTrace tailWord_7720941 prefixEnd_7720941 440505982000642390725505 := by
  unfold tailWord_7720941
  simp only [CollatzResearch.WordTrace]
  refine ⟨281605853121356863586274677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187737235414237909057516451 281605853121356863586274677)
  ·
    refine ⟨26400548730127205961213251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281605853121356863586274677 26400548730127205961213251)
    ·
      refine ⟨39600823095190808941819877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26400548730127205961213251 39600823095190808941819877)
      ·
        refine ⟨7425154330348276676591227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39600823095190808941819877 7425154330348276676591227)
        ·
          refine ⟨11137731495522415014886841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7425154330348276676591227 11137731495522415014886841)
          ·
            refine ⟨8353298621641811261165131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11137731495522415014886841 8353298621641811261165131)
            ·
              refine ⟨12529947932462716891747697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353298621641811261165131 12529947932462716891747697)
              ·
                refine ⟨9397460949347037668810773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12529947932462716891747697 9397460949347037668810773)
                ·
                  refine ⟨440505982000642390725505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9397460949347037668810773 440505982000642390725505)
                  ·
                    rfl

theorem cell23_7720941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_7720941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720941 prefixEnd_7720941 := by exact prefixLift 7720941
  have htrace : WordTrace (prefixWord ++ tailWord_7720941) baseStart_7720941 baseEnd_7720941 := by
    simpa [prefixWord, tailWord_7720941, baseEnd_7720941] using wordTrace_append hprefix tailTrace_7720941
  have hstable : (prefixWord ++ tailWord_7720941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720941).length < 2 ^ (prefixWord ++ tailWord_7720941).sum := by decide
  have hdescent : baseEnd_7720941 < baseStart_7720941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720960 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 3]
def baseStart_7720960 : Nat := 118140960795 + 7720960 * 2 ^ 59
def prefixEnd_7720960 : Nat := 4983230072969 + 3 ^ 40 * 7720960 * 2
def baseEnd_7720960 : Nat := 3964563594138216942191957

theorem tailTrace_7720960 : CollatzResearch.WordTrace tailWord_7720960 prefixEnd_7720960 3964563594138216942191957 := by
  unfold tailWord_7720960
  simp only [CollatzResearch.WordTrace]
  refine ⟨140803273054144014915608167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187737697405525353220810889 140803273054144014915608167)
  ·
    refine ⟨211204909581216022373412251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140803273054144014915608167 211204909581216022373412251)
    ·
      refine ⟨316807364371824033560118377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211204909581216022373412251 316807364371824033560118377)
      ·
        refine ⟨237605523278868025170088783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316807364371824033560118377 237605523278868025170088783)
        ·
          refine ⟨356408284918302037755133175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237605523278868025170088783 356408284918302037755133175)
          ·
            refine ⟨534612427377453056632699763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356408284918302037755133175 534612427377453056632699763)
            ·
              refine ⟨801918641066179584949049645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534612427377453056632699763 801918641066179584949049645)
              ·
                refine ⟨300719490399817344355893617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 801918641066179584949049645 300719490399817344355893617)
                ·
                  refine ⟨225539617799863008266920213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300719490399817344355893617 225539617799863008266920213)
                  ·
                    refine ⟨10572169584368578512511885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 225539617799863008266920213 10572169584368578512511885)
                    ·
                      refine ⟨3964563594138216942191957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10572169584368578512511885 3964563594138216942191957)
                      ·
                        rfl

theorem cell23_7720960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_7720960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720960 prefixEnd_7720960 := by exact prefixLift 7720960
  have htrace : WordTrace (prefixWord ++ tailWord_7720960) baseStart_7720960 baseEnd_7720960 := by
    simpa [prefixWord, tailWord_7720960, baseEnd_7720960] using wordTrace_append hprefix tailTrace_7720960
  have hstable : (prefixWord ++ tailWord_7720960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720960).length < 2 ^ (prefixWord ++ tailWord_7720960).sum := by decide
  have hdescent : baseEnd_7720960 < baseStart_7720960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720967 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 1, 6]
def baseStart_7720967 : Nat := 118140960795 + 7720967 * 2 ^ 59
def prefixEnd_7720967 : Nat := 4983230072969 + 3 ^ 40 * 7720967 * 2
def baseEnd_7720967 : Nat := 1321522396167599471601475

theorem tailTrace_7720967 : CollatzResearch.WordTrace tailWord_7720967 prefixEnd_7720967 1321522396167599471601475 := by
  unfold tailWord_7720967
  simp only [CollatzResearch.WordTrace]
  refine ⟨281606801419262670026721155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187737867612841780017814103 281606801419262670026721155)
  ·
    refine ⟨422410202128894005040081733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281606801419262670026721155 422410202128894005040081733)
    ·
      refine ⟨79201912899167625945015325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422410202128894005040081733 79201912899167625945015325)
      ·
        refine ⟨29700717337187859729380747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79201912899167625945015325 29700717337187859729380747)
        ·
          refine ⟨44551076005781789594071121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29700717337187859729380747 44551076005781789594071121)
          ·
            refine ⟨33413307004336342195553341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44551076005781789594071121 33413307004336342195553341)
            ·
              refine ⟨12529990126626128323332503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33413307004336342195553341 12529990126626128323332503)
              ·
                refine ⟨18794985189939192484998755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12529990126626128323332503 18794985189939192484998755)
                ·
                  refine ⟨28192477784908788727498133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18794985189939192484998755 28192477784908788727498133)
                  ·
                    refine ⟨1321522396167599471601475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28192477784908788727498133 1321522396167599471601475)
                    ·
                      rfl

theorem cell23_7720967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_7720967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720967 prefixEnd_7720967 := by exact prefixLift 7720967
  have htrace : WordTrace (prefixWord ++ tailWord_7720967) baseStart_7720967 baseEnd_7720967 := by
    simpa [prefixWord, tailWord_7720967, baseEnd_7720967] using wordTrace_append hprefix tailTrace_7720967
  have hstable : (prefixWord ++ tailWord_7720967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720967).length < 2 ^ (prefixWord ++ tailWord_7720967).sum := by decide
  have hdescent : baseEnd_7720967 < baseStart_7720967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720974 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_7720974 : Nat := 118140960795 + 7720974 * 2 ^ 59
def prefixEnd_7720974 : Nat := 4983230072969 + 3 ^ 40 * 7720974 * 2
def baseEnd_7720974 : Nat := 3964570782867379887416893

theorem tailTrace_7720974 : CollatzResearch.WordTrace tailWord_7720974 prefixEnd_7720974 3964570782867379887416893 := by
  unfold tailWord_7720974
  simp only [CollatzResearch.WordTrace]
  refine ⟨35200882091279663777778247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187738037820158206814817317 35200882091279663777778247)
  ·
    refine ⟨52801323136919495666667371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35200882091279663777778247 52801323136919495666667371)
    ·
      refine ⟨79201984705379243500001057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52801323136919495666667371 79201984705379243500001057)
      ·
        refine ⟨59401488529034432625000793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79201984705379243500001057 59401488529034432625000793)
        ·
          refine ⟨44551116396775824468750595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59401488529034432625000793 44551116396775824468750595)
          ·
            refine ⟨66826674595163736703125893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44551116396775824468750595 66826674595163736703125893)
            ·
              refine ⟨12530001486593200631836105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66826674595163736703125893 12530001486593200631836105)
              ·
                refine ⟨9397501114944900473877079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12530001486593200631836105 9397501114944900473877079)
                ·
                  refine ⟨14096251672417350710815619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9397501114944900473877079 14096251672417350710815619)
                  ·
                    refine ⟨21144377508626026066223429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14096251672417350710815619 21144377508626026066223429)
                    ·
                      refine ⟨3964570782867379887416893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21144377508626026066223429 3964570782867379887416893)
                      ·
                        rfl

theorem cell23_7720974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_7720974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720974 prefixEnd_7720974 := by exact prefixLift 7720974
  have htrace : WordTrace (prefixWord ++ tailWord_7720974) baseStart_7720974 baseEnd_7720974 := by
    simpa [prefixWord, tailWord_7720974, baseEnd_7720974] using wordTrace_append hprefix tailTrace_7720974
  have hstable : (prefixWord ++ tailWord_7720974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720974).length < 2 ^ (prefixWord ++ tailWord_7720974).sum := by decide
  have hdescent : baseEnd_7720974 < baseStart_7720974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7720994 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_7720994 : Nat := 118140960795 + 7720994 * 2 ^ 59
def prefixEnd_7720994 : Nat := 4983230072969 + 3 ^ 40 * 7720994 * 2
def baseEnd_7720994 : Nat := 3964581052480469809166801

theorem tailTrace_7720994 : CollatzResearch.WordTrace tailWord_7720994 prefixEnd_7720994 3964581052480469809166801 := by
  unfold tailWord_7720994
  simp only [CollatzResearch.WordTrace]
  refine ⟨70401946547541213409488509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187738524126776569091969357 70401946547541213409488509)
  ·
    refine ⟨26400729955327955028558191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70401946547541213409488509 26400729955327955028558191)
    ·
      refine ⟨39601094932991932542837287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26400729955327955028558191 39601094932991932542837287)
      ·
        refine ⟨59401642399487898814255931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39601094932991932542837287 59401642399487898814255931)
        ·
          refine ⟨89102463599231848221383897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59401642399487898814255931 89102463599231848221383897)
          ·
            refine ⟨66826847699423886166037923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89102463599231848221383897 66826847699423886166037923)
            ·
              refine ⟨100240271549135829249056885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66826847699423886166037923 100240271549135829249056885)
              ·
                refine ⟨9397525457731483992099083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100240271549135829249056885 9397525457731483992099083)
                ·
                  refine ⟨14096288186597225988148625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9397525457731483992099083 14096288186597225988148625)
                  ·
                    refine ⟨10572216139947919491111469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14096288186597225988148625 10572216139947919491111469)
                    ·
                      refine ⟨3964581052480469809166801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10572216139947919491111469 3964581052480469809166801)
                      ·
                        rfl

theorem cell23_7720994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_7720994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7720994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7720994 prefixEnd_7720994 := by exact prefixLift 7720994
  have htrace : WordTrace (prefixWord ++ tailWord_7720994) baseStart_7720994 baseEnd_7720994 := by
    simpa [prefixWord, tailWord_7720994, baseEnd_7720994] using wordTrace_append hprefix tailTrace_7720994
  have hstable : (prefixWord ++ tailWord_7720994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7720994).length < 2 ^ (prefixWord ++ tailWord_7720994).sum := by decide
  have hdescent : baseEnd_7720994 < baseStart_7720994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7720994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721040 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 6, 6]
def baseStart_7721040 : Nat := 118140960795 + 7721040 * 2 ^ 59
def prefixEnd_7721040 : Nat := 4983230072969 + 3 ^ 40 * 7721040 * 2
def baseEnd_7721040 : Nat := 1321534890863525543063863

theorem tailTrace_7721040 : CollatzResearch.WordTrace tailWord_7721040 prefixEnd_7721040 1321534890863525543063863 := by
  unfold tailWord_7721040
  simp only [CollatzResearch.WordTrace]
  refine ⟨140804731973999101747064287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187739642631998802329419049 140804731973999101747064287)
  ·
    refine ⟨211207097960998652620596431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140804731973999101747064287 211207097960998652620596431)
    ·
      refine ⟨316810646941497978930894647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211207097960998652620596431 316810646941497978930894647)
      ·
        refine ⟨475215970412246968396341971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316810646941497978930894647 475215970412246968396341971)
        ·
          refine ⟨712823955618370452594512957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475215970412246968396341971 712823955618370452594512957)
          ·
            refine ⟨267308983356888919722942359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 712823955618370452594512957 267308983356888919722942359)
            ·
              refine ⟨400963475035333379584413539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267308983356888919722942359 400963475035333379584413539)
              ·
                refine ⟨601445212553000069376620309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400963475035333379584413539 601445212553000069376620309)
                ·
                  refine ⟨28192744338421878252029077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 601445212553000069376620309 28192744338421878252029077)
                  ·
                    refine ⟨1321534890863525543063863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28192744338421878252029077 1321534890863525543063863)
                    ·
                      rfl

theorem cell23_7721040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_7721040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721040 prefixEnd_7721040 := by exact prefixLift 7721040
  have htrace : WordTrace (prefixWord ++ tailWord_7721040) baseStart_7721040 baseEnd_7721040 := by
    simpa [prefixWord, tailWord_7721040, baseEnd_7721040] using wordTrace_append hprefix tailTrace_7721040
  have hstable : (prefixWord ++ tailWord_7721040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721040).length < 2 ^ (prefixWord ++ tailWord_7721040).sum := by decide
  have hdescent : baseEnd_7721040 < baseStart_7721040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721081 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 1, 4, 2]
def baseStart_7721081 : Nat := 118140960795 + 7721081 * 2 ^ 59
def prefixEnd_7721081 : Nat := 4983230072969 + 3 ^ 40 * 7721081 * 2
def baseEnd_7721081 : Nat := 3964625725297410968778901

theorem tailTrace_7721081 : CollatzResearch.WordTrace tailWord_7721081 prefixEnd_7721081 3964625725297410968778901 := by
  unfold tailWord_7721081
  simp only [CollatzResearch.WordTrace]
  refine ⟨281610959340849667496371097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187740639560566444997580731 281610959340849667496371097)
  ·
    refine ⟨211208219505637250622278323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281610959340849667496371097 211208219505637250622278323)
    ·
      refine ⟨316812329258455875933417485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211208219505637250622278323 316812329258455875933417485)
      ·
        refine ⟨118804623471920953475031557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316812329258455875933417485 118804623471920953475031557)
        ·
          refine ⟨22275866900985178776568417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118804623471920953475031557 22275866900985178776568417)
          ·
            refine ⟨16706900175738884082426313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22275866900985178776568417 16706900175738884082426313)
            ·
              refine ⟨12530175131804163061819735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16706900175738884082426313 12530175131804163061819735)
              ·
                refine ⟨18795262697706244592729603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12530175131804163061819735 18795262697706244592729603)
                ·
                  refine ⟨28192894046559366889094405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18795262697706244592729603 28192894046559366889094405)
                  ·
                    refine ⟨5286167633729881291705201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28192894046559366889094405 5286167633729881291705201)
                    ·
                      refine ⟨3964625725297410968778901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5286167633729881291705201 3964625725297410968778901)
                      ·
                        rfl

theorem cell23_7721081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_7721081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721081 prefixEnd_7721081 := by exact prefixLift 7721081
  have htrace : WordTrace (prefixWord ++ tailWord_7721081) baseStart_7721081 baseEnd_7721081 := by
    simpa [prefixWord, tailWord_7721081, baseEnd_7721081] using wordTrace_append hprefix tailTrace_7721081
  have hstable : (prefixWord ++ tailWord_7721081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721081).length < 2 ^ (prefixWord ++ tailWord_7721081).sum := by decide
  have hdescent : baseEnd_7721081 < baseStart_7721081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721097 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 1, 5, 3]
def baseStart_7721097 : Nat := 118140960795 + 7721097 * 2 ^ 59
def prefixEnd_7721097 : Nat := 4983230072969 + 3 ^ 40 * 7721097 * 2
def baseEnd_7721097 : Nat := 3964633940987882906178827

theorem tailTrace_7721097 : CollatzResearch.WordTrace tailWord_7721097 prefixEnd_7721097 3964633940987882906178827 := by
  unfold tailWord_7721097
  simp only [CollatzResearch.WordTrace]
  refine ⟨281611542908791702228953545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187741028605861134819302363 281611542908791702228953545)
  ·
    refine ⟨211208657181593776671715159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281611542908791702228953545 211208657181593776671715159)
    ·
      refine ⟨316812985772390665007572739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211208657181593776671715159 316812985772390665007572739)
      ·
        refine ⟨475219478658585997511359109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316812985772390665007572739 475219478658585997511359109)
        ·
          refine ⟨89103652248484874533379833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 475219478658585997511359109 89103652248484874533379833)
          ·
            refine ⟨66827739186363655900034875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89103652248484874533379833 66827739186363655900034875)
            ·
              refine ⟨100241608779545483850052313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66827739186363655900034875 100241608779545483850052313)
              ·
                refine ⟨75181206584659112887539235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100241608779545483850052313 75181206584659112887539235)
                ·
                  refine ⟨112771809876988669331308853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75181206584659112887539235 112771809876988669331308853)
                  ·
                    refine ⟨10572357175967687749810205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112771809876988669331308853 10572357175967687749810205)
                    ·
                      refine ⟨3964633940987882906178827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10572357175967687749810205 3964633940987882906178827)
                      ·
                        rfl

theorem cell23_7721097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5, 3].length) (baseStart_7721097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721097 prefixEnd_7721097 := by exact prefixLift 7721097
  have htrace : WordTrace (prefixWord ++ tailWord_7721097) baseStart_7721097 baseEnd_7721097 := by
    simpa [prefixWord, tailWord_7721097, baseEnd_7721097] using wordTrace_append hprefix tailTrace_7721097
  have hstable : (prefixWord ++ tailWord_7721097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721097).length < 2 ^ (prefixWord ++ tailWord_7721097).sum := by decide
  have hdescent : baseEnd_7721097 < baseStart_7721097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721102 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2]
def baseStart_7721102 : Nat := 118140960795 + 7721102 * 2 ^ 59
def prefixEnd_7721102 : Nat := 4983230072969 + 3 ^ 40 * 7721102 * 2
def baseEnd_7721102 : Nat := 3964636508391155386616305

theorem tailTrace_7721102 : CollatzResearch.WordTrace tailWord_7721102 prefixEnd_7721102 3964636508391155386616305 := by
  unfold tailWord_7721102
  simp only [CollatzResearch.WordTrace]
  refine ⟨35201465659221698510360695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187741150182515725388590373 35201465659221698510360695)
  ·
    refine ⟨52802198488832547765541043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35201465659221698510360695 52802198488832547765541043)
    ·
      refine ⟨79203297733248821648311565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52802198488832547765541043 79203297733248821648311565)
      ·
        refine ⟨29701236649968308118116837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79203297733248821648311565 29701236649968308118116837)
        ·
          refine ⟨5568981871869057772146907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29701236649968308118116837 5568981871869057772146907)
          ·
            refine ⟨8353472807803586658220361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568981871869057772146907 8353472807803586658220361)
            ·
              refine ⟨6265104605852689993665271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8353472807803586658220361 6265104605852689993665271)
              ·
                refine ⟨9397656908779034990497907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6265104605852689993665271 9397656908779034990497907)
                ·
                  refine ⟨14096485363168552485746861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9397656908779034990497907 14096485363168552485746861)
                  ·
                    refine ⟨5286182011188207182155073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14096485363168552485746861 5286182011188207182155073)
                    ·
                      refine ⟨3964636508391155386616305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5286182011188207182155073 3964636508391155386616305)
                      ·
                        rfl

theorem cell23_7721102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_7721102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721102 prefixEnd_7721102 := by exact prefixLift 7721102
  have htrace : WordTrace (prefixWord ++ tailWord_7721102) baseStart_7721102 baseEnd_7721102 := by
    simpa [prefixWord, tailWord_7721102, baseEnd_7721102] using wordTrace_append hprefix tailTrace_7721102
  have hstable : (prefixWord ++ tailWord_7721102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721102).length < 2 ^ (prefixWord ++ tailWord_7721102).sum := by decide
  have hdescent : baseEnd_7721102 < baseStart_7721102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721104 : List Nat := [2, 1, 1, 1, 1, 1, 8, 3, 5]
def baseStart_7721104 : Nat := 118140960795 + 7721104 * 2 ^ 59
def prefixEnd_7721104 : Nat := 4983230072969 + 3 ^ 40 * 7721104 * 2
def baseEnd_7721104 : Nat := 440515281705829375421255

theorem tailTrace_7721104 : CollatzResearch.WordTrace tailWord_7721104 prefixEnd_7721104 440515281705829375421255 := by
  unfold tailWord_7721104
  simp only [CollatzResearch.WordTrace]
  refine ⟨140805899109883171212229183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187741198813177561616305577 140805899109883171212229183)
  ·
    refine ⟨211208848664824756818343775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140805899109883171212229183 211208848664824756818343775)
    ·
      refine ⟨316813272997237135227515663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211208848664824756818343775 316813272997237135227515663)
      ·
        refine ⟨475219909495855702841273495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316813272997237135227515663 475219909495855702841273495)
        ·
          refine ⟨712829864243783554261910243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475219909495855702841273495 712829864243783554261910243)
          ·
            refine ⟨1069244796365675331392865365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712829864243783554261910243 1069244796365675331392865365)
            ·
              refine ⟨12530212457410257789760141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1069244796365675331392865365 12530212457410257789760141)
              ·
                refine ⟨4698829671528846671160053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12530212457410257789760141 4698829671528846671160053)
                ·
                  refine ⟨440515281705829375421255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4698829671528846671160053 440515281705829375421255)
                  ·
                    rfl

theorem cell23_7721104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 5].length) (baseStart_7721104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721104 prefixEnd_7721104 := by exact prefixLift 7721104
  have htrace : WordTrace (prefixWord ++ tailWord_7721104) baseStart_7721104 baseEnd_7721104 := by
    simpa [prefixWord, tailWord_7721104, baseEnd_7721104] using wordTrace_append hprefix tailTrace_7721104
  have hstable : (prefixWord ++ tailWord_7721104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721104).length < 2 ^ (prefixWord ++ tailWord_7721104).sum := by decide
  have hdescent : baseEnd_7721104 < baseStart_7721104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721177 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 8]
def baseStart_7721177 : Nat := 118140960795 + 7721177 * 2 ^ 59
def prefixEnd_7721177 : Nat := 4983230072969 + 3 ^ 40 * 7721177 * 2
def baseEnd_7721177 : Nat := 440519446604471399242051

theorem tailTrace_7721177 : CollatzResearch.WordTrace tailWord_7721177 prefixEnd_7721177 440519446604471399242051 := by
  unfold tailWord_7721177
  simp only [CollatzResearch.WordTrace]
  refine ⟨281614460748501875891865785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187742973832334583927910523 281614460748501875891865785)
  ·
    refine ⟨211210845561376406918899339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281614460748501875891865785 211210845561376406918899339)
    ·
      refine ⟨316816268342064610378349009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211210845561376406918899339 316816268342064610378349009)
      ·
        refine ⟨237612201256548457783761757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316816268342064610378349009 237612201256548457783761757)
        ·
          refine ⟨89104575471205671668910659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237612201256548457783761757 89104575471205671668910659)
          ·
            refine ⟨133656863206808507503365989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89104575471205671668910659 133656863206808507503365989)
            ·
              refine ⟨25060661851276595156881123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133656863206808507503365989 25060661851276595156881123)
              ·
                refine ⟨37590992776914892735321685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25060661851276595156881123 37590992776914892735321685)
                ·
                  refine ⟨440519446604471399242051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37590992776914892735321685 440519446604471399242051)
                  ·
                    rfl

theorem cell23_7721177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 8].length) (baseStart_7721177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721177 prefixEnd_7721177 := by exact prefixLift 7721177
  have htrace : WordTrace (prefixWord ++ tailWord_7721177) baseStart_7721177 baseEnd_7721177 := by
    simpa [prefixWord, tailWord_7721177, baseEnd_7721177] using wordTrace_append hprefix tailTrace_7721177
  have hstable : (prefixWord ++ tailWord_7721177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721177).length < 2 ^ (prefixWord ++ tailWord_7721177).sum := by decide
  have hdescent : baseEnd_7721177 < baseStart_7721177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721194 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 6]
def baseStart_7721194 : Nat := 118140960795 + 7721194 * 2 ^ 59
def prefixEnd_7721194 : Nat := 4983230072969 + 3 ^ 40 * 7721194 * 2
def baseEnd_7721194 : Nat := 440520416512374336296209

theorem tailTrace_7721194 : CollatzResearch.WordTrace tailWord_7721194 prefixEnd_7721194 440520416512374336296209 := by
  unfold tailWord_7721194
  simp only [CollatzResearch.WordTrace]
  refine ⟨70403770197360071948808659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187743387192960191863489757 70403770197360071948808659)
  ·
    refine ⟨105605655296040107923212989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70403770197360071948808659 105605655296040107923212989)
    ·
      refine ⟨39602120736015040471204871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105605655296040107923212989 39602120736015040471204871)
      ·
        refine ⟨59403181104022560706807307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39602120736015040471204871 59403181104022560706807307)
        ·
          refine ⟨89104771656033841060210961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59403181104022560706807307 89104771656033841060210961)
          ·
            refine ⟨66828578742025380795158221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89104771656033841060210961 66828578742025380795158221)
            ·
              refine ⟨25060717028259517798184333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66828578742025380795158221 25060717028259517798184333)
              ·
                refine ⟨9397768885597319174319125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25060717028259517798184333 9397768885597319174319125)
                ·
                  refine ⟨440520416512374336296209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9397768885597319174319125 440520416512374336296209)
                  ·
                    rfl

theorem cell23_7721194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_7721194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721194 prefixEnd_7721194 := by exact prefixLift 7721194
  have htrace : WordTrace (prefixWord ++ tailWord_7721194) baseStart_7721194 baseEnd_7721194 := by
    simpa [prefixWord, tailWord_7721194, baseEnd_7721194] using wordTrace_append hprefix tailTrace_7721194
  have hstable : (prefixWord ++ tailWord_7721194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721194).length < 2 ^ (prefixWord ++ tailWord_7721194).sum := by decide
  have hdescent : baseEnd_7721194 < baseStart_7721194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721265 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 2, 3, 2]
def baseStart_7721265 : Nat := 118140960795 + 7721265 * 2 ^ 59
def prefixEnd_7721265 : Nat := 4983230072969 + 3 ^ 40 * 7721265 * 2
def baseEnd_7721265 : Nat := 3964720205737838248878055

theorem tailTrace_7721265 : CollatzResearch.WordTrace tailWord_7721265 prefixEnd_7721265 3964720205737838248878055 := by
  unfold tailWord_7721265
  simp only [CollatzResearch.WordTrace]
  refine ⟨281617670372183066921069249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187745113581455377947379499 281617670372183066921069249)
  ·
    refine ⟨211213252779137300190801937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281617670372183066921069249 211213252779137300190801937)
    ·
      refine ⟨158409939584352975143101453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211213252779137300190801937 158409939584352975143101453)
      ·
        refine ⟨59403727344132365678663045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158409939584352975143101453 59403727344132365678663045)
        ·
          refine ⟨11138198877024818564749321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59403727344132365678663045 11138198877024818564749321)
          ·
            refine ⟨8353649157768613923561991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11138198877024818564749321 8353649157768613923561991)
            ·
              refine ⟨12530473736652920885342987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353649157768613923561991 12530473736652920885342987)
              ·
                refine ⟨18795710604979381328014481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12530473736652920885342987 18795710604979381328014481)
                ·
                  refine ⟨14096782953734535996010861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18795710604979381328014481 14096782953734535996010861)
                  ·
                    refine ⟨5286293607650450998504073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14096782953734535996010861 5286293607650450998504073)
                    ·
                      refine ⟨3964720205737838248878055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5286293607650450998504073 3964720205737838248878055)
                      ·
                        rfl

theorem cell23_7721265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_7721265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721265 prefixEnd_7721265 := by exact prefixLift 7721265
  have htrace : WordTrace (prefixWord ++ tailWord_7721265) baseStart_7721265 baseEnd_7721265 := by
    simpa [prefixWord, tailWord_7721265, baseEnd_7721265] using wordTrace_append hprefix tailTrace_7721265
  have hstable : (prefixWord ++ tailWord_7721265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721265).length < 2 ^ (prefixWord ++ tailWord_7721265).sum := by decide
  have hdescent : baseEnd_7721265 < baseStart_7721265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721278 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_7721278 : Nat := 118140960795 + 7721278 * 2 ^ 59
def prefixEnd_7721278 : Nat := 4983230072969 + 3 ^ 40 * 7721278 * 2
def baseEnd_7721278 : Nat := 3964726880986346698015495

theorem tailTrace_7721278 : CollatzResearch.WordTrace tailWord_7721278 prefixEnd_7721278 3964726880986346698015495 := by
  unfold tailWord_7721278
  simp only [CollatzResearch.WordTrace]
  refine ⟨35202268065141996267661561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187745429680757313427528325 35202268065141996267661561)
  ·
    refine ⟨26401701048856497200746171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35202268065141996267661561 26401701048856497200746171)
    ·
      refine ⟨39602551573284745801119257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26401701048856497200746171 39602551573284745801119257)
      ·
        refine ⟨29701913679963559350839443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39602551573284745801119257 29701913679963559350839443)
        ·
          refine ⟨44552870519945339026259165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29701913679963559350839443 44552870519945339026259165)
          ·
            refine ⟨16707326444979502134847187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44552870519945339026259165 16707326444979502134847187)
            ·
              refine ⟨25060989667469253202270781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16707326444979502134847187 25060989667469253202270781)
              ·
                refine ⟨9397871125300969950851543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25060989667469253202270781 9397871125300969950851543)
                ·
                  refine ⟨14096806687951454926277315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9397871125300969950851543 14096806687951454926277315)
                  ·
                    refine ⟨21145210031927182389415973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14096806687951454926277315 21145210031927182389415973)
                    ·
                      refine ⟨3964726880986346698015495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21145210031927182389415973 3964726880986346698015495)
                      ·
                        rfl

theorem cell23_7721278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_7721278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721278 prefixEnd_7721278 := by exact prefixLift 7721278
  have htrace : WordTrace (prefixWord ++ tailWord_7721278) baseStart_7721278 baseEnd_7721278 := by
    simpa [prefixWord, tailWord_7721278, baseEnd_7721278] using wordTrace_append hprefix tailTrace_7721278
  have hstable : (prefixWord ++ tailWord_7721278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721278).length < 2 ^ (prefixWord ++ tailWord_7721278).sum := by decide
  have hdescent : baseEnd_7721278 < baseStart_7721278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721308 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7721308 : Nat := 118140960795 + 7721308 * 2 ^ 59
def prefixEnd_7721308 : Nat := 4983230072969 + 3 ^ 40 * 7721308 * 2
def baseEnd_7721308 : Nat := 3964742285405981580640357

theorem tailTrace_7721308 : CollatzResearch.WordTrace tailWord_7721308 prefixEnd_7721308 3964742285405981580640357 := by
  unfold tailWord_7721308
  simp only [CollatzResearch.WordTrace]
  refine ⟨140809619355513642632442289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187746159140684856843256385 140809619355513642632442289)
  ·
    refine ⟨105607214516635231974331717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140809619355513642632442289 105607214516635231974331717)
    ·
      refine ⟨19801352721869105995187197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105607214516635231974331717 19801352721869105995187197)
      ·
        refine ⟨7425507270700914748195199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19801352721869105995187197 7425507270700914748195199)
        ·
          refine ⟨11138260906051372122292799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7425507270700914748195199 11138260906051372122292799)
          ·
            refine ⟨16707391359077058183439199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11138260906051372122292799 16707391359077058183439199)
            ·
              refine ⟨25061087038615587275158799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16707391359077058183439199 25061087038615587275158799)
              ·
                refine ⟨37591630557923380912738199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25061087038615587275158799 37591630557923380912738199)
                ·
                  refine ⟨56387445836885071369107299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37591630557923380912738199 56387445836885071369107299)
                  ·
                    refine ⟨84581168755327607053660949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56387445836885071369107299 84581168755327607053660949)
                    ·
                      refine ⟨3964742285405981580640357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84581168755327607053660949 3964742285405981580640357)
                      ·
                        rfl

theorem cell23_7721308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7721308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721308 prefixEnd_7721308 := by exact prefixLift 7721308
  have htrace : WordTrace (prefixWord ++ tailWord_7721308) baseStart_7721308 baseEnd_7721308 := by
    simpa [prefixWord, tailWord_7721308, baseEnd_7721308] using wordTrace_append hprefix tailTrace_7721308
  have hstable : (prefixWord ++ tailWord_7721308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721308).length < 2 ^ (prefixWord ++ tailWord_7721308).sum := by decide
  have hdescent : baseEnd_7721308 < baseStart_7721308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721311 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 3]
def baseStart_7721311 : Nat := 118140960795 + 7721311 * 2 ^ 59
def prefixEnd_7721311 : Nat := 4983230072969 + 3 ^ 40 * 7721311 * 2
def baseEnd_7721311 : Nat := 3964743825847945068902843

theorem tailTrace_7721311 : CollatzResearch.WordTrace tailWord_7721311 prefixEnd_7721311 3964743825847945068902843 := by
  unfold tailWord_7721311
  simp only [CollatzResearch.WordTrace]
  refine ⟨281619348130016416777243787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187746232086677611184829191 281619348130016416777243787)
  ·
    refine ⟨422429022195024625165865681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281619348130016416777243787 422429022195024625165865681)
    ·
      refine ⟨316821766646268468874399261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422429022195024625165865681 316821766646268468874399261)
      ·
        refine ⟨118808162492350675827899723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316821766646268468874399261 118808162492350675827899723)
        ·
          refine ⟨178212243738526013741849585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118808162492350675827899723 178212243738526013741849585)
          ·
            refine ⟨133659182803894510306387189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178212243738526013741849585 133659182803894510306387189)
            ·
              refine ⟨12530548387865110341223799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133659182803894510306387189 12530548387865110341223799)
              ·
                refine ⟨18795822581797665511835699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12530548387865110341223799 18795822581797665511835699)
                ·
                  refine ⟨28193733872696498267753549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18795822581797665511835699 28193733872696498267753549)
                  ·
                    refine ⟨10572650202261186850407581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28193733872696498267753549 10572650202261186850407581)
                    ·
                      refine ⟨3964743825847945068902843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10572650202261186850407581 3964743825847945068902843)
                      ·
                        rfl

theorem cell23_7721311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_7721311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721311 prefixEnd_7721311 := by exact prefixLift 7721311
  have htrace : WordTrace (prefixWord ++ tailWord_7721311) baseStart_7721311 baseEnd_7721311 := by
    simpa [prefixWord, tailWord_7721311, baseEnd_7721311] using wordTrace_append hprefix tailTrace_7721311
  have hstable : (prefixWord ++ tailWord_7721311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721311).length < 2 ^ (prefixWord ++ tailWord_7721311).sum := by decide
  have hdescent : baseEnd_7721311 < baseStart_7721311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721346 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_7721346 : Nat := 118140960795 + 7721346 * 2 ^ 59
def prefixEnd_7721346 : Nat := 4983230072969 + 3 ^ 40 * 7721346 * 2
def baseEnd_7721346 : Nat := 3964761797670852431965183

theorem tailTrace_7721346 : CollatzResearch.WordTrace tailWord_7721346 prefixEnd_7721346 3964761797670852431965183 := by
  unfold tailWord_7721346
  simp only [CollatzResearch.WordTrace]
  refine ⟨70405156171222404438691973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187747083123259745169845261 70405156171222404438691973)
  ·
    refine ⟨13200966782104200832254745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70405156171222404438691973 13200966782104200832254745)
    ·
      refine ⟨9900725086578150624191059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13200966782104200832254745 9900725086578150624191059)
      ·
        refine ⟨14851087629867225936286589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9900725086578150624191059 14851087629867225936286589)
        ·
          refine ⟨5569157861200209726107471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14851087629867225936286589 5569157861200209726107471)
          ·
            refine ⟨8353736791800314589161207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569157861200209726107471 8353736791800314589161207)
            ·
              refine ⟨12530605187700471883741811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353736791800314589161207 12530605187700471883741811)
              ·
                refine ⟨18795907781550707825612717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12530605187700471883741811 18795907781550707825612717)
                ·
                  refine ⟨7048465418081515434604769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18795907781550707825612717 7048465418081515434604769)
                  ·
                    refine ⟨5286349063561136575953577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7048465418081515434604769 5286349063561136575953577)
                    ·
                      refine ⟨3964761797670852431965183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5286349063561136575953577 3964761797670852431965183)
                      ·
                        rfl

theorem cell23_7721346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_7721346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721346 prefixEnd_7721346 := by exact prefixLift 7721346
  have htrace : WordTrace (prefixWord ++ tailWord_7721346) baseStart_7721346 baseEnd_7721346 := by
    simpa [prefixWord, tailWord_7721346, baseEnd_7721346] using wordTrace_append hprefix tailTrace_7721346
  have hstable : (prefixWord ++ tailWord_7721346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721346).length < 2 ^ (prefixWord ++ tailWord_7721346).sum := by decide
  have hdescent : baseEnd_7721346 < baseStart_7721346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721366 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7721366 : Nat := 118140960795 + 7721366 * 2 ^ 59
def prefixEnd_7721366 : Nat := 4983230072969 + 3 ^ 40 * 7721366 * 2
def baseEnd_7721366 : Nat := 3964772067283942353715091

theorem tailTrace_7721366 : CollatzResearch.WordTrace tailWord_7721366 prefixEnd_7721366 3964772067283942353715091 := by
  unfold tailWord_7721366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17601334634051072573155997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187747569429878107446997301 17601334634051072573155997)
  ·
    refine ⟨6600500487769152214933499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17601334634051072573155997 6600500487769152214933499)
    ·
      refine ⟨9900750731653728322400249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6600500487769152214933499 9900750731653728322400249)
      ·
        refine ⟨7425563048740296241800187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9900750731653728322400249 7425563048740296241800187)
        ·
          refine ⟨11138344573110444362700281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7425563048740296241800187 11138344573110444362700281)
          ·
            refine ⟨8353758429832833272025211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11138344573110444362700281 8353758429832833272025211)
            ·
              refine ⟨12530637644749249908037817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353758429832833272025211 12530637644749249908037817)
              ·
                refine ⟨9397978233561937431028363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12530637644749249908037817 9397978233561937431028363)
                ·
                  refine ⟨14096967350342906146542545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9397978233561937431028363 14096967350342906146542545)
                  ·
                    refine ⟨10572725512757179609906909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14096967350342906146542545 10572725512757179609906909)
                    ·
                      refine ⟨3964772067283942353715091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10572725512757179609906909 3964772067283942353715091)
                      ·
                        rfl

theorem cell23_7721366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7721366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721366 prefixEnd_7721366 := by exact prefixLift 7721366
  have htrace : WordTrace (prefixWord ++ tailWord_7721366) baseStart_7721366 baseEnd_7721366 := by
    simpa [prefixWord, tailWord_7721366, baseEnd_7721366] using wordTrace_append hprefix tailTrace_7721366
  have hstable : (prefixWord ++ tailWord_7721366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721366).length < 2 ^ (prefixWord ++ tailWord_7721366).sum := by decide
  have hdescent : baseEnd_7721366 < baseStart_7721366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721389 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_7721389 : Nat := 118140960795 + 7721389 * 2 ^ 59
def prefixEnd_7721389 : Nat := 4983230072969 + 3 ^ 40 * 7721389 * 2
def baseEnd_7721389 : Nat := 3964783877338995763727485

theorem tailTrace_7721389 : CollatzResearch.WordTrace tailWord_7721389 prefixEnd_7721389 3964783877338995763727485 := by
  unfold tailWord_7721389
  simp only [CollatzResearch.WordTrace]
  refine ⟨281622193023733836098583221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187748128682489224065722147 281622193023733836098583221)
  ·
    refine ⟨26402080595975047134242177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281622193023733836098583221 26402080595975047134242177)
    ·
      refine ⟨19801560446981285350681633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26402080595975047134242177 19801560446981285350681633)
      ·
        refine ⟨14851170335235964013011225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19801560446981285350681633 14851170335235964013011225)
        ·
          refine ⟨11138377751426973009758419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14851170335235964013011225 11138377751426973009758419)
          ·
            refine ⟨16707566627140459514637629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11138377751426973009758419 16707566627140459514637629)
            ·
              refine ⟨6265337485177672317989111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16707566627140459514637629 6265337485177672317989111)
              ·
                refine ⟨9398006227766508476983667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6265337485177672317989111 9398006227766508476983667)
                ·
                  refine ⟨14097009341649762715475501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9398006227766508476983667 14097009341649762715475501)
                  ·
                    refine ⟨5286378503118661018303313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14097009341649762715475501 5286378503118661018303313)
                    ·
                      refine ⟨3964783877338995763727485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5286378503118661018303313 3964783877338995763727485)
                      ·
                        rfl

theorem cell23_7721389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_7721389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721389 prefixEnd_7721389 := by exact prefixLift 7721389
  have htrace : WordTrace (prefixWord ++ tailWord_7721389) baseStart_7721389 baseEnd_7721389 := by
    simpa [prefixWord, tailWord_7721389, baseEnd_7721389] using wordTrace_append hprefix tailTrace_7721389
  have hstable : (prefixWord ++ tailWord_7721389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721389).length < 2 ^ (prefixWord ++ tailWord_7721389).sum := by decide
  have hdescent : baseEnd_7721389 < baseStart_7721389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721441 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_7721441 : Nat := 118140960795 + 7721441 * 2 ^ 59
def prefixEnd_7721441 : Nat := 4983230072969 + 3 ^ 40 * 7721441 * 2
def baseEnd_7721441 : Nat := 3964810578333029560277245

theorem tailTrace_7721441 : CollatzResearch.WordTrace tailWord_7721441 prefixEnd_7721441 3964810578333029560277245 := by
  unfold tailWord_7721441
  simp only [CollatzResearch.WordTrace]
  refine ⟨281624089619545448979476177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187749393079696965986317451 281624089619545448979476177)
  ·
    refine ⟨211218067214659086734607133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281624089619545448979476177 211218067214659086734607133)
    ·
      refine ⟨79206775205497157525477675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211218067214659086734607133 79206775205497157525477675)
      ·
        refine ⟨118810162808245736288216513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79206775205497157525477675 118810162808245736288216513)
        ·
          refine ⟨89107622106184302216162385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118810162808245736288216513 89107622106184302216162385)
          ·
            refine ⟨66830716579638226662121789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89107622106184302216162385 66830716579638226662121789)
            ·
              refine ⟨25061518717364334998295671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66830716579638226662121789 25061518717364334998295671)
              ·
                refine ⟨37592278076046502497443507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25061518717364334998295671 37592278076046502497443507)
                ·
                  refine ⟨56388417114069753746165261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37592278076046502497443507 56388417114069753746165261)
                  ·
                    refine ⟨21145656417776157654811973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56388417114069753746165261 21145656417776157654811973)
                    ·
                      refine ⟨3964810578333029560277245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21145656417776157654811973 3964810578333029560277245)
                      ·
                        rfl

theorem cell23_7721441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_7721441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721441 prefixEnd_7721441 := by exact prefixLift 7721441
  have htrace : WordTrace (prefixWord ++ tailWord_7721441) baseStart_7721441 baseEnd_7721441 := by
    simpa [prefixWord, tailWord_7721441, baseEnd_7721441] using wordTrace_append hprefix tailTrace_7721441
  have hstable : (prefixWord ++ tailWord_7721441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721441).length < 2 ^ (prefixWord ++ tailWord_7721441).sum := by decide
  have hdescent : baseEnd_7721441 < baseStart_7721441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721451 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 5, 4]
def baseStart_7721451 : Nat := 118140960795 + 7721451 * 2 ^ 59
def prefixEnd_7721451 : Nat := 4983230072969 + 3 ^ 40 * 7721451 * 2
def baseEnd_7721451 : Nat := 1321605237713191507050733

theorem tailTrace_7721451 : CollatzResearch.WordTrace tailWord_7721451 prefixEnd_7721451 1321605237713191507050733 := by
  unfold tailWord_7721451
  simp only [CollatzResearch.WordTrace]
  refine ⟨281624454349509220687340207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187749636233006147124893471 281624454349509220687340207)
  ·
    refine ⟨422436681524263831031010311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281624454349509220687340207 422436681524263831031010311)
    ·
      refine ⟨633655022286395746546515467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422436681524263831031010311 633655022286395746546515467)
      ·
        refine ⟨950482533429593619819773201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633655022286395746546515467 950482533429593619819773201)
        ·
          refine ⟨712861900072195214864829901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950482533429593619819773201 712861900072195214864829901)
          ·
            refine ⟨267323212527073205574311213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 712861900072195214864829901 267323212527073205574311213)
            ·
              refine ⟨100246204697652452090366705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267323212527073205574311213 100246204697652452090366705)
              ·
                refine ⟨75184653523239339067775029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100246204697652452090366705 75184653523239339067775029)
                ·
                  refine ⟨7048561267803688037603909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75184653523239339067775029 7048561267803688037603909)
                  ·
                    refine ⟨1321605237713191507050733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7048561267803688037603909 1321605237713191507050733)
                    ·
                      rfl

theorem cell23_7721451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 4].length) (baseStart_7721451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721451 prefixEnd_7721451 := by exact prefixLift 7721451
  have htrace : WordTrace (prefixWord ++ tailWord_7721451) baseStart_7721451 baseEnd_7721451 := by
    simpa [prefixWord, tailWord_7721451, baseEnd_7721451] using wordTrace_append hprefix tailTrace_7721451
  have hstable : (prefixWord ++ tailWord_7721451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721451).length < 2 ^ (prefixWord ++ tailWord_7721451).sum := by decide
  have hdescent : baseEnd_7721451 < baseStart_7721451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721491 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 3]
def baseStart_7721491 : Nat := 118140960795 + 7721491 * 2 ^ 59
def prefixEnd_7721491 : Nat := 4983230072969 + 3 ^ 40 * 7721491 * 2
def baseEnd_7721491 : Nat := 3964836252365754364652015

theorem tailTrace_7721491 : CollatzResearch.WordTrace tailWord_7721491 prefixEnd_7721491 3964836252365754364652015 := by
  unfold tailWord_7721491
  simp only [CollatzResearch.WordTrace]
  refine ⟨281625913269364307518796327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187750608846242871679197551 281625913269364307518796327)
  ·
    refine ⟨422438869904046461278194491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281625913269364307518796327 422438869904046461278194491)
    ·
      refine ⟨633658304856069691917291737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422438869904046461278194491 633658304856069691917291737)
      ·
        refine ⟨475243728642052268937968803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633658304856069691917291737 475243728642052268937968803)
        ·
          refine ⟨712865592963078403406953205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475243728642052268937968803 712865592963078403406953205)
          ·
            refine ⟨66831149340288600319401863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 712865592963078403406953205 66831149340288600319401863)
            ·
              refine ⟨100246724010432900479102795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66831149340288600319401863 100246724010432900479102795)
              ·
                refine ⟨150370086015649350718654193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100246724010432900479102795 150370086015649350718654193)
                ·
                  refine ⟨112777564511737013038990645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150370086015649350718654193 112777564511737013038990645)
                  ·
                    refine ⟨10572896672975344972405373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112777564511737013038990645 10572896672975344972405373)
                    ·
                      refine ⟨3964836252365754364652015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10572896672975344972405373 3964836252365754364652015)
                      ·
                        rfl

theorem cell23_7721491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 3].length) (baseStart_7721491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721491 prefixEnd_7721491 := by exact prefixLift 7721491
  have htrace : WordTrace (prefixWord ++ tailWord_7721491) baseStart_7721491 baseEnd_7721491 := by
    simpa [prefixWord, tailWord_7721491, baseEnd_7721491] using wordTrace_append hprefix tailTrace_7721491
  have hstable : (prefixWord ++ tailWord_7721491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721491).length < 2 ^ (prefixWord ++ tailWord_7721491).sum := by decide
  have hdescent : baseEnd_7721491 < baseStart_7721491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721548 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_7721548 : Nat := 118140960795 + 7721548 * 2 ^ 59
def prefixEnd_7721548 : Nat := 4983230072969 + 3 ^ 40 * 7721548 * 2
def baseEnd_7721548 : Nat := 3964865520763060641639253

theorem tailTrace_7721548 : CollatzResearch.WordTrace tailWord_7721548 prefixEnd_7721548 3964865520763060641639253 := by
  unfold tailWord_7721548
  simp only [CollatzResearch.WordTrace]
  refine ⟨140813996115078903126810649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187751994820105204169080865 140813996115078903126810649)
  ·
    refine ⟨105610497086309177345107987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140813996115078903126810649 105610497086309177345107987)
    ·
      refine ⟨158415745629463766017661981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105610497086309177345107987 158415745629463766017661981)
      ·
        refine ⟨59405904611048912256623243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158415745629463766017661981 59405904611048912256623243)
        ·
          refine ⟨89108856916573368384934865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59405904611048912256623243 89108856916573368384934865)
          ·
            refine ⟨66831642687430026288701149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89108856916573368384934865 66831642687430026288701149)
            ·
              refine ⟨25061866007786259858262931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66831642687430026288701149 25061866007786259858262931)
              ·
                refine ⟨37592799011679389787394397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25061866007786259858262931 37592799011679389787394397)
                ·
                  refine ⟨14097299629379771170272899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37592799011679389787394397 14097299629379771170272899)
                  ·
                    refine ⟨21145949444069656755409349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14097299629379771170272899 21145949444069656755409349)
                    ·
                      refine ⟨3964865520763060641639253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21145949444069656755409349 3964865520763060641639253)
                      ·
                        rfl

theorem cell23_7721548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_7721548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721548 prefixEnd_7721548 := by exact prefixLift 7721548
  have htrace : WordTrace (prefixWord ++ tailWord_7721548) baseStart_7721548 baseEnd_7721548 := by
    simpa [prefixWord, tailWord_7721548, baseEnd_7721548] using wordTrace_append hprefix tailTrace_7721548
  have hstable : (prefixWord ++ tailWord_7721548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721548).length < 2 ^ (prefixWord ++ tailWord_7721548).sum := by decide
  have hdescent : baseEnd_7721548 < baseStart_7721548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721551 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 5]
def baseStart_7721551 : Nat := 118140960795 + 7721551 * 2 ^ 59
def prefixEnd_7721551 : Nat := 4983230072969 + 3 ^ 40 * 7721551 * 2
def baseEnd_7721551 : Nat := 3964867061205024129901739

theorem tailTrace_7721551 : CollatzResearch.WordTrace tailWord_7721551 prefixEnd_7721551 3964867061205024129901739 := by
  unfold tailWord_7721551
  simp only [CollatzResearch.WordTrace]
  refine ⟨281628101649146937765980507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187752067766097958510653671 281628101649146937765980507)
  ·
    refine ⟨422442152473720406648970761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281628101649146937765980507 422442152473720406648970761)
    ·
      refine ⟨316831614355290304986728071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422442152473720406648970761 316831614355290304986728071)
      ·
        refine ⟨475247421532935457480092107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316831614355290304986728071 475247421532935457480092107)
        ·
          refine ⟨712871132299403186220138161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475247421532935457480092107 712871132299403186220138161)
          ·
            refine ⟨534653349224552389665103621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 712871132299403186220138161 534653349224552389665103621)
            ·
              refine ⟨100247502979603573062206929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 534653349224552389665103621 100247502979603573062206929)
              ·
                refine ⟨75185627234702679796655197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100247502979603573062206929 75185627234702679796655197)
                ·
                  refine ⟨28194610213013504923745699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75185627234702679796655197 28194610213013504923745699)
                  ·
                    refine ⟨42291915319520257385618549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28194610213013504923745699 42291915319520257385618549)
                    ·
                      refine ⟨3964867061205024129901739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42291915319520257385618549 3964867061205024129901739)
                      ·
                        rfl

theorem cell23_7721551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_7721551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721551 prefixEnd_7721551 := by exact prefixLift 7721551
  have htrace : WordTrace (prefixWord ++ tailWord_7721551) baseStart_7721551 baseEnd_7721551 := by
    simpa [prefixWord, tailWord_7721551, baseEnd_7721551] using wordTrace_append hprefix tailTrace_7721551
  have hstable : (prefixWord ++ tailWord_7721551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721551).length < 2 ^ (prefixWord ++ tailWord_7721551).sum := by decide
  have hdescent : baseEnd_7721551 < baseStart_7721551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721568 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 5]
def baseStart_7721568 : Nat := 118140960795 + 7721568 * 2 ^ 59
def prefixEnd_7721568 : Nat := 4983230072969 + 3 ^ 40 * 7721568 * 2
def baseEnd_7721568 : Nat := 3964875790376150563389161

theorem tailTrace_7721568 : CollatzResearch.WordTrace tailWord_7721568 prefixEnd_7721568 3964875790376150563389161 := by
  unfold tailWord_7721568
  simp only [CollatzResearch.WordTrace]
  refine ⟨140814360845042674834674679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187752481126723566446232905 140814360845042674834674679)
  ·
    refine ⟨211221541267564012252012019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140814360845042674834674679 211221541267564012252012019)
    ·
      refine ⟨316832311901346018378018029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211221541267564012252012019 316832311901346018378018029)
      ·
        refine ⟨118812116963004756891756761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316832311901346018378018029 118812116963004756891756761)
        ·
          refine ⟨89109087722253567668817571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118812116963004756891756761 89109087722253567668817571)
          ·
            refine ⟨133663631583380351503226357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89109087722253567668817571 133663631583380351503226357)
            ·
              refine ⟨12530965460941907953427471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133663631583380351503226357 12530965460941907953427471)
              ·
                refine ⟨18796448191412861930141207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12530965460941907953427471 18796448191412861930141207)
                ·
                  refine ⟨28194672287119292895211811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18796448191412861930141207 28194672287119292895211811)
                  ·
                    refine ⟨42292008430678939342817717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28194672287119292895211811 42292008430678939342817717)
                    ·
                      refine ⟨3964875790376150563389161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42292008430678939342817717 3964875790376150563389161)
                      ·
                        rfl

theorem cell23_7721568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_7721568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721568 prefixEnd_7721568 := by exact prefixLift 7721568
  have htrace : WordTrace (prefixWord ++ tailWord_7721568) baseStart_7721568 baseEnd_7721568 := by
    simpa [prefixWord, tailWord_7721568, baseEnd_7721568] using wordTrace_append hprefix tailTrace_7721568
  have hstable : (prefixWord ++ tailWord_7721568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721568).length < 2 ^ (prefixWord ++ tailWord_7721568).sum := by decide
  have hdescent : baseEnd_7721568 < baseStart_7721568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721578 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_7721578 : Nat := 118140960795 + 7721578 * 2 ^ 59
def prefixEnd_7721578 : Nat := 4983230072969 + 3 ^ 40 * 7721578 * 2
def baseEnd_7721578 : Nat := 3964880925182695524264115

theorem tailTrace_7721578 : CollatzResearch.WordTrace tailWord_7721578 prefixEnd_7721578 3964880925182695524264115 := by
  unfold tailWord_7721578
  simp only [CollatzResearch.WordTrace]
  refine ⟨70407271605012280344303347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187752724280032747584808925 70407271605012280344303347)
  ·
    refine ⟨105610907407518420516455021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70407271605012280344303347 105610907407518420516455021)
    ·
      refine ⟨39604090277819407693670633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105610907407518420516455021 39604090277819407693670633)
      ·
        refine ⟨29703067708364555770252975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39604090277819407693670633 29703067708364555770252975)
        ·
          refine ⟨44554601562546833655379463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29703067708364555770252975 44554601562546833655379463)
          ·
            refine ⟨66831902343820250483069195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44554601562546833655379463 66831902343820250483069195)
            ·
              refine ⟨100247853515730375724603793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66831902343820250483069195 100247853515730375724603793)
              ·
                refine ⟨75185890136797781793452845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100247853515730375724603793 75185890136797781793452845)
                ·
                  refine ⟨28194708801299168172544817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75185890136797781793452845 28194708801299168172544817)
                  ·
                    refine ⟨21146031600974376129408613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28194708801299168172544817 21146031600974376129408613)
                    ·
                      refine ⟨3964880925182695524264115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21146031600974376129408613 3964880925182695524264115)
                      ·
                        rfl

theorem cell23_7721578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_7721578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721578 prefixEnd_7721578 := by exact prefixLift 7721578
  have htrace : WordTrace (prefixWord ++ tailWord_7721578) baseStart_7721578 baseEnd_7721578 := by
    simpa [prefixWord, tailWord_7721578, baseEnd_7721578] using wordTrace_append hprefix tailTrace_7721578
  have hstable : (prefixWord ++ tailWord_7721578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721578).length < 2 ^ (prefixWord ++ tailWord_7721578).sum := by decide
  have hdescent : baseEnd_7721578 < baseStart_7721578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721591 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_7721591 : Nat := 118140960795 + 7721591 * 2 ^ 59
def prefixEnd_7721591 : Nat := 4983230072969 + 3 ^ 40 * 7721591 * 2
def baseEnd_7721591 : Nat := 3964887600431203973401555

theorem tailTrace_7721591 : CollatzResearch.WordTrace tailWord_7721591 prefixEnd_7721591 3964887600431203973401555 := by
  unfold tailWord_7721591
  simp only [CollatzResearch.WordTrace]
  refine ⟨281629560569002024597436627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187753040379334683064957751 281629560569002024597436627)
  ·
    refine ⟨422444340853503036896154941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281629560569002024597436627 422444340853503036896154941)
    ·
      refine ⟨158416627820063638836058103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422444340853503036896154941 158416627820063638836058103)
      ·
        refine ⟨237624941730095458254087155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158416627820063638836058103 237624941730095458254087155)
        ·
          refine ⟨356437412595143187381130733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237624941730095458254087155 356437412595143187381130733)
          ·
            refine ⟨133664029723178695267924025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356437412595143187381130733 133664029723178695267924025)
            ·
              refine ⟨100248022292384021450943019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133664029723178695267924025 100248022292384021450943019)
              ·
                refine ⟨150372033438576032176414529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100248022292384021450943019 150372033438576032176414529)
                ·
                  refine ⟨112779025078932024132310897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150372033438576032176414529 112779025078932024132310897)
                  ·
                    refine ⟨84584268809199018099233173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112779025078932024132310897 84584268809199018099233173)
                    ·
                      refine ⟨3964887600431203973401555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84584268809199018099233173 3964887600431203973401555)
                      ·
                        rfl

theorem cell23_7721591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_7721591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721591 prefixEnd_7721591 := by exact prefixLift 7721591
  have htrace : WordTrace (prefixWord ++ tailWord_7721591) baseStart_7721591 baseEnd_7721591 := by
    simpa [prefixWord, tailWord_7721591, baseEnd_7721591] using wordTrace_append hprefix tailTrace_7721591
  have hstable : (prefixWord ++ tailWord_7721591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721591).length < 2 ^ (prefixWord ++ tailWord_7721591).sum := by decide
  have hdescent : baseEnd_7721591 < baseStart_7721591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721626 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 2, 4]
def baseStart_7721626 : Nat := 118140960795 + 7721626 * 2 ^ 59
def prefixEnd_7721626 : Nat := 4983230072969 + 3 ^ 40 * 7721626 * 2
def baseEnd_7721626 : Nat := 1321635190751370445487965

theorem tailTrace_7721626 : CollatzResearch.WordTrace tailWord_7721626 prefixEnd_7721626 1321635190751370445487965 := by
  unfold tailWord_7721626
  simp only [CollatzResearch.WordTrace]
  refine ⟨70407709280968806393740183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187753891415916817049973821 70407709280968806393740183)
  ·
    refine ⟨105611563921453209590610275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70407709280968806393740183 105611563921453209590610275)
    ·
      refine ⟨158417345882179814385915413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105611563921453209590610275 158417345882179814385915413)
      ·
        refine ⟨7425813088227178799339785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158417345882179814385915413 7425813088227178799339785)
        ·
          refine ⟨5569359816170384099504839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7425813088227178799339785 5569359816170384099504839)
          ·
            refine ⟨8354039724255576149257259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569359816170384099504839 8354039724255576149257259)
            ·
              refine ⟨12531059586383364223885889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354039724255576149257259 12531059586383364223885889)
              ·
                refine ⟨9398294689787523167914417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12531059586383364223885889 9398294689787523167914417)
                ·
                  refine ⟨7048721017340642375935813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9398294689787523167914417 7048721017340642375935813)
                  ·
                    refine ⟨1321635190751370445487965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7048721017340642375935813 1321635190751370445487965)
                    ·
                      rfl

theorem cell23_7721626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_7721626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721626 prefixEnd_7721626 := by exact prefixLift 7721626
  have htrace : WordTrace (prefixWord ++ tailWord_7721626) baseStart_7721626 baseEnd_7721626 := by
    simpa [prefixWord, tailWord_7721626, baseEnd_7721626] using wordTrace_append hprefix tailTrace_7721626
  have hstable : (prefixWord ++ tailWord_7721626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721626).length < 2 ^ (prefixWord ++ tailWord_7721626).sum := by decide
  have hdescent : baseEnd_7721626 < baseStart_7721626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721632 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 4, 1, 3]
def baseStart_7721632 : Nat := 118140960795 + 7721632 * 2 ^ 59
def prefixEnd_7721632 : Nat := 4983230072969 + 3 ^ 40 * 7721632 * 2
def baseEnd_7721632 : Nat := 3964908653138038312988867

theorem tailTrace_7721632 : CollatzResearch.WordTrace tailWord_7721632 prefixEnd_7721632 3964908653138038312988867 := by
  unfold tailWord_7721632
  simp only [CollatzResearch.WordTrace]
  refine ⟨140815527980926744299839575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187754037307902325733119433 140815527980926744299839575)
  ·
    refine ⟨211223291971390116449759363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140815527980926744299839575 211223291971390116449759363)
    ·
      refine ⟨316834937957085174674639045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211223291971390116449759363 316834937957085174674639045)
      ·
        refine ⟨59406550866953470251494821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316834937957085174674639045 59406550866953470251494821)
        ·
          refine ⟨11138728287553775672155279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59406550866953470251494821 11138728287553775672155279)
          ·
            refine ⟨16708092431330663508232919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11138728287553775672155279 16708092431330663508232919)
            ·
              refine ⟨25062138646995995262349379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16708092431330663508232919 25062138646995995262349379)
              ·
                refine ⟨37593207970493992893524069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25062138646995995262349379 37593207970493992893524069)
                ·
                  refine ⟨7048726494467623667535763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37593207970493992893524069 7048726494467623667535763)
                  ·
                    refine ⟨10573089741701435501303645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7048726494467623667535763 10573089741701435501303645)
                    ·
                      refine ⟨3964908653138038312988867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10573089741701435501303645 3964908653138038312988867)
                      ·
                        rfl

theorem cell23_7721632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_7721632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721632 prefixEnd_7721632 := by exact prefixLift 7721632
  have htrace : WordTrace (prefixWord ++ tailWord_7721632) baseStart_7721632 baseEnd_7721632 := by
    simpa [prefixWord, tailWord_7721632, baseEnd_7721632] using wordTrace_append hprefix tailTrace_7721632
  have hstable : (prefixWord ++ tailWord_7721632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721632).length < 2 ^ (prefixWord ++ tailWord_7721632).sum := by decide
  have hdescent : baseEnd_7721632 < baseStart_7721632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721649 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 1, 3, 3]
def baseStart_7721649 : Nat := 118140960795 + 7721649 * 2 ^ 59
def prefixEnd_7721649 : Nat := 4983230072969 + 3 ^ 40 * 7721649 * 2
def baseEnd_7721649 : Nat := 3964917382309164746476289

theorem tailTrace_7721649 : CollatzResearch.WordTrace tailWord_7721649 prefixEnd_7721649 3964917382309164746476289 := by
  unfold tailWord_7721649
  simp only [CollatzResearch.WordTrace]
  refine ⟨281631676002791900503048001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187754450668527933668698667 281631676002791900503048001)
  ·
    refine ⟨211223757002093925377286001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281631676002791900503048001 211223757002093925377286001)
    ·
      refine ⟨158417817751570444032964501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211223757002093925377286001 158417817751570444032964501)
      ·
        refine ⟨7425835207104864564045211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158417817751570444032964501 7425835207104864564045211)
        ·
          refine ⟨11138752810657296846067817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7425835207104864564045211 11138752810657296846067817)
          ·
            refine ⟨8354064607992972634550863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11138752810657296846067817 8354064607992972634550863)
            ·
              refine ⟨12531096911989458951826295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354064607992972634550863 12531096911989458951826295)
              ·
                refine ⟨18796645367984188427739443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12531096911989458951826295 18796645367984188427739443)
                ·
                  refine ⟨28194968051976282641609165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18796645367984188427739443 28194968051976282641609165)
                  ·
                    refine ⟨10573113019491105990603437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28194968051976282641609165 10573113019491105990603437)
                    ·
                      refine ⟨3964917382309164746476289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10573113019491105990603437 3964917382309164746476289)
                      ·
                        rfl

theorem cell23_7721649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_7721649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721649 prefixEnd_7721649 := by exact prefixLift 7721649
  have htrace : WordTrace (prefixWord ++ tailWord_7721649) baseStart_7721649 baseEnd_7721649 := by
    simpa [prefixWord, tailWord_7721649, baseEnd_7721649] using wordTrace_append hprefix tailTrace_7721649
  have hstable : (prefixWord ++ tailWord_7721649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721649).length < 2 ^ (prefixWord ++ tailWord_7721649).sum := by decide
  have hdescent : baseEnd_7721649 < baseStart_7721649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721658 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_7721658 : Nat := 118140960795 + 7721658 * 2 ^ 59
def prefixEnd_7721658 : Nat := 4983230072969 + 3 ^ 40 * 7721658 * 2
def baseEnd_7721658 : Nat := 3964922003635055211263747

theorem tailTrace_7721658 : CollatzResearch.WordTrace tailWord_7721658 prefixEnd_7721658 3964922003635055211263747 := by
  unfold tailWord_7721658
  simp only [CollatzResearch.WordTrace]
  refine ⟨70408001064939823760031407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187754669506506196693417085 70408001064939823760031407)
  ·
    refine ⟨105612001597409735640047111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70408001064939823760031407 105612001597409735640047111)
    ·
      refine ⟨158418002396114603460070667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105612001597409735640047111 158418002396114603460070667)
      ·
        refine ⟨237627003594171905190106001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158418002396114603460070667 237627003594171905190106001)
        ·
          refine ⟨178220252695628928892579501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237627003594171905190106001 178220252695628928892579501)
          ·
            refine ⟨66832594760860848334717313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178220252695628928892579501 66832594760860848334717313)
            ·
              refine ⟨50124446070645636251037985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66832594760860848334717313 50124446070645636251037985)
              ·
                refine ⟨37593334552984227188278489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50124446070645636251037985 37593334552984227188278489)
                ·
                  refine ⟨28195000914738170391208867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37593334552984227188278489 28195000914738170391208867)
                  ·
                    refine ⟨42292501372107255586813301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28195000914738170391208867 42292501372107255586813301)
                    ·
                      refine ⟨3964922003635055211263747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42292501372107255586813301 3964922003635055211263747)
                      ·
                        rfl

theorem cell23_7721658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_7721658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721658 prefixEnd_7721658 := by exact prefixLift 7721658
  have htrace : WordTrace (prefixWord ++ tailWord_7721658) baseStart_7721658 baseEnd_7721658 := by
    simpa [prefixWord, tailWord_7721658, baseEnd_7721658] using wordTrace_append hprefix tailTrace_7721658
  have hstable : (prefixWord ++ tailWord_7721658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721658).length < 2 ^ (prefixWord ++ tailWord_7721658).sum := by decide
  have hdescent : baseEnd_7721658 < baseStart_7721658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721672 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 4, 2, 2]
def baseStart_7721672 : Nat := 118140960795 + 7721672 * 2 ^ 59
def prefixEnd_7721672 : Nat := 4983230072969 + 3 ^ 40 * 7721672 * 2
def baseEnd_7721672 : Nat := 3964929192364218156488683

theorem tailTrace_7721672 : CollatzResearch.WordTrace tailWord_7721672 prefixEnd_7721672 3964929192364218156488683 := by
  unfold tailWord_7721672
  simp only [CollatzResearch.WordTrace]
  refine ⟨140816257440854287715567635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187755009921139050287423513 140816257440854287715567635)
  ·
    refine ⟨211224386161281431573351453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140816257440854287715567635 211224386161281431573351453)
    ·
      refine ⟨79209144810480536840006795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211224386161281431573351453 79209144810480536840006795)
      ·
        refine ⟨118813717215720805260010193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79209144810480536840006795 118813717215720805260010193)
        ·
          refine ⟨89110287911790603945007645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118813717215720805260010193 89110287911790603945007645)
          ·
            refine ⟨33416357966921476479377867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89110287911790603945007645 33416357966921476479377867)
            ·
              refine ⟨50124536950382214719066801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33416357966921476479377867 50124536950382214719066801)
              ·
                refine ⟨37593402712786661039300101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50124536950382214719066801 37593402712786661039300101)
                ·
                  refine ⟨7048763008647498944868769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37593402712786661039300101 7048763008647498944868769)
                  ·
                    refine ⟨5286572256485624208651577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7048763008647498944868769 5286572256485624208651577)
                    ·
                      refine ⟨3964929192364218156488683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5286572256485624208651577 3964929192364218156488683)
                      ·
                        rfl

theorem cell23_7721672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_7721672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721672 prefixEnd_7721672 := by exact prefixLift 7721672
  have htrace : WordTrace (prefixWord ++ tailWord_7721672) baseStart_7721672 baseEnd_7721672 := by
    simpa [prefixWord, tailWord_7721672, baseEnd_7721672] using wordTrace_append hprefix tailTrace_7721672
  have hstable : (prefixWord ++ tailWord_7721672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721672).length < 2 ^ (prefixWord ++ tailWord_7721672).sum := by decide
  have hdescent : baseEnd_7721672 < baseStart_7721672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721695 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 7]
def baseStart_7721695 : Nat := 118140960795 + 7721695 * 2 ^ 59
def prefixEnd_7721695 : Nat := 4983230072969 + 3 ^ 40 * 7721695 * 2
def baseEnd_7721695 : Nat := 440549000268807951833453

theorem tailTrace_7721695 : CollatzResearch.WordTrace tailWord_7721695 prefixEnd_7721695 440549000268807951833453 := by
  unfold tailWord_7721695
  simp only [CollatzResearch.WordTrace]
  refine ⟨281633353760625250359222539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187755569173750166906148359 281633353760625250359222539)
  ·
    refine ⟨422450030640937875538833809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281633353760625250359222539 422450030640937875538833809)
    ·
      refine ⟨316837522980703406654125357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422450030640937875538833809 316837522980703406654125357)
      ·
        refine ⟨118814071117763777495297009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316837522980703406654125357 118814071117763777495297009)
        ·
          refine ⟨89110553338322833121472757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118814071117763777495297009 89110553338322833121472757)
          ·
            refine ⟨8354114375467765605138071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89110553338322833121472757 8354114375467765605138071)
            ·
              refine ⟨12531171563201648407707107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354114375467765605138071 12531171563201648407707107)
              ·
                refine ⟨18796757344802472611560661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12531171563201648407707107 18796757344802472611560661)
                ·
                  refine ⟨440549000268807951833453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18796757344802472611560661 440549000268807951833453)
                  ·
                    rfl

theorem cell23_7721695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 7].length) (baseStart_7721695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721695 prefixEnd_7721695 := by exact prefixLift 7721695
  have htrace : WordTrace (prefixWord ++ tailWord_7721695) baseStart_7721695 baseEnd_7721695 := by
    simpa [prefixWord, tailWord_7721695, baseEnd_7721695] using wordTrace_append hprefix tailTrace_7721695
  have hstable : (prefixWord ++ tailWord_7721695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721695).length < 2 ^ (prefixWord ++ tailWord_7721695).sum := by decide
  have hdescent : baseEnd_7721695 < baseStart_7721695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721708 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_7721708 : Nat := 118140960795 + 7721708 * 2 ^ 59
def prefixEnd_7721708 : Nat := 4983230072969 + 3 ^ 40 * 7721708 * 2
def baseEnd_7721708 : Nat := 1321649225889260005212839

theorem tailTrace_7721708 : CollatzResearch.WordTrace tailWord_7721708 prefixEnd_7721708 1321649225889260005212839 := by
  unfold tailWord_7721708
  simp only [CollatzResearch.WordTrace]
  refine ⟨140816913954789076789722889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187755885273052102386297185 140816913954789076789722889)
  ·
    refine ⟨105612685466091807592292167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140816913954789076789722889 105612685466091807592292167)
    ·
      refine ⟨158419028199137711388438251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105612685466091807592292167 158419028199137711388438251)
      ·
        refine ⟨237628542298706567082657377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158419028199137711388438251 237628542298706567082657377)
        ·
          refine ⟨178221406724029925311993033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237628542298706567082657377 178221406724029925311993033)
          ·
            refine ⟨133666055043022443983994775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178221406724029925311993033 133666055043022443983994775)
            ·
              refine ⟨200499082564533665975992163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133666055043022443983994775 200499082564533665975992163)
              ·
                refine ⟨300748623846800498963988245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200499082564533665975992163 300748623846800498963988245)
                ·
                  refine ⟨14097591742818773388936949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 300748623846800498963988245 14097591742818773388936949)
                  ·
                    refine ⟨1321649225889260005212839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14097591742818773388936949 1321649225889260005212839)
                    ·
                      rfl

theorem cell23_7721708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_7721708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721708 prefixEnd_7721708 := by exact prefixLift 7721708
  have htrace : WordTrace (prefixWord ++ tailWord_7721708) baseStart_7721708 baseEnd_7721708 := by
    simpa [prefixWord, tailWord_7721708, baseEnd_7721708] using wordTrace_append hprefix tailTrace_7721708
  have hstable : (prefixWord ++ tailWord_7721708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721708).length < 2 ^ (prefixWord ++ tailWord_7721708).sum := by decide
  have hdescent : baseEnd_7721708 < baseStart_7721708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721725 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_7721725 : Nat := 118140960795 + 7721725 * 2 ^ 59
def prefixEnd_7721725 : Nat := 4983230072969 + 3 ^ 40 * 7721725 * 2
def baseEnd_7721725 : Nat := 1321652135612968816375313

theorem tailTrace_7721725 : CollatzResearch.WordTrace tailWord_7721725 prefixEnd_7721725 1321652135612968816375313 := by
  unfold tailWord_7721725
  simp only [CollatzResearch.WordTrace]
  refine ⟨281634447950516565482814629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187756298633677710321876419 281634447950516565482814629)
  ·
    refine ⟨52806458990721856028027743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281634447950516565482814629 52806458990721856028027743)
    ·
      refine ⟨79209688486082784042041615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52806458990721856028027743 79209688486082784042041615)
      ·
        refine ⟨118814532729124176063062423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79209688486082784042041615 118814532729124176063062423)
        ·
          refine ⟨178221799093686264094593635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118814532729124176063062423 178221799093686264094593635)
          ·
            refine ⟨267332698640529396141890453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178221799093686264094593635 267332698640529396141890453)
            ·
              refine ⟨12531220248774815444151115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 267332698640529396141890453 12531220248774815444151115)
              ·
                refine ⟨18796830373162223166226673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12531220248774815444151115 18796830373162223166226673)
                ·
                  refine ⟨14097622779871667374670005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18796830373162223166226673 14097622779871667374670005)
                  ·
                    refine ⟨1321652135612968816375313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14097622779871667374670005 1321652135612968816375313)
                    ·
                      rfl

theorem cell23_7721725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_7721725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721725 prefixEnd_7721725 := by exact prefixLift 7721725
  have htrace : WordTrace (prefixWord ++ tailWord_7721725) baseStart_7721725 baseEnd_7721725 := by
    simpa [prefixWord, tailWord_7721725, baseEnd_7721725] using wordTrace_append hprefix tailTrace_7721725
  have hstable : (prefixWord ++ tailWord_7721725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721725).length < 2 ^ (prefixWord ++ tailWord_7721725).sum := by decide
  have hdescent : baseEnd_7721725 < baseStart_7721725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721735 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7721735 : Nat := 118140960795 + 7721735 * 2 ^ 59
def prefixEnd_7721735 : Nat := 4983230072969 + 3 ^ 40 * 7721735 * 2
def baseEnd_7721735 : Nat := 3964961541645451410000893

theorem tailTrace_7721735 : CollatzResearch.WordTrace tailWord_7721735 prefixEnd_7721735 3964961541645451410000893 := by
  unfold tailWord_7721735
  simp only [CollatzResearch.WordTrace]
  refine ⟨281634812680480337190678659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187756541786986891460452439 281634812680480337190678659)
  ·
    refine ⟨422452219020720505786017989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281634812680480337190678659 422452219020720505786017989)
    ·
      refine ⟨79209791066385094834878373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422452219020720505786017989 79209791066385094834878373)
      ·
        refine ⟨14851835824947205281539695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79209791066385094834878373 14851835824947205281539695)
        ·
          refine ⟨22277753737420807922309543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14851835824947205281539695 22277753737420807922309543)
          ·
            refine ⟨33416630606131211883464315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22277753737420807922309543 33416630606131211883464315)
            ·
              refine ⟨50124945909196817825196473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33416630606131211883464315 50124945909196817825196473)
              ·
                refine ⟨37593709431897613368897355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50124945909196817825196473 37593709431897613368897355)
                ·
                  refine ⟨56390564147846420053346033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37593709431897613368897355 56390564147846420053346033)
                  ·
                    refine ⟨42292923110884815040009525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56390564147846420053346033 42292923110884815040009525)
                    ·
                      refine ⟨3964961541645451410000893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42292923110884815040009525 3964961541645451410000893)
                      ·
                        rfl

theorem cell23_7721735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7721735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721735 prefixEnd_7721735 := by exact prefixLift 7721735
  have htrace : WordTrace (prefixWord ++ tailWord_7721735) baseStart_7721735 baseEnd_7721735 := by
    simpa [prefixWord, tailWord_7721735, baseEnd_7721735] using wordTrace_append hprefix tailTrace_7721735
  have hstable : (prefixWord ++ tailWord_7721735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721735).length < 2 ^ (prefixWord ++ tailWord_7721735).sum := by decide
  have hdescent : baseEnd_7721735 < baseStart_7721735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721745 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_7721745 : Nat := 118140960795 + 7721745 * 2 ^ 59
def prefixEnd_7721745 : Nat := 4983230072969 + 3 ^ 40 * 7721745 * 2
def baseEnd_7721745 : Nat := 3964966676451996370875847

theorem tailTrace_7721745 : CollatzResearch.WordTrace tailWord_7721745 prefixEnd_7721745 3964966676451996370875847 := by
  unfold tailWord_7721745
  simp only [CollatzResearch.WordTrace]
  refine ⟨281635177410444108898542689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187756784940296072599028459 281635177410444108898542689)
  ·
    refine ⟨211226383057833081673907017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281635177410444108898542689 211226383057833081673907017)
    ·
      refine ⟨158419787293374811255430263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211226383057833081673907017 158419787293374811255430263)
      ·
        refine ⟨237629680940062216883145395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158419787293374811255430263 237629680940062216883145395)
        ·
          refine ⟨356444521410093325324718093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237629680940062216883145395 356444521410093325324718093)
          ·
            refine ⟨133666695528784996996769285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356444521410093325324718093 133666695528784996996769285)
            ·
              refine ⟨25062505411647186936894241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133666695528784996996769285 25062505411647186936894241)
              ·
                refine ⟨18796879058735390202670681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25062505411647186936894241 18796879058735390202670681)
                ·
                  refine ⟨14097659294051542652003011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18796879058735390202670681 14097659294051542652003011)
                  ·
                    refine ⟨21146488941077313978004517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14097659294051542652003011 21146488941077313978004517)
                    ·
                      refine ⟨3964966676451996370875847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21146488941077313978004517 3964966676451996370875847)
                      ·
                        rfl

theorem cell23_7721745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_7721745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721745 prefixEnd_7721745 := by exact prefixLift 7721745
  have htrace : WordTrace (prefixWord ++ tailWord_7721745) baseStart_7721745 baseEnd_7721745 := by
    simpa [prefixWord, tailWord_7721745, baseEnd_7721745] using wordTrace_append hprefix tailTrace_7721745
  have hstable : (prefixWord ++ tailWord_7721745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721745).length < 2 ^ (prefixWord ++ tailWord_7721745).sum := by decide
  have hdescent : baseEnd_7721745 < baseStart_7721745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721762 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_7721762 : Nat := 118140960795 + 7721762 * 2 ^ 59
def prefixEnd_7721762 : Nat := 4983230072969 + 3 ^ 40 * 7721762 * 2
def baseEnd_7721762 : Nat := 3964975405623122804363269

theorem tailTrace_7721762 : CollatzResearch.WordTrace tailWord_7721762 prefixEnd_7721762 3964975405623122804363269 := by
  unfold tailWord_7721762
  simp only [CollatzResearch.WordTrace]
  refine ⟨70408949362845630200477885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187757198300921680534607693 70408949362845630200477885)
  ·
    refine ⟨26403356011067111325179207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70408949362845630200477885 26403356011067111325179207)
    ·
      refine ⟨39605034016600666987768811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26403356011067111325179207 39605034016600666987768811)
      ·
        refine ⟨59407551024901000481653217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39605034016600666987768811 59407551024901000481653217)
        ·
          refine ⟨44555663268675750361239913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59407551024901000481653217 44555663268675750361239913)
          ·
            refine ⟨33416747451506812770929935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44555663268675750361239913 33416747451506812770929935)
            ·
              refine ⟨50125121177260219156394903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33416747451506812770929935 50125121177260219156394903)
              ·
                refine ⟨75187681765890328734592355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50125121177260219156394903 75187681765890328734592355)
                ·
                  refine ⟨112781522648835493101888533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75187681765890328734592355 112781522648835493101888533)
                  ·
                    refine ⟨5286633874164163739151025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112781522648835493101888533 5286633874164163739151025)
                    ·
                      refine ⟨3964975405623122804363269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5286633874164163739151025 3964975405623122804363269)
                      ·
                        rfl

theorem cell23_7721762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_7721762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721762 prefixEnd_7721762 := by exact prefixLift 7721762
  have htrace : WordTrace (prefixWord ++ tailWord_7721762) baseStart_7721762 baseEnd_7721762 := by
    simpa [prefixWord, tailWord_7721762, baseEnd_7721762] using wordTrace_append hprefix tailTrace_7721762
  have hstable : (prefixWord ++ tailWord_7721762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721762).length < 2 ^ (prefixWord ++ tailWord_7721762).sum := by decide
  have hdescent : baseEnd_7721762 < baseStart_7721762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721765 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 1, 4, 3]
def baseStart_7721765 : Nat := 118140960795 + 7721765 * 2 ^ 59
def prefixEnd_7721765 : Nat := 4983230072969 + 3 ^ 40 * 7721765 * 2
def baseEnd_7721765 : Nat := 3964976946065086292625755

theorem tailTrace_7721765 : CollatzResearch.WordTrace tailWord_7721765 prefixEnd_7721765 3964976946065086292625755 := by
  unfold tailWord_7721765
  simp only [CollatzResearch.WordTrace]
  refine ⟨281635906870371652314270749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187757271246914434876180499 281635906870371652314270749)
  ·
    refine ⟨105613465076389369617851531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281635906870371652314270749 105613465076389369617851531)
    ·
      refine ⟨158420197614584054426777297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105613465076389369617851531 158420197614584054426777297)
      ·
        refine ⟨118815148210938040820082973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158420197614584054426777297 118815148210938040820082973)
        ·
          refine ⟨44555680579101765307531115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118815148210938040820082973 44555680579101765307531115)
          ·
            refine ⟨66833520868652647961296673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44555680579101765307531115 66833520868652647961296673)
            ·
              refine ⟨50125140651489485970972505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66833520868652647961296673 50125140651489485970972505)
              ·
                refine ⟨37593855488617114478229379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50125140651489485970972505 37593855488617114478229379)
                ·
                  refine ⟨56390783232925671717344069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37593855488617114478229379 56390783232925671717344069)
                  ·
                    refine ⟨10573271856173563447002013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56390783232925671717344069 10573271856173563447002013)
                    ·
                      refine ⟨3964976946065086292625755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10573271856173563447002013 3964976946065086292625755)
                      ·
                        rfl

theorem cell23_7721765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_7721765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721765 prefixEnd_7721765 := by exact prefixLift 7721765
  have htrace : WordTrace (prefixWord ++ tailWord_7721765) baseStart_7721765 baseEnd_7721765 := by
    simpa [prefixWord, tailWord_7721765, baseEnd_7721765] using wordTrace_append hprefix tailTrace_7721765
  have hstable : (prefixWord ++ tailWord_7721765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721765).length < 2 ^ (prefixWord ++ tailWord_7721765).sum := by decide
  have hdescent : baseEnd_7721765 < baseStart_7721765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721832 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 1, 5]
def baseStart_7721832 : Nat := 118140960795 + 7721832 * 2 ^ 59
def prefixEnd_7721832 : Nat := 4983230072969 + 3 ^ 40 * 7721832 * 2
def baseEnd_7721832 : Nat := 1321670449756312510162649

theorem tailTrace_7721832 : CollatzResearch.WordTrace tailWord_7721832 prefixEnd_7721832 1321670449756312510162649 := by
  unfold tailWord_7721832
  simp only [CollatzResearch.WordTrace]
  refine ⟨140819175280564461378479875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187758900374085948504639833 140819175280564461378479875)
  ·
    refine ⟨211228762920846692067719813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140819175280564461378479875 211228762920846692067719813)
    ·
      refine ⟨39605393047658754762697465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211228762920846692067719813 39605393047658754762697465)
      ·
        refine ⟨29704044785744066072023099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39605393047658754762697465 29704044785744066072023099)
        ·
          refine ⟨44556067178616099108034649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29704044785744066072023099 44556067178616099108034649)
          ·
            refine ⟨33417050383962074331025987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44556067178616099108034649 33417050383962074331025987)
            ·
              refine ⟨50125575575943111496538981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33417050383962074331025987 50125575575943111496538981)
              ·
                refine ⟨9398545420489333405601059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50125575575943111496538981 9398545420489333405601059)
                ·
                  refine ⟨14097818130734000108401589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9398545420489333405601059 14097818130734000108401589)
                  ·
                    refine ⟨1321670449756312510162649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14097818130734000108401589 1321670449756312510162649)
                    ·
                      rfl

theorem cell23_7721832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_7721832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721832 prefixEnd_7721832 := by exact prefixLift 7721832
  have htrace : WordTrace (prefixWord ++ tailWord_7721832) baseStart_7721832 baseEnd_7721832 := by
    simpa [prefixWord, tailWord_7721832, baseEnd_7721832] using wordTrace_append hprefix tailTrace_7721832
  have hstable : (prefixWord ++ tailWord_7721832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721832).length < 2 ^ (prefixWord ++ tailWord_7721832).sum := by decide
  have hdescent : baseEnd_7721832 < baseStart_7721832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721835 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 4]
def baseStart_7721835 : Nat := 118140960795 + 7721835 * 2 ^ 59
def prefixEnd_7721835 : Nat := 4983230072969 + 3 ^ 40 * 7721835 * 2
def baseEnd_7721835 : Nat := 3965012889710901018750433

theorem tailTrace_7721835 : CollatzResearch.WordTrace tailWord_7721835 prefixEnd_7721835 3965012889710901018750433 := by
  unfold tailWord_7721835
  simp only [CollatzResearch.WordTrace]
  refine ⟨281638459980118054269318959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187758973320078702846212639 281638459980118054269318959)
  ·
    refine ⟨422457689970177081403978439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281638459980118054269318959 422457689970177081403978439)
    ·
      refine ⟨633686534955265622105967659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422457689970177081403978439 633686534955265622105967659)
      ·
        refine ⟨950529802432898433158951489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633686534955265622105967659 950529802432898433158951489)
        ·
          refine ⟨712897351824673824869213617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950529802432898433158951489 712897351824673824869213617)
          ·
            refine ⟨534673013868505368651910213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 712897351824673824869213617 534673013868505368651910213)
            ·
              refine ⟨100251190100344756622233165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 534673013868505368651910213 100251190100344756622233165)
              ·
                refine ⟨37594196287629283733337437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100251190100344756622233165 37594196287629283733337437)
                ·
                  refine ⟨14097823607860981400001539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37594196287629283733337437 14097823607860981400001539)
                  ·
                    refine ⟨21146735411791472100002309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14097823607860981400001539 21146735411791472100002309)
                    ·
                      refine ⟨3965012889710901018750433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21146735411791472100002309 3965012889710901018750433)
                      ·
                        rfl

theorem cell23_7721835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 4].length) (baseStart_7721835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721835 prefixEnd_7721835 := by exact prefixLift 7721835
  have htrace : WordTrace (prefixWord ++ tailWord_7721835) baseStart_7721835 baseEnd_7721835 := by
    simpa [prefixWord, tailWord_7721835, baseEnd_7721835] using wordTrace_append hprefix tailTrace_7721835
  have hstable : (prefixWord ++ tailWord_7721835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721835).length < 2 ^ (prefixWord ++ tailWord_7721835).sum := by decide
  have hdescent : baseEnd_7721835 < baseStart_7721835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721855 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 5]
def baseStart_7721855 : Nat := 118140960795 + 7721855 * 2 ^ 59
def prefixEnd_7721855 : Nat := 4983230072969 + 3 ^ 40 * 7721855 * 2
def baseEnd_7721855 : Nat := 3965023159323990940500341

theorem tailTrace_7721855 : CollatzResearch.WordTrace tailWord_7721855 prefixEnd_7721855 3965023159323990940500341 := by
  unfold tailWord_7721855
  simp only [CollatzResearch.WordTrace]
  refine ⟨281639189440045597685047019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187759459626697065123364679 281639189440045597685047019)
  ·
    refine ⟨422458784160068396527570529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281639189440045597685047019 422458784160068396527570529)
    ·
      refine ⟨316844088120051297395677897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422458784160068396527570529 316844088120051297395677897)
      ·
        refine ⟨237633066090038473046758423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316844088120051297395677897 237633066090038473046758423)
        ·
          refine ⟨356449599135057709570137635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237633066090038473046758423 356449599135057709570137635)
          ·
            refine ⟨534674398702586564355206453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356449599135057709570137635 534674398702586564355206453)
            ·
              refine ⟨50125724878367490408300605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 534674398702586564355206453 50125724878367490408300605)
              ·
                refine ⟨18797146829387808903112727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50125724878367490408300605 18797146829387808903112727)
                ·
                  refine ⟨28195720244081713354669091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18797146829387808903112727 28195720244081713354669091)
                  ·
                    refine ⟨42293580366122570032003637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28195720244081713354669091 42293580366122570032003637)
                    ·
                      refine ⟨3965023159323990940500341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42293580366122570032003637 3965023159323990940500341)
                      ·
                        rfl

theorem cell23_7721855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_7721855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721855 prefixEnd_7721855 := by exact prefixLift 7721855
  have htrace : WordTrace (prefixWord ++ tailWord_7721855) baseStart_7721855 baseEnd_7721855 := by
    simpa [prefixWord, tailWord_7721855, baseEnd_7721855] using wordTrace_append hprefix tailTrace_7721855
  have hstable : (prefixWord ++ tailWord_7721855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721855).length < 2 ^ (prefixWord ++ tailWord_7721855).sum := by decide
  have hdescent : baseEnd_7721855 < baseStart_7721855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721863 : List Nat := [1, 1, 4, 2, 3, 2, 3, 2, 1, 1, 3]
def baseStart_7721863 : Nat := 118140960795 + 7721863 * 2 ^ 59
def prefixEnd_7721863 : Nat := 4983230072969 + 3 ^ 40 * 7721863 * 2
def baseEnd_7721863 : Nat := 3965027267169226909200305

theorem tailTrace_7721863 : CollatzResearch.WordTrace tailWord_7721863 prefixEnd_7721863 3965027267169226909200305 := by
  unfold tailWord_7721863
  simp only [CollatzResearch.WordTrace]
  refine ⟨281639481224016615051338243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187759654149344410034225495 281639481224016615051338243)
  ·
    refine ⟨422459221836024922577007365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281639481224016615051338243 422459221836024922577007365)
    ·
      refine ⟨79211104094254672983188881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422459221836024922577007365 79211104094254672983188881)
      ·
        refine ⟨59408328070691004737391661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79211104094254672983188881 59408328070691004737391661)
        ·
          refine ⟨22278123026509126776521873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59408328070691004737391661 22278123026509126776521873)
          ·
            refine ⟨16708592269881845082391405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22278123026509126776521873 16708592269881845082391405)
            ·
              refine ⟨6265722101205691905896777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16708592269881845082391405 6265722101205691905896777)
              ·
                refine ⟨4699291575904268929422583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6265722101205691905896777 4699291575904268929422583)
                ·
                  refine ⟨7048937363856403394133875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4699291575904268929422583 7048937363856403394133875)
                  ·
                    refine ⟨10573406045784605091200813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7048937363856403394133875 10573406045784605091200813)
                    ·
                      refine ⟨3965027267169226909200305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10573406045784605091200813 3965027267169226909200305)
                      ·
                        rfl

theorem cell23_7721863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_7721863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721863 prefixEnd_7721863 := by exact prefixLift 7721863
  have htrace : WordTrace (prefixWord ++ tailWord_7721863) baseStart_7721863 baseEnd_7721863 := by
    simpa [prefixWord, tailWord_7721863, baseEnd_7721863] using wordTrace_append hprefix tailTrace_7721863
  have hstable : (prefixWord ++ tailWord_7721863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721863).length < 2 ^ (prefixWord ++ tailWord_7721863).sum := by decide
  have hdescent : baseEnd_7721863 < baseStart_7721863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721865 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 6]
def baseStart_7721865 : Nat := 118140960795 + 7721865 * 2 ^ 59
def prefixEnd_7721865 : Nat := 4983230072969 + 3 ^ 40 * 7721865 * 2
def baseEnd_7721865 : Nat := 3965028294130535901375295

theorem tailTrace_7721865 : CollatzResearch.WordTrace tailWord_7721865 prefixEnd_7721865 3965028294130535901375295 := by
  unfold tailWord_7721865
  simp only [CollatzResearch.WordTrace]
  refine ⟨281639554170009369392911049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187759702780006246261940699 281639554170009369392911049)
  ·
    refine ⟨211229665627507027044683287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281639554170009369392911049 211229665627507027044683287)
    ·
      refine ⟨316844498441260540567024931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211229665627507027044683287 316844498441260540567024931)
      ·
        refine ⟨475266747661890810850537397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316844498441260540567024931 475266747661890810850537397)
        ·
          refine ⟨44556257593302263517237881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 475266747661890810850537397 44556257593302263517237881)
          ·
            refine ⟨33417193194976697637928411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44556257593302263517237881 33417193194976697637928411)
            ·
              refine ⟨50125789792465046456892617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33417193194976697637928411 50125789792465046456892617)
              ·
                refine ⟨37594342344348784842669463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50125789792465046456892617 37594342344348784842669463)
                ·
                  refine ⟨56391513516523177264004195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37594342344348784842669463 56391513516523177264004195)
                  ·
                    refine ⟨84587270274784765896006293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56391513516523177264004195 84587270274784765896006293)
                    ·
                      refine ⟨3965028294130535901375295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84587270274784765896006293 3965028294130535901375295)
                      ·
                        rfl

theorem cell23_7721865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_7721865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721865 prefixEnd_7721865 := by exact prefixLift 7721865
  have htrace : WordTrace (prefixWord ++ tailWord_7721865) baseStart_7721865 baseEnd_7721865 := by
    simpa [prefixWord, tailWord_7721865, baseEnd_7721865] using wordTrace_append hprefix tailTrace_7721865
  have hstable : (prefixWord ++ tailWord_7721865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721865).length < 2 ^ (prefixWord ++ tailWord_7721865).sum := by decide
  have hdescent : baseEnd_7721865 < baseStart_7721865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721889 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7721889 : Nat := 118140960795 + 7721889 * 2 ^ 59
def prefixEnd_7721889 : Nat := 4983230072969 + 3 ^ 40 * 7721889 * 2
def baseEnd_7721889 : Nat := 3965040617666243807475185

theorem tailTrace_7721889 : CollatzResearch.WordTrace tailWord_7721889 prefixEnd_7721889 3965040617666243807475185 := by
  unfold tailWord_7721889
  simp only [CollatzResearch.WordTrace]
  refine ⟨281640429521922421491784721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187760286347948280994523147 281640429521922421491784721)
  ·
    refine ⟨211230322141441816118838541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281640429521922421491784721 211230322141441816118838541)
    ·
      refine ⟨79211370803040681044564453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211230322141441816118838541 79211370803040681044564453)
      ·
        refine ⟨14852132025570127695855835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79211370803040681044564453 14852132025570127695855835)
        ·
          refine ⟨22278198038355191543783753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14852132025570127695855835 22278198038355191543783753)
          ·
            refine ⟨16708648528766393657837815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22278198038355191543783753 16708648528766393657837815)
            ·
              refine ⟨25062972793149590486756723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16708648528766393657837815 25062972793149590486756723)
              ·
                refine ⟨37594459189724385730135085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25062972793149590486756723 37594459189724385730135085)
                ·
                  refine ⟨14097922196146644648800657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37594459189724385730135085 14097922196146644648800657)
                  ·
                    refine ⟨10573441647109983486600493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14097922196146644648800657 10573441647109983486600493)
                    ·
                      refine ⟨3965040617666243807475185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10573441647109983486600493 3965040617666243807475185)
                      ·
                        rfl

theorem cell23_7721889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7721889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721889 prefixEnd_7721889 := by exact prefixLift 7721889
  have htrace : WordTrace (prefixWord ++ tailWord_7721889) baseStart_7721889 baseEnd_7721889 := by
    simpa [prefixWord, tailWord_7721889, baseEnd_7721889] using wordTrace_append hprefix tailTrace_7721889
  have hstable : (prefixWord ++ tailWord_7721889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721889).length < 2 ^ (prefixWord ++ tailWord_7721889).sum := by decide
  have hdescent : baseEnd_7721889 < baseStart_7721889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721920 : List Nat := [2, 1, 1, 2, 3, 5, 2, 2, 1, 2, 2]
def baseStart_7721920 : Nat := 118140960795 + 7721920 * 2 ^ 59
def prefixEnd_7721920 : Nat := 4983230072969 + 3 ^ 40 * 7721920 * 2
def baseEnd_7721920 : Nat := 3965056535566533186187543

theorem tailTrace_7721920 : CollatzResearch.WordTrace tailWord_7721920 prefixEnd_7721920 3965056535566533186187543 := by
  unfold tailWord_7721920
  simp only [CollatzResearch.WordTrace]
  refine ⟨140820780092405056893081607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187761040123206742524108809 140820780092405056893081607)
  ·
    refine ⟨211231170138607585339622411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140820780092405056893081607 211231170138607585339622411)
    ·
      refine ⟨316846755207911378009433617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211231170138607585339622411 316846755207911378009433617)
      ·
        refine ⟨237635066405933533507075213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316846755207911378009433617 237635066405933533507075213)
        ·
          refine ⟨89113149902225075065153205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237635066405933533507075213 89113149902225075065153205)
          ·
            refine ⟨8354357803333600787358113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89113149902225075065153205 8354357803333600787358113)
            ·
              refine ⟨6265768352500200590518585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8354357803333600787358113 6265768352500200590518585)
              ·
                refine ⟨4699326264375150442888939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6265768352500200590518585 4699326264375150442888939)
                ·
                  refine ⟨7048989396562725664333409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4699326264375150442888939 7048989396562725664333409)
                  ·
                    refine ⟨5286742047422044248250057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7048989396562725664333409 5286742047422044248250057)
                    ·
                      refine ⟨3965056535566533186187543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5286742047422044248250057 3965056535566533186187543)
                      ·
                        rfl

theorem cell23_7721920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 1, 2, 2].length) (baseStart_7721920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721920 prefixEnd_7721920 := by exact prefixLift 7721920
  have htrace : WordTrace (prefixWord ++ tailWord_7721920) baseStart_7721920 baseEnd_7721920 := by
    simpa [prefixWord, tailWord_7721920, baseEnd_7721920] using wordTrace_append hprefix tailTrace_7721920
  have hstable : (prefixWord ++ tailWord_7721920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721920).length < 2 ^ (prefixWord ++ tailWord_7721920).sum := by decide
  have hdescent : baseEnd_7721920 < baseStart_7721920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721935 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 1, 8]
def baseStart_7721935 : Nat := 118140960795 + 7721935 * 2 ^ 59
def prefixEnd_7721935 : Nat := 4983230072969 + 3 ^ 40 * 7721935 * 2
def baseEnd_7721935 : Nat := 1321688079258783542499991

theorem tailTrace_7721935 : CollatzResearch.WordTrace tailWord_7721935 prefixEnd_7721935 1321688079258783542499991 := by
  unfold tailWord_7721935
  simp only [CollatzResearch.WordTrace]
  refine ⟨281642107279755771347959259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187761404853170514231972839 281642107279755771347959259)
  ·
    refine ⟨422463160919633657021938889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281642107279755771347959259 422463160919633657021938889)
    ·
      refine ⟨316847370689725242766454167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422463160919633657021938889 316847370689725242766454167)
      ·
        refine ⟨475271056034587864149681251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316847370689725242766454167 475271056034587864149681251)
        ·
          refine ⟨712906584051881796224521877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475271056034587864149681251 712906584051881796224521877)
          ·
            refine ⟨33417496127431959198024463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 712906584051881796224521877 33417496127431959198024463)
            ·
              refine ⟨50126244191147938797036695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33417496127431959198024463 50126244191147938797036695)
              ·
                refine ⟨75189366286721908195555043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50126244191147938797036695 75189366286721908195555043)
                ·
                  refine ⟨112784049430082862293332565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75189366286721908195555043 112784049430082862293332565)
                  ·
                    refine ⟨1321688079258783542499991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112784049430082862293332565 1321688079258783542499991)
                    ·
                      rfl

theorem cell23_7721935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_7721935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721935 prefixEnd_7721935 := by exact prefixLift 7721935
  have htrace : WordTrace (prefixWord ++ tailWord_7721935) baseStart_7721935 baseEnd_7721935 := by
    simpa [prefixWord, tailWord_7721935, baseEnd_7721935] using wordTrace_append hprefix tailTrace_7721935
  have hstable : (prefixWord ++ tailWord_7721935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721935).length < 2 ^ (prefixWord ++ tailWord_7721935).sum := by decide
  have hdescent : baseEnd_7721935 < baseStart_7721935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7721970 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7721970 : Nat := 118140960795 + 7721970 * 2 ^ 59
def prefixEnd_7721970 : Nat := 4983230072969 + 3 ^ 40 * 7721970 * 2
def baseEnd_7721970 : Nat := 3965082209599257990562313

theorem tailTrace_7721970 : CollatzResearch.WordTrace tailWord_7721970 prefixEnd_7721970 3965082209599257990562313 := by
  unfold tailWord_7721970
  simp only [CollatzResearch.WordTrace]
  refine ⟨70410845958657243081370841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187762255889752648216988909 70410845958657243081370841)
  ·
    refine ⟨52808134468992932311028131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70410845958657243081370841 52808134468992932311028131)
    ·
      refine ⟨79212201703489398466542197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52808134468992932311028131 79212201703489398466542197)
      ·
        refine ⟨7426143909702131106238331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79212201703489398466542197 7426143909702131106238331)
        ·
          refine ⟨11139215864553196659357497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426143909702131106238331 11139215864553196659357497)
          ·
            refine ⟨8354411898414897494518123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11139215864553196659357497 8354411898414897494518123)
            ·
              refine ⟨12531617847622346241777185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354411898414897494518123 12531617847622346241777185)
              ·
                refine ⟨9398713385716759681332889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12531617847622346241777185 9398713385716759681332889)
                ·
                  refine ⟨7049035039287569760999667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9398713385716759681332889 7049035039287569760999667)
                  ·
                    refine ⟨10573552558931354641499501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7049035039287569760999667 10573552558931354641499501)
                    ·
                      refine ⟨3965082209599257990562313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10573552558931354641499501 3965082209599257990562313)
                      ·
                        rfl

theorem cell23_7721970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7721970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7721970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7721970 prefixEnd_7721970 := by exact prefixLift 7721970
  have htrace : WordTrace (prefixWord ++ tailWord_7721970) baseStart_7721970 baseEnd_7721970 := by
    simpa [prefixWord, tailWord_7721970, baseEnd_7721970] using wordTrace_append hprefix tailTrace_7721970
  have hstable : (prefixWord ++ tailWord_7721970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7721970).length < 2 ^ (prefixWord ++ tailWord_7721970).sum := by decide
  have hdescent : baseEnd_7721970 < baseStart_7721970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7721970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722066 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_7722066 : Nat := 118140960795 + 7722066 * 2 ^ 59
def prefixEnd_7722066 : Nat := 4983230072969 + 3 ^ 40 * 7722066 * 2
def baseEnd_7722066 : Nat := 3965131503742089614961871

theorem tailTrace_7722066 : CollatzResearch.WordTrace tailWord_7722066 prefixEnd_7722066 3965131503742089614961871 := by
  unfold tailWord_7722066
  simp only [CollatzResearch.WordTrace]
  refine ⟨70411721310570295180244513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187764590161520787147318701 70411721310570295180244513)
  ·
    refine ⟨52808790982927721385183385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70411721310570295180244513 52808790982927721385183385)
    ·
      refine ⟨39606593237195791038887539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52808790982927721385183385 39606593237195791038887539)
      ·
        refine ⟨59409889855793686558331309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39606593237195791038887539 59409889855793686558331309)
        ·
          refine ⟨22278708695922632459374241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59409889855793686558331309 22278708695922632459374241)
          ·
            refine ⟨16709031521941974344530681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22278708695922632459374241 16709031521941974344530681)
            ·
              refine ⟨12531773641456480758398011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16709031521941974344530681 12531773641456480758398011)
              ·
                refine ⟨18797660462184721137597017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12531773641456480758398011 18797660462184721137597017)
                ·
                  refine ⟨14098245346638540853197763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18797660462184721137597017 14098245346638540853197763)
                  ·
                    refine ⟨21147368019957811279796645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14098245346638540853197763 21147368019957811279796645)
                    ·
                      refine ⟨3965131503742089614961871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21147368019957811279796645 3965131503742089614961871)
                      ·
                        rfl

theorem cell23_7722066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_7722066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722066 prefixEnd_7722066 := by exact prefixLift 7722066
  have htrace : WordTrace (prefixWord ++ tailWord_7722066) baseStart_7722066 baseEnd_7722066 := by
    simpa [prefixWord, tailWord_7722066, baseEnd_7722066] using wordTrace_append hprefix tailTrace_7722066
  have hstable : (prefixWord ++ tailWord_7722066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722066).length < 2 ^ (prefixWord ++ tailWord_7722066).sum := by decide
  have hdescent : baseEnd_7722066 < baseStart_7722066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722089 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 6]
def baseStart_7722089 : Nat := 118140960795 + 7722089 * 2 ^ 59
def prefixEnd_7722089 : Nat := 4983230072969 + 3 ^ 40 * 7722089 * 2
def baseEnd_7722089 : Nat := 440571479310793669441585

theorem tailTrace_7722089 : CollatzResearch.WordTrace tailWord_7722089 prefixEnd_7722089 440571479310793669441585 := by
  unfold tailWord_7722089
  simp only [CollatzResearch.WordTrace]
  refine ⟨281647724121197855649065321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187765149414131903766043547 281647724121197855649065321)
  ·
    refine ⟨211235793090898391736798991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281647724121197855649065321 211235793090898391736798991)
    ·
      refine ⟨316853689636347587605198487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211235793090898391736798991 316853689636347587605198487)
      ·
        refine ⟨475280534454521381407797731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316853689636347587605198487 475280534454521381407797731)
        ·
          refine ⟨712920801681782072111696597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475280534454521381407797731 712920801681782072111696597)
          ·
            refine ⟨16709081289416767315117889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 712920801681782072111696597 16709081289416767315117889)
            ·
              refine ⟨12531810967062575486338417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16709081289416767315117889 12531810967062575486338417)
              ·
                refine ⟨9398858225296931614753813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12531810967062575486338417 9398858225296931614753813)
                ·
                  refine ⟨440571479310793669441585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9398858225296931614753813 440571479310793669441585)
                  ·
                    rfl

theorem cell23_7722089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 6].length) (baseStart_7722089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722089 prefixEnd_7722089 := by exact prefixLift 7722089
  have htrace : WordTrace (prefixWord ++ tailWord_7722089) baseStart_7722089 baseEnd_7722089 := by
    simpa [prefixWord, tailWord_7722089, baseEnd_7722089] using wordTrace_append hprefix tailTrace_7722089
  have hstable : (prefixWord ++ tailWord_7722089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722089).length < 2 ^ (prefixWord ++ tailWord_7722089).sum := by decide
  have hdescent : baseEnd_7722089 < baseStart_7722089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722092 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_7722092 : Nat := 118140960795 + 7722092 * 2 ^ 59
def prefixEnd_7722092 : Nat := 4983230072969 + 3 ^ 40 * 7722092 * 2
def baseEnd_7722092 : Nat := 3965144854239106513236751

theorem tailTrace_7722092 : CollatzResearch.WordTrace tailWord_7722092 prefixEnd_7722092 3965144854239106513236751 := by
  unfold tailWord_7722092
  simp only [CollatzResearch.WordTrace]
  refine ⟨140823916770093493580712265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187765222360124658107616353 140823916770093493580712265)
  ·
    refine ⟨105617937577570120185534199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140823916770093493580712265 105617937577570120185534199)
    ·
      refine ⟨158426906366355180278301299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105617937577570120185534199 158426906366355180278301299)
      ·
        refine ⟨237640359549532770417451949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158426906366355180278301299 237640359549532770417451949)
        ·
          refine ⟨89115134831074788906544481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237640359549532770417451949 89115134831074788906544481)
          ·
            refine ⟨66836351123306091679908361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89115134831074788906544481 66836351123306091679908361)
            ·
              refine ⟨50127263342479568759931271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66836351123306091679908361 50127263342479568759931271)
              ·
                refine ⟨75190895013719353139896907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50127263342479568759931271 75190895013719353139896907)
                ·
                  refine ⟨112786342520579029709845361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75190895013719353139896907 112786342520579029709845361)
                  ·
                    refine ⟨84589756890434272282384021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112786342520579029709845361 84589756890434272282384021)
                    ·
                      refine ⟨3965144854239106513236751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84589756890434272282384021 3965144854239106513236751)
                      ·
                        rfl

theorem cell23_7722092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_7722092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722092 prefixEnd_7722092 := by exact prefixLift 7722092
  have htrace : WordTrace (prefixWord ++ tailWord_7722092) baseStart_7722092 baseEnd_7722092 := by
    simpa [prefixWord, tailWord_7722092, baseEnd_7722092] using wordTrace_append hprefix tailTrace_7722092
  have hstable : (prefixWord ++ tailWord_7722092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722092).length < 2 ^ (prefixWord ++ tailWord_7722092).sum := by decide
  have hdescent : baseEnd_7722092 < baseStart_7722092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722093 : List Nat := [1, 5, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_7722093 : Nat := 118140960795 + 7722093 * 2 ^ 59
def prefixEnd_7722093 : Nat := 4983230072969 + 3 ^ 40 * 7722093 * 2
def baseEnd_7722093 : Nat := 1321715122573253669774749

theorem tailTrace_7722093 : CollatzResearch.WordTrace tailWord_7722093 prefixEnd_7722093 1321715122573253669774749 := by
  unfold tailWord_7722093
  simp only [CollatzResearch.WordTrace]
  refine ⟨281647870013183364332210933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187765246675455576221473955 281647870013183364332210933)
  ·
    refine ⟨26404487813735940406144775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281647870013183364332210933 26404487813735940406144775)
    ·
      refine ⟨39606731720603910609217163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26404487813735940406144775 39606731720603910609217163)
      ·
        refine ⟨59410097580905865913825745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39606731720603910609217163 59410097580905865913825745)
        ·
          refine ⟨44557573185679399435369309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59410097580905865913825745 44557573185679399435369309)
          ·
            refine ⟨16709089944629774788263491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44557573185679399435369309 16709089944629774788263491)
            ·
              refine ⟨25063634916944662182395237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16709089944629774788263491 25063634916944662182395237)
              ·
                refine ⟨4699431546927124159199107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25063634916944662182395237 4699431546927124159199107)
                ·
                  refine ⟨7049147320390686238798661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4699431546927124159199107 7049147320390686238798661)
                  ·
                    refine ⟨1321715122573253669774749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7049147320390686238798661 1321715122573253669774749)
                    ·
                      rfl

theorem cell23_7722093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_7722093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722093 prefixEnd_7722093 := by exact prefixLift 7722093
  have htrace : WordTrace (prefixWord ++ tailWord_7722093) baseStart_7722093 baseEnd_7722093 := by
    simpa [prefixWord, tailWord_7722093, baseEnd_7722093] using wordTrace_append hprefix tailTrace_7722093
  have hstable : (prefixWord ++ tailWord_7722093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722093).length < 2 ^ (prefixWord ++ tailWord_7722093).sum := by decide
  have hdescent : baseEnd_7722093 < baseStart_7722093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722099 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 9, 1, 3]
def baseStart_7722099 : Nat := 118140960795 + 7722099 * 2 ^ 59
def prefixEnd_7722099 : Nat := 4983230072969 + 3 ^ 40 * 7722099 * 2
def baseEnd_7722099 : Nat := 3965148448603687985849219

theorem tailTrace_7722099 : CollatzResearch.WordTrace tailWord_7722099 prefixEnd_7722099 3965148448603687985849219 := by
  unfold tailWord_7722099
  simp only [CollatzResearch.WordTrace]
  refine ⟨281648088851161627356929351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187765392567441084904619567 281648088851161627356929351)
  ·
    refine ⟨422472133276742441035394027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281648088851161627356929351 422472133276742441035394027)
    ·
      refine ⟨633708199915113661553091041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422472133276742441035394027 633708199915113661553091041)
      ·
        refine ⟨475281149936335246164818281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633708199915113661553091041 475281149936335246164818281)
        ·
          refine ⟨356460862452251434623613711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475281149936335246164818281 356460862452251434623613711)
          ·
            refine ⟨534691293678377151935420567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356460862452251434623613711 534691293678377151935420567)
            ·
              refine ⟨802036940517565727903130851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534691293678377151935420567 802036940517565727903130851)
              ·
                refine ⟨1203055410776348591854696277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802036940517565727903130851 1203055410776348591854696277)
                ·
                  refine ⟨7049152797517667530398611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1203055410776348591854696277 7049152797517667530398611)
                  ·
                    refine ⟨10573729196276501295597917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7049152797517667530398611 10573729196276501295597917)
                    ·
                      refine ⟨3965148448603687985849219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10573729196276501295597917 3965148448603687985849219)
                      ·
                        rfl

theorem cell23_7722099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 1, 3].length) (baseStart_7722099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722099 prefixEnd_7722099 := by exact prefixLift 7722099
  have htrace : WordTrace (prefixWord ++ tailWord_7722099) baseStart_7722099 baseEnd_7722099 := by
    simpa [prefixWord, tailWord_7722099, baseEnd_7722099] using wordTrace_append hprefix tailTrace_7722099
  have hstable : (prefixWord ++ tailWord_7722099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722099).length < 2 ^ (prefixWord ++ tailWord_7722099).sum := by decide
  have hdescent : baseEnd_7722099 < baseStart_7722099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722116 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_7722116 : Nat := 118140960795 + 7722116 * 2 ^ 59
def prefixEnd_7722116 : Nat := 4983230072969 + 3 ^ 40 * 7722116 * 2
def baseEnd_7722116 : Nat := 3965157177774814419336641

theorem tailTrace_7722116 : CollatzResearch.WordTrace tailWord_7722116 prefixEnd_7722116 3965157177774814419336641 := by
  unfold tailWord_7722116
  simp only [CollatzResearch.WordTrace]
  refine ⟨140824354446050019630149101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187765805928066692840198801 140824354446050019630149101)
  ·
    refine ⟨52809132917268757361305913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140824354446050019630149101 52809132917268757361305913)
    ·
      refine ⟨39606849687951568020979435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52809132917268757361305913 39606849687951568020979435)
      ·
        refine ⟨59410274531927352031469153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39606849687951568020979435 59410274531927352031469153)
        ·
          refine ⟨44557705898945514023601865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59410274531927352031469153 44557705898945514023601865)
          ·
            refine ⟨33418279424209135517701399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44557705898945514023601865 33418279424209135517701399)
            ·
              refine ⟨50127419136313703276552099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33418279424209135517701399 50127419136313703276552099)
              ·
                refine ⟨75191128704470554914828149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50127419136313703276552099 75191128704470554914828149)
                ·
                  refine ⟨7049168316044114523265139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75191128704470554914828149 7049168316044114523265139)
                  ·
                    refine ⟨10573752474066171784897709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7049168316044114523265139 10573752474066171784897709)
                    ·
                      refine ⟨3965157177774814419336641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10573752474066171784897709 3965157177774814419336641)
                      ·
                        rfl

theorem cell23_7722116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_7722116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722116 prefixEnd_7722116 := by exact prefixLift 7722116
  have htrace : WordTrace (prefixWord ++ tailWord_7722116) baseStart_7722116 baseEnd_7722116 := by
    simpa [prefixWord, tailWord_7722116, baseEnd_7722116] using wordTrace_append hprefix tailTrace_7722116
  have hstable : (prefixWord ++ tailWord_7722116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722116).length < 2 ^ (prefixWord ++ tailWord_7722116).sum := by decide
  have hdescent : baseEnd_7722116 < baseStart_7722116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722119 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 1, 5]
def baseStart_7722119 : Nat := 118140960795 + 7722119 * 2 ^ 59
def prefixEnd_7722119 : Nat := 4983230072969 + 3 ^ 40 * 7722119 * 2
def baseEnd_7722119 : Nat := 1321719572738925969199709

theorem tailTrace_7722119 : CollatzResearch.WordTrace tailWord_7722119 prefixEnd_7722119 1321719572738925969199709 := by
  unfold tailWord_7722119
  simp only [CollatzResearch.WordTrace]
  refine ⟨281648818311089170772657411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187765878874059447181771607 281648818311089170772657411)
  ·
    refine ⟨422473227466633756158986117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281648818311089170772657411 422473227466633756158986117)
    ·
      refine ⟨79213730149993829279809897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422473227466633756158986117 79213730149993829279809897)
      ·
        refine ⟨59410297612495371959857423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79213730149993829279809897 59410297612495371959857423)
        ·
          refine ⟨89115446418743057939786135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59410297612495371959857423 89115446418743057939786135)
          ·
            refine ⟨133673169628114586909679203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89115446418743057939786135 133673169628114586909679203)
            ·
              refine ⟨200509754442171880364518805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133673169628114586909679203 200509754442171880364518805)
              ·
                refine ⟨9398894739476806892086819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 200509754442171880364518805 9398894739476806892086819)
                ·
                  refine ⟨14098342109215210338130229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9398894739476806892086819 14098342109215210338130229)
                  ·
                    refine ⟨1321719572738925969199709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14098342109215210338130229 1321719572738925969199709)
                    ·
                      rfl

theorem cell23_7722119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_7722119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722119 prefixEnd_7722119 := by exact prefixLift 7722119
  have htrace : WordTrace (prefixWord ++ tailWord_7722119) baseStart_7722119 baseEnd_7722119 := by
    simpa [prefixWord, tailWord_7722119, baseEnd_7722119] using wordTrace_append hprefix tailTrace_7722119
  have hstable : (prefixWord ++ tailWord_7722119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722119).length < 2 ^ (prefixWord ++ tailWord_7722119).sum := by decide
  have hdescent : baseEnd_7722119 < baseStart_7722119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722120 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7722120 : Nat := 118140960795 + 7722120 * 2 ^ 59
def prefixEnd_7722120 : Nat := 4983230072969 + 3 ^ 40 * 7722120 * 2
def baseEnd_7722120 : Nat := 3965159231697432403686623

theorem tailTrace_7722120 : CollatzResearch.WordTrace tailWord_7722120 prefixEnd_7722120 3965159231697432403686623 := by
  unfold tailWord_7722120
  simp only [CollatzResearch.WordTrace]
  refine ⟨140824427392042773971721907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187765903189390365295629209 140824427392042773971721907)
  ·
    refine ⟨211236641088064160957582861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140824427392042773971721907 211236641088064160957582861)
    ·
      refine ⟨79213740408024060359093573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211236641088064160957582861 79213740408024060359093573)
      ·
        refine ⟨14852576326504511317330045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79213740408024060359093573 14852576326504511317330045)
        ·
          refine ⟨5569716122439191743998767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14852576326504511317330045 5569716122439191743998767)
          ·
            refine ⟨8354574183658787615998151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569716122439191743998767 8354574183658787615998151)
            ·
              refine ⟨12531861275488181423997227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354574183658787615998151 12531861275488181423997227)
              ·
                refine ⟨18797791913232272135995841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12531861275488181423997227 18797791913232272135995841)
                ·
                  refine ⟨14098343934924204101996881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18797791913232272135995841 14098343934924204101996881)
                  ·
                    refine ⟨10573757951193153076497661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14098343934924204101996881 10573757951193153076497661)
                    ·
                      refine ⟨3965159231697432403686623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10573757951193153076497661 3965159231697432403686623)
                      ·
                        rfl

theorem cell23_7722120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7722120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722120 prefixEnd_7722120 := by exact prefixLift 7722120
  have htrace : WordTrace (prefixWord ++ tailWord_7722120) baseStart_7722120 baseEnd_7722120 := by
    simpa [prefixWord, tailWord_7722120, baseEnd_7722120] using wordTrace_append hprefix tailTrace_7722120
  have hstable : (prefixWord ++ tailWord_7722120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722120).length < 2 ^ (prefixWord ++ tailWord_7722120).sum := by decide
  have hdescent : baseEnd_7722120 < baseStart_7722120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722136 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 1, 5]
def baseStart_7722136 : Nat := 118140960795 + 7722136 * 2 ^ 59
def prefixEnd_7722136 : Nat := 4983230072969 + 3 ^ 40 * 7722136 * 2
def baseEnd_7722136 : Nat := 1321722482462634780362183

theorem tailTrace_7722136 : CollatzResearch.WordTrace tailWord_7722136 prefixEnd_7722136 1321722482462634780362183 := by
  unfold tailWord_7722136
  simp only [CollatzResearch.WordTrace]
  refine ⟨140824719176013791338013131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187766292234685055117350841 140824719176013791338013131)
  ·
    refine ⟨211237078764020687007019697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140824719176013791338013131 211237078764020687007019697)
    ·
      refine ⟨158427809073015515255264773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211237078764020687007019697 158427809073015515255264773)
      ·
        refine ⟨29705214201190409110362145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158427809073015515255264773 29705214201190409110362145)
        ·
          refine ⟨22278910650892806832771609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29705214201190409110362145 22278910650892806832771609)
          ·
            refine ⟨16709182988169605124578707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22278910650892806832771609 16709182988169605124578707)
            ·
              refine ⟨25063774482254407686868061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16709182988169605124578707 25063774482254407686868061)
              ·
                refine ⟨9398915430845402882575523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25063774482254407686868061 9398915430845402882575523)
                ·
                  refine ⟨14098373146268104323863285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9398915430845402882575523 14098373146268104323863285)
                  ·
                    refine ⟨1321722482462634780362183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14098373146268104323863285 1321722482462634780362183)
                    ·
                      rfl

theorem cell23_7722136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_7722136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722136 prefixEnd_7722136 := by exact prefixLift 7722136
  have htrace : WordTrace (prefixWord ++ tailWord_7722136) baseStart_7722136 baseEnd_7722136 := by
    simpa [prefixWord, tailWord_7722136, baseEnd_7722136] using wordTrace_append hprefix tailTrace_7722136
  have hstable : (prefixWord ++ tailWord_7722136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722136).length < 2 ^ (prefixWord ++ tailWord_7722136).sum := by decide
  have hdescent : baseEnd_7722136 < baseStart_7722136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722159 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 3]
def baseStart_7722159 : Nat := 118140960795 + 7722159 * 2 ^ 59
def prefixEnd_7722159 : Nat := 4983230072969 + 3 ^ 40 * 7722159 * 2
def baseEnd_7722159 : Nat := 3965179257442957751098943

theorem tailTrace_7722159 : CollatzResearch.WordTrace tailWord_7722159 prefixEnd_7722159 3965179257442957751098943 := by
  unfold tailWord_7722159
  simp only [CollatzResearch.WordTrace]
  refine ⟨281650277230944257604113531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187766851487296171736075687 281650277230944257604113531)
  ·
    refine ⟨422475415846416386406170297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281650277230944257604113531 422475415846416386406170297)
    ·
      refine ⟨316856561884812289804627723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422475415846416386406170297 316856561884812289804627723)
      ·
        refine ⟨475284842827218434706941585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316856561884812289804627723 475284842827218434706941585)
        ·
          refine ⟨356463632120413826030206189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475284842827218434706941585 356463632120413826030206189)
          ·
            refine ⟨133673862045155184761327321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356463632120413826030206189 133673862045155184761327321)
            ·
              refine ⟨100255396533866388570995491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133673862045155184761327321 100255396533866388570995491)
              ·
                refine ⟨150383094800799582856493237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100255396533866388570995491 150383094800799582856493237)
                ·
                  refine ⟨14098415137574960892796241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150383094800799582856493237 14098415137574960892796241)
                  ·
                    refine ⟨10573811353181220669597181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14098415137574960892796241 10573811353181220669597181)
                    ·
                      refine ⟨3965179257442957751098943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10573811353181220669597181 3965179257442957751098943)
                      ·
                        rfl

theorem cell23_7722159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 3].length) (baseStart_7722159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722159 prefixEnd_7722159 := by exact prefixLift 7722159
  have htrace : WordTrace (prefixWord ++ tailWord_7722159) baseStart_7722159 baseEnd_7722159 := by
    simpa [prefixWord, tailWord_7722159, baseEnd_7722159] using wordTrace_append hprefix tailTrace_7722159
  have hstable : (prefixWord ++ tailWord_7722159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722159).length < 2 ^ (prefixWord ++ tailWord_7722159).sum := by decide
  have hdescent : baseEnd_7722159 < baseStart_7722159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722169 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 6]
def baseStart_7722169 : Nat := 118140960795 + 7722169 * 2 ^ 59
def prefixEnd_7722169 : Nat := 4983230072969 + 3 ^ 40 * 7722169 * 2
def baseEnd_7722169 : Nat := 3965184392249502711973897

theorem tailTrace_7722169 : CollatzResearch.WordTrace tailWord_7722169 prefixEnd_7722169 3965184392249502711973897 := by
  unfold tailWord_7722169
  simp only [CollatzResearch.WordTrace]
  refine ⟨281650641960908029311977561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187767094640605352874651707 281650641960908029311977561)
  ·
    refine ⟨211237981470681021983983171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281650641960908029311977561 211237981470681021983983171)
    ·
      refine ⟨316856972206021532975974757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211237981470681021983983171 316856972206021532975974757)
      ·
        refine ⟨59410682288629037432995267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316856972206021532975974757 59410682288629037432995267)
        ·
          refine ⟨89116023432943556149492901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59410682288629037432995267 89116023432943556149492901)
          ·
            refine ⟨16709254393676916778029919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89116023432943556149492901 16709254393676916778029919)
            ·
              refine ⟨25063881590515375167044879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16709254393676916778029919 25063881590515375167044879)
              ·
                refine ⟨37595822385773062750567319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25063881590515375167044879 37595822385773062750567319)
                ·
                  refine ⟨56393733578659594125850979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37595822385773062750567319 56393733578659594125850979)
                  ·
                    refine ⟨84590600367989391188776469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56393733578659594125850979 84590600367989391188776469)
                    ·
                      refine ⟨3965184392249502711973897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84590600367989391188776469 3965184392249502711973897)
                      ·
                        rfl

theorem cell23_7722169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_7722169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722169 prefixEnd_7722169 := by exact prefixLift 7722169
  have htrace : WordTrace (prefixWord ++ tailWord_7722169) baseStart_7722169 baseEnd_7722169 := by
    simpa [prefixWord, tailWord_7722169, baseEnd_7722169] using wordTrace_append hprefix tailTrace_7722169
  have hstable : (prefixWord ++ tailWord_7722169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722169).length < 2 ^ (prefixWord ++ tailWord_7722169).sum := by decide
  have hdescent : baseEnd_7722169 < baseStart_7722169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722173 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 3, 2, 2]
def baseStart_7722173 : Nat := 118140960795 + 7722173 * 2 ^ 59
def prefixEnd_7722173 : Nat := 4983230072969 + 3 ^ 40 * 7722173 * 2
def baseEnd_7722173 : Nat := 3965186446172120696323879

theorem tailTrace_7722173 : CollatzResearch.WordTrace tailWord_7722173 prefixEnd_7722173 3965186446172120696323879 := by
  unfold tailWord_7722173
  simp only [CollatzResearch.WordTrace]
  refine ⟨281650787852893537995123173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187767191901929025330082115 281650787852893537995123173)
  ·
    refine ⟨52809522722417538374085595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281650787852893537995123173 52809522722417538374085595)
    ·
      refine ⟨79214284083626307561128393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52809522722417538374085595 79214284083626307561128393)
      ·
        refine ⟨59410713062719730670846295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79214284083626307561128393 59410713062719730670846295)
        ·
          refine ⟨89116069594079596006269443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59410713062719730670846295 89116069594079596006269443)
          ·
            refine ⟨133674104391119394009404165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89116069594079596006269443 133674104391119394009404165)
            ·
              refine ⟨25063894573334886376763281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133674104391119394009404165 25063894573334886376763281)
              ·
                refine ⟨18797920930001164782572461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25063894573334886376763281 18797920930001164782572461)
                ·
                  refine ⟨7049220348750436793464673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18797920930001164782572461 7049220348750436793464673)
                  ·
                    refine ⟨5286915261562827595098505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7049220348750436793464673 5286915261562827595098505)
                    ·
                      refine ⟨3965186446172120696323879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5286915261562827595098505 3965186446172120696323879)
                      ·
                        rfl

theorem cell23_7722173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_7722173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722173 prefixEnd_7722173 := by exact prefixLift 7722173
  have htrace : WordTrace (prefixWord ++ tailWord_7722173) baseStart_7722173 baseEnd_7722173 := by
    simpa [prefixWord, tailWord_7722173, baseEnd_7722173] using wordTrace_append hprefix tailTrace_7722173
  have hstable : (prefixWord ++ tailWord_7722173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722173).length < 2 ^ (prefixWord ++ tailWord_7722173).sum := by decide
  have hdescent : baseEnd_7722173 < baseStart_7722173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722249 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 5]
def baseStart_7722249 : Nat := 118140960795 + 7722249 * 2 ^ 59
def prefixEnd_7722249 : Nat := 4983230072969 + 3 ^ 40 * 7722249 * 2
def baseEnd_7722249 : Nat := 3965225470701862398973529

theorem tailTrace_7722249 : CollatzResearch.WordTrace tailWord_7722249 prefixEnd_7722249 3965225470701862398973529 := by
  unfold tailWord_7722249
  simp only [CollatzResearch.WordTrace]
  refine ⟨281653559800618202974889801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187769039867078801983259867 281653559800618202974889801)
  ·
    refine ⟨211240169850463652231167351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281653559800618202974889801 211240169850463652231167351)
    ·
      refine ⟨316860254775695478346751027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211240169850463652231167351 316860254775695478346751027)
      ·
        refine ⟨475290382163543217520126541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316860254775695478346751027 475290382163543217520126541)
        ·
          refine ⟨178233893311328706570047453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475290382163543217520126541 178233893311328706570047453)
          ·
            refine ⟨66837709991748264963767795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178233893311328706570047453 66837709991748264963767795)
            ·
              refine ⟨100256564987622397445651693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66837709991748264963767795 100256564987622397445651693)
              ·
                refine ⟨37596211870358399042119385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100256564987622397445651693 37596211870358399042119385)
                ·
                  refine ⟨28197158902768799281589539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37596211870358399042119385 28197158902768799281589539)
                  ·
                    refine ⟨42295738354153198922384309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28197158902768799281589539 42295738354153198922384309)
                    ·
                      refine ⟨3965225470701862398973529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42295738354153198922384309 3965225470701862398973529)
                      ·
                        rfl

theorem cell23_7722249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_7722249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722249 prefixEnd_7722249 := by exact prefixLift 7722249
  have htrace : WordTrace (prefixWord ++ tailWord_7722249) baseStart_7722249 baseEnd_7722249 := by
    simpa [prefixWord, tailWord_7722249, baseEnd_7722249] using wordTrace_append hprefix tailTrace_7722249
  have hstable : (prefixWord ++ tailWord_7722249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722249).length < 2 ^ (prefixWord ++ tailWord_7722249).sum := by decide
  have hdescent : baseEnd_7722249 < baseStart_7722249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722258 : List Nat := [3, 2, 4, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7722258 : Nat := 118140960795 + 7722258 * 2 ^ 59
def prefixEnd_7722258 : Nat := 4983230072969 + 3 ^ 40 * 7722258 * 2
def baseEnd_7722258 : Nat := 3965230092027752863760989

theorem tailTrace_7722258 : CollatzResearch.WordTrace tailWord_7722258 prefixEnd_7722258 3965230092027752863760989 := by
  unfold tailWord_7722258
  simp only [CollatzResearch.WordTrace]
  refine ⟨70413472014396399377991857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187769258705057065007978285 70413472014396399377991857)
  ·
    refine ⟨52810104010797299533493893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70413472014396399377991857 52810104010797299533493893)
    ·
      refine ⟨9901894502024493662530105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52810104010797299533493893 9901894502024493662530105)
      ·
        refine ⟨7426420876518370246897579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9901894502024493662530105 7426420876518370246897579)
        ·
          refine ⟨11139631314777555370346369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426420876518370246897579 11139631314777555370346369)
          ·
            refine ⟨8354723486083166527759777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11139631314777555370346369 8354723486083166527759777)
            ·
              refine ⟨6266042614562374895819833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8354723486083166527759777 6266042614562374895819833)
              ·
                refine ⟨4699531960921781171864875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6266042614562374895819833 4699531960921781171864875)
                ·
                  refine ⟨7049297941382671757797313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4699531960921781171864875 7049297941382671757797313)
                  ·
                    refine ⟨5286973456037003818347985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7049297941382671757797313 5286973456037003818347985)
                    ·
                      refine ⟨3965230092027752863760989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5286973456037003818347985 3965230092027752863760989)
                      ·
                        rfl

theorem cell23_7722258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7722258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722258 prefixEnd_7722258 := by exact prefixLift 7722258
  have htrace : WordTrace (prefixWord ++ tailWord_7722258) baseStart_7722258 baseEnd_7722258 := by
    simpa [prefixWord, tailWord_7722258, baseEnd_7722258] using wordTrace_append hprefix tailTrace_7722258
  have hstable : (prefixWord ++ tailWord_7722258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722258).length < 2 ^ (prefixWord ++ tailWord_7722258).sum := by decide
  have hdescent : baseEnd_7722258 < baseStart_7722258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722266 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3]
def baseStart_7722266 : Nat := 118140960795 + 7722266 * 2 ^ 59
def prefixEnd_7722266 : Nat := 4983230072969 + 3 ^ 40 * 7722266 * 2
def baseEnd_7722266 : Nat := 3965234199872988832460951

theorem tailTrace_7722266 : CollatzResearch.WordTrace tailWord_7722266 prefixEnd_7722266 3965234199872988832460951 := by
  unfold tailWord_7722266
  simp only [CollatzResearch.WordTrace]
  refine ⟨70413544960389153719564663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187769453227704409918839101 70413544960389153719564663)
  ·
    refine ⟨105620317440583730579346995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70413544960389153719564663 105620317440583730579346995)
    ·
      refine ⟨158430476160875595869020493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105620317440583730579346995 158430476160875595869020493)
      ·
        refine ⟨59411428560328348450882685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158430476160875595869020493 59411428560328348450882685)
        ·
          refine ⟨22279285710123130669081007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59411428560328348450882685 22279285710123130669081007)
          ·
            refine ⟨33418928565184696003621511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22279285710123130669081007 33418928565184696003621511)
            ·
              refine ⟨50128392847777044005432267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33418928565184696003621511 50128392847777044005432267)
              ·
                refine ⟨75192589271665566008148401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50128392847777044005432267 75192589271665566008148401)
                ·
                  refine ⟨56394441953749174506111301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75192589271665566008148401 56394441953749174506111301)
                  ·
                    refine ⟨10573957866327970219895869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56394441953749174506111301 10573957866327970219895869)
                    ·
                      refine ⟨3965234199872988832460951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10573957866327970219895869 3965234199872988832460951)
                      ·
                        rfl

theorem cell23_7722266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_7722266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722266 prefixEnd_7722266 := by exact prefixLift 7722266
  have htrace : WordTrace (prefixWord ++ tailWord_7722266) baseStart_7722266 baseEnd_7722266 := by
    simpa [prefixWord, tailWord_7722266, baseEnd_7722266] using wordTrace_append hprefix tailTrace_7722266
  have hstable : (prefixWord ++ tailWord_7722266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722266).length < 2 ^ (prefixWord ++ tailWord_7722266).sum := by decide
  have hdescent : baseEnd_7722266 < baseStart_7722266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722276 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_7722276 : Nat := 118140960795 + 7722276 * 2 ^ 59
def prefixEnd_7722276 : Nat := 4983230072969 + 3 ^ 40 * 7722276 * 2
def baseEnd_7722276 : Nat := 3965239334679533793335905

theorem tailTrace_7722276 : CollatzResearch.WordTrace tailWord_7722276 prefixEnd_7722276 3965239334679533793335905 := by
  unfold tailWord_7722276
  simp only [CollatzResearch.WordTrace]
  refine ⟨140827272285760193293061341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187769696381013591057415121 140827272285760193293061341)
  ·
    refine ⟨52810227107160072484898003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140827272285760193293061341 52810227107160072484898003)
    ·
      refine ⟨79215340660740108727347005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52810227107160072484898003 79215340660740108727347005)
      ·
        refine ⟨29705752747777540772755127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79215340660740108727347005 29705752747777540772755127)
        ·
          refine ⟨44558629121666311159132691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29705752747777540772755127 44558629121666311159132691)
          ·
            refine ⟨66837943682499466738699037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44558629121666311159132691 66837943682499466738699037)
            ·
              refine ⟨25064228880937300027012139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66837943682499466738699037 25064228880937300027012139)
              ·
                refine ⟨37596343321405950040518209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25064228880937300027012139 37596343321405950040518209)
                ·
                  refine ⟨28197257491054462530388657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37596343321405950040518209 28197257491054462530388657)
                  ·
                    refine ⟨21147943118290846897791493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28197257491054462530388657 21147943118290846897791493)
                    ·
                      refine ⟨3965239334679533793335905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21147943118290846897791493 3965239334679533793335905)
                      ·
                        rfl

theorem cell23_7722276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_7722276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722276 prefixEnd_7722276 := by exact prefixLift 7722276
  have htrace : WordTrace (prefixWord ++ tailWord_7722276) baseStart_7722276 baseEnd_7722276 := by
    simpa [prefixWord, tailWord_7722276, baseEnd_7722276] using wordTrace_append hprefix tailTrace_7722276
  have hstable : (prefixWord ++ tailWord_7722276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722276).length < 2 ^ (prefixWord ++ tailWord_7722276).sum := by decide
  have hdescent : baseEnd_7722276 < baseStart_7722276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722280 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_7722280 : Nat := 118140960795 + 7722280 * 2 ^ 59
def prefixEnd_7722280 : Nat := 4983230072969 + 3 ^ 40 * 7722280 * 2
def baseEnd_7722280 : Nat := 3965241388602151777685887

theorem tailTrace_7722280 : CollatzResearch.WordTrace tailWord_7722280 prefixEnd_7722280 3965241388602151777685887 := by
  unfold tailWord_7722280
  simp only [CollatzResearch.WordTrace]
  refine ⟨140827345231752947634634147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187769793642337263512845529 140827345231752947634634147)
  ·
    refine ⟨211241017847629421451951221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140827345231752947634634147 211241017847629421451951221)
    ·
      refine ⟨19803845423215258261120427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211241017847629421451951221 19803845423215258261120427)
      ·
        refine ⟨29705768134822887391680641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19803845423215258261120427 29705768134822887391680641)
        ·
          refine ⟨22279326101117165543760481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29705768134822887391680641 22279326101117165543760481)
          ·
            refine ⟨16709494575837874157820361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22279326101117165543760481 16709494575837874157820361)
            ·
              refine ⟨12532120931878405618365271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16709494575837874157820361 12532120931878405618365271)
              ·
                refine ⟨18798181397817608427547907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12532120931878405618365271 18798181397817608427547907)
                ·
                  refine ⟨28197272096726412641321861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18798181397817608427547907 28197272096726412641321861)
                  ·
                    refine ⟨5286988518136202370247849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28197272096726412641321861 5286988518136202370247849)
                    ·
                      refine ⟨3965241388602151777685887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5286988518136202370247849 3965241388602151777685887)
                      ·
                        rfl

theorem cell23_7722280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_7722280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722280 prefixEnd_7722280 := by exact prefixLift 7722280
  have htrace : WordTrace (prefixWord ++ tailWord_7722280) baseStart_7722280 baseEnd_7722280 := by
    simpa [prefixWord, tailWord_7722280, baseEnd_7722280] using wordTrace_append hprefix tailTrace_7722280
  have hstable : (prefixWord ++ tailWord_7722280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722280).length < 2 ^ (prefixWord ++ tailWord_7722280).sum := by decide
  have hdescent : baseEnd_7722280 < baseStart_7722280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722301 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7722301 : Nat := 118140960795 + 7722301 * 2 ^ 59
def prefixEnd_7722301 : Nat := 4983230072969 + 3 ^ 40 * 7722301 * 2
def baseEnd_7722301 : Nat := 3965252171695896195523291

theorem tailTrace_7722301 : CollatzResearch.WordTrace tailWord_7722301 prefixEnd_7722301 3965252171695896195523291 := by
  unfold tailWord_7722301
  simp only [CollatzResearch.WordTrace]
  refine ⟨281655456396429815855782757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187770304264286543903855171 281655456396429815855782757)
  ·
    refine ⟨52810398074330590472959267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281655456396429815855782757 52810398074330590472959267)
    ·
      refine ⟨79215597111495885709438901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52810398074330590472959267 79215597111495885709438901)
      ·
        refine ⟨7426462229202739285259897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79215597111495885709438901 7426462229202739285259897)
        ·
          refine ⟨5569846671902054463944923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7426462229202739285259897 5569846671902054463944923)
          ·
            refine ⟨8354770007853081695917385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569846671902054463944923 8354770007853081695917385)
            ·
              refine ⟨6266077505889811271938039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8354770007853081695917385 6266077505889811271938039)
              ·
                refine ⟨9399116258834716907907059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6266077505889811271938039 9399116258834716907907059)
                ·
                  refine ⟨14098674388252075361860589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9399116258834716907907059 14098674388252075361860589)
                  ·
                    refine ⟨5287002895594528260697721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14098674388252075361860589 5287002895594528260697721)
                    ·
                      refine ⟨3965252171695896195523291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5287002895594528260697721 3965252171695896195523291)
                      ·
                        rfl

theorem cell23_7722301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7722301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722301 prefixEnd_7722301 := by exact prefixLift 7722301
  have htrace : WordTrace (prefixWord ++ tailWord_7722301) baseStart_7722301 baseEnd_7722301 := by
    simpa [prefixWord, tailWord_7722301, baseEnd_7722301] using wordTrace_append hprefix tailTrace_7722301
  have hstable : (prefixWord ++ tailWord_7722301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722301).length < 2 ^ (prefixWord ++ tailWord_7722301).sum := by decide
  have hdescent : baseEnd_7722301 < baseStart_7722301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722303 : List Nat := [1, 1, 2, 2, 4, 3, 2, 3, 5]
def baseStart_7722303 : Nat := 118140960795 + 7722303 * 2 ^ 59
def prefixEnd_7722303 : Nat := 4983230072969 + 3 ^ 40 * 7722303 * 2
def baseEnd_7722303 : Nat := 440583688739689465299809

theorem tailTrace_7722303 : CollatzResearch.WordTrace tailWord_7722303 prefixEnd_7722303 440583688739689465299809 := by
  unfold tailWord_7722303
  simp only [CollatzResearch.WordTrace]
  refine ⟨281655529342422570197355563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187770352894948380131570375 281655529342422570197355563)
  ·
    refine ⟨422483294013633855296033345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281655529342422570197355563 422483294013633855296033345)
    ·
      refine ⟨316862470510225391472025009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422483294013633855296033345 316862470510225391472025009)
      ·
        refine ⟨237646852882669043604018757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316862470510225391472025009 237646852882669043604018757)
        ·
          refine ⟨44558784915500445675753517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237646852882669043604018757 44558784915500445675753517)
          ·
            refine ⟨16709544343312667128407569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44558784915500445675753517 16709544343312667128407569)
            ·
              refine ⟨12532158257484500346305677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16709544343312667128407569 12532158257484500346305677)
              ·
                refine ⟨4699559346556687629864629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12532158257484500346305677 4699559346556687629864629)
                ·
                  refine ⟨440583688739689465299809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4699559346556687629864629 440583688739689465299809)
                  ·
                    rfl

theorem cell23_7722303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 5].length) (baseStart_7722303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722303 prefixEnd_7722303 := by exact prefixLift 7722303
  have htrace : WordTrace (prefixWord ++ tailWord_7722303) baseStart_7722303 baseEnd_7722303 := by
    simpa [prefixWord, tailWord_7722303, baseEnd_7722303] using wordTrace_append hprefix tailTrace_7722303
  have hstable : (prefixWord ++ tailWord_7722303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722303).length < 2 ^ (prefixWord ++ tailWord_7722303).sum := by decide
  have hdescent : baseEnd_7722303 < baseStart_7722303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722309 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_7722309 : Nat := 118140960795 + 7722309 * 2 ^ 59
def prefixEnd_7722309 : Nat := 4983230072969 + 3 ^ 40 * 7722309 * 2
def baseEnd_7722309 : Nat := 3965256279541132164223253

theorem tailTrace_7722309 : CollatzResearch.WordTrace tailWord_7722309 prefixEnd_7722309 3965256279541132164223253 := by
  unfold tailWord_7722309
  simp only [CollatzResearch.WordTrace]
  refine ⟨281655748180400833222073981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187770498786933888814715987 281655748180400833222073981)
  ·
    refine ⟨105620905567650312458277743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281655748180400833222073981 105620905567650312458277743)
    ·
      refine ⟨158431358351475468687416615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105620905567650312458277743 158431358351475468687416615)
      ·
        refine ⟨237647037527213203031124923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158431358351475468687416615 237647037527213203031124923)
        ·
          refine ⟨356470556290819804546687385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237647037527213203031124923 356470556290819804546687385)
          ·
            refine ⟨267352917218114853410015539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356470556290819804546687385 267352917218114853410015539)
            ·
              refine ⟨401029375827172280115023309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267352917218114853410015539 401029375827172280115023309)
              ·
                refine ⟨150386015935189605043133741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401029375827172280115023309 150386015935189605043133741)
                ·
                  refine ⟨56394755975696101891175153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150386015935189605043133741 56394755975696101891175153)
                  ·
                    refine ⟨42296066981772076418381365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56394755975696101891175153 42296066981772076418381365)
                    ·
                      refine ⟨3965256279541132164223253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42296066981772076418381365 3965256279541132164223253)
                      ·
                        rfl

theorem cell23_7722309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_7722309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722309 prefixEnd_7722309 := by exact prefixLift 7722309
  have htrace : WordTrace (prefixWord ++ tailWord_7722309) baseStart_7722309 baseEnd_7722309 := by
    simpa [prefixWord, tailWord_7722309, baseEnd_7722309] using wordTrace_append hprefix tailTrace_7722309
  have hstable : (prefixWord ++ tailWord_7722309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722309).length < 2 ^ (prefixWord ++ tailWord_7722309).sum := by decide
  have hdescent : baseEnd_7722309 < baseStart_7722309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722336 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 4]
def baseStart_7722336 : Nat := 118140960795 + 7722336 * 2 ^ 59
def prefixEnd_7722336 : Nat := 4983230072969 + 3 ^ 40 * 7722336 * 2
def baseEnd_7722336 : Nat := 3965270143518803558585629

theorem tailTrace_7722336 : CollatzResearch.WordTrace tailWord_7722336 prefixEnd_7722336 3965270143518803558585629 := by
  unfold tailWord_7722336
  simp only [CollatzResearch.WordTrace]
  refine ⟨140828366475651508416653431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187771155300868677888871241 140828366475651508416653431)
  ·
    refine ⟨211242549713477262624980147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140828366475651508416653431 211242549713477262624980147)
    ·
      refine ⟨316863824570215893937470221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211242549713477262624980147 316863824570215893937470221)
      ·
        refine ⟨118823934213830960226551333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316863824570215893937470221 118823934213830960226551333)
        ·
          refine ⟨22279487665093305042478375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118823934213830960226551333 22279487665093305042478375)
          ·
            refine ⟨33419231497639957563717563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22279487665093305042478375 33419231497639957563717563)
            ·
              refine ⟨50128847246459936345576345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33419231497639957563717563 50128847246459936345576345)
              ·
                refine ⟨37596635434844952259182259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50128847246459936345576345 37596635434844952259182259)
                ·
                  refine ⟨56394953152267428388773389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37596635434844952259182259 56394953152267428388773389)
                  ·
                    refine ⟨21148107432100285645790021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56394953152267428388773389 21148107432100285645790021)
                    ·
                      refine ⟨3965270143518803558585629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21148107432100285645790021 3965270143518803558585629)
                      ·
                        rfl

theorem cell23_7722336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_7722336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722336 prefixEnd_7722336 := by exact prefixLift 7722336
  have htrace : WordTrace (prefixWord ++ tailWord_7722336) baseStart_7722336 baseEnd_7722336 := by
    simpa [prefixWord, tailWord_7722336, baseEnd_7722336] using wordTrace_append hprefix tailTrace_7722336
  have hstable : (prefixWord ++ tailWord_7722336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722336).length < 2 ^ (prefixWord ++ tailWord_7722336).sum := by decide
  have hdescent : baseEnd_7722336 < baseStart_7722336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722359 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 10]
def baseStart_7722359 : Nat := 118140960795 + 7722359 * 2 ^ 59
def prefixEnd_7722359 : Nat := 4983230072969 + 3 ^ 40 * 7722359 * 2
def baseEnd_7722359 : Nat := 440586883730428552066447

theorem tailTrace_7722359 : CollatzResearch.WordTrace tailWord_7722359 prefixEnd_7722359 440586883730428552066447 := by
  unfold tailWord_7722359
  simp only [CollatzResearch.WordTrace]
  refine ⟨281657571830219691761394131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187771714553479794507596087 281657571830219691761394131)
  ·
    refine ⟨422486357745329537642091197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281657571830219691761394131 422486357745329537642091197)
    ·
      refine ⟨158432384154498576615784199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422486357745329537642091197 158432384154498576615784199)
      ·
        refine ⟨237648576231747864923676299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158432384154498576615784199 237648576231747864923676299)
        ·
          refine ⟨356472864347621797385514449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237648576231747864923676299 356472864347621797385514449)
          ·
            refine ⟨267354648260716348039135837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356472864347621797385514449 267354648260716348039135837)
            ·
              refine ⟨100257993097768630514675939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267354648260716348039135837 100257993097768630514675939)
              ·
                refine ⟨150386989646652945772013909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100257993097768630514675939 150386989646652945772013909)
                ·
                  refine ⟨440586883730428552066447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 150386989646652945772013909 440586883730428552066447)
                  ·
                    rfl

theorem cell23_7722359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 10].length) (baseStart_7722359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722359 prefixEnd_7722359 := by exact prefixLift 7722359
  have htrace : WordTrace (prefixWord ++ tailWord_7722359) baseStart_7722359 baseEnd_7722359 := by
    simpa [prefixWord, tailWord_7722359, baseEnd_7722359] using wordTrace_append hprefix tailTrace_7722359
  have hstable : (prefixWord ++ tailWord_7722359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722359).length < 2 ^ (prefixWord ++ tailWord_7722359).sum := by decide
  have hdescent : baseEnd_7722359 < baseStart_7722359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722370 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7722370 : Nat := 118140960795 + 7722370 * 2 ^ 59
def prefixEnd_7722370 : Nat := 4983230072969 + 3 ^ 40 * 7722370 * 2
def baseEnd_7722370 : Nat := 3965287601861056425560473

theorem tailTrace_7722370 : CollatzResearch.WordTrace tailWord_7722370 prefixEnd_7722370 3965287601861056425560473 := by
  unfold tailWord_7722370
  simp only [CollatzResearch.WordTrace]
  refine ⟨70414493258294960160011141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187771982022119893760029709 70414493258294960160011141)
  ·
    refine ⟨13202717485930305030002089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70414493258294960160011141 13202717485930305030002089)
    ·
      refine ⟨9902038114447728772501567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13202717485930305030002089 9902038114447728772501567)
      ·
        refine ⟨14853057171671593158752351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9902038114447728772501567 14853057171671593158752351)
        ·
          refine ⟨22279585757507389738128527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14853057171671593158752351 22279585757507389738128527)
          ·
            refine ⟨33419378636261084607192791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22279585757507389738128527 33419378636261084607192791)
            ·
              refine ⟨50129067954391626910789187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33419378636261084607192791 50129067954391626910789187)
              ·
                refine ⟨75193601931587440366183781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50129067954391626910789187 75193601931587440366183781)
                ·
                  refine ⟨14098800362172645068659459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75193601931587440366183781 14098800362172645068659459)
                  ·
                    refine ⟨21148200543258967602989189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14098800362172645068659459 21148200543258967602989189)
                    ·
                      refine ⟨3965287601861056425560473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21148200543258967602989189 3965287601861056425560473)
                      ·
                        rfl

theorem cell23_7722370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7722370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722370 prefixEnd_7722370 := by exact prefixLift 7722370
  have htrace : WordTrace (prefixWord ++ tailWord_7722370) baseStart_7722370 baseEnd_7722370 := by
    simpa [prefixWord, tailWord_7722370, baseEnd_7722370] using wordTrace_append hprefix tailTrace_7722370
  have hstable : (prefixWord ++ tailWord_7722370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722370).length < 2 ^ (prefixWord ++ tailWord_7722370).sum := by decide
  have hdescent : baseEnd_7722370 < baseStart_7722370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722376 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 8]
def baseStart_7722376 : Nat := 118140960795 + 7722376 * 2 ^ 59
def prefixEnd_7722376 : Nat := 4983230072969 + 3 ^ 40 * 7722376 * 2
def baseEnd_7722376 : Nat := 440587853638331489120605

theorem tailTrace_7722376 : CollatzResearch.WordTrace tailWord_7722376 prefixEnd_7722376 440587853638331489120605 := by
  unfold tailWord_7722376
  simp only [CollatzResearch.WordTrace]
  refine ⟨140829095935579051832381491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187772127914105402443175321 140829095935579051832381491)
  ·
    refine ⟨211243643903368577748572237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140829095935579051832381491 211243643903368577748572237)
    ·
      refine ⟨79216366463763216655714589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211243643903368577748572237 79216366463763216655714589)
      ·
        refine ⟨29706137423911206245892971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79216366463763216655714589 29706137423911206245892971)
        ·
          refine ⟨44559206135866809368839457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29706137423911206245892971 44559206135866809368839457)
          ·
            refine ⟨33419404601900107026629593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44559206135866809368839457 33419404601900107026629593)
            ·
              refine ⟨25064553451425080269972195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33419404601900107026629593 25064553451425080269972195)
              ·
                refine ⟨37596830177137620404958293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25064553451425080269972195 37596830177137620404958293)
                ·
                  refine ⟨440587853638331489120605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37596830177137620404958293 440587853638331489120605)
                  ·
                    rfl

theorem cell23_7722376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 8].length) (baseStart_7722376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722376 prefixEnd_7722376 := by exact prefixLift 7722376
  have htrace : WordTrace (prefixWord ++ tailWord_7722376) baseStart_7722376 baseEnd_7722376 := by
    simpa [prefixWord, tailWord_7722376, baseEnd_7722376] using wordTrace_append hprefix tailTrace_7722376
  have hstable : (prefixWord ++ tailWord_7722376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722376).length < 2 ^ (prefixWord ++ tailWord_7722376).sum := by decide
  have hdescent : baseEnd_7722376 < baseStart_7722376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722393 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 6]
def baseStart_7722393 : Nat := 118140960795 + 7722393 * 2 ^ 59
def prefixEnd_7722393 : Nat := 4983230072969 + 3 ^ 40 * 7722393 * 2
def baseEnd_7722393 : Nat := 440588823546234426174763

theorem tailTrace_7722393 : CollatzResearch.WordTrace tailWord_7722393 prefixEnd_7722393 440588823546234426174763 := by
  unfold tailWord_7722393
  simp only [CollatzResearch.WordTrace]
  refine ⟨281658811912096515568131833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187772541274731010378754555 281658811912096515568131833)
  ·
    refine ⟨211244108934072386676098875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281658811912096515568131833 211244108934072386676098875)
    ·
      refine ⟨316866163401108580014148313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211244108934072386676098875 316866163401108580014148313)
      ·
        refine ⟨237649622550831435010611235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316866163401108580014148313 237649622550831435010611235)
        ·
          refine ⟨356474433826247152515916853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237649622550831435010611235 356474433826247152515916853)
          ·
            refine ⟨33419478171210670548367205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 356474433826247152515916853 33419478171210670548367205)
            ·
              refine ⟨6266152157102000727818851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33419478171210670548367205 6266152157102000727818851)
              ·
                refine ⟨9399228235653001091728277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6266152157102000727818851 9399228235653001091728277)
                ·
                  refine ⟨440588823546234426174763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9399228235653001091728277 440588823546234426174763)
                  ·
                    rfl

theorem cell23_7722393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 6].length) (baseStart_7722393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722393 prefixEnd_7722393 := by exact prefixLift 7722393
  have htrace : WordTrace (prefixWord ++ tailWord_7722393) baseStart_7722393 baseEnd_7722393 := by
    simpa [prefixWord, tailWord_7722393, baseEnd_7722393] using wordTrace_append hprefix tailTrace_7722393
  have hstable : (prefixWord ++ tailWord_7722393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722393).length < 2 ^ (prefixWord ++ tailWord_7722393).sum := by decide
  have hdescent : baseEnd_7722393 < baseStart_7722393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722403 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 5, 1, 3]
def baseStart_7722403 : Nat := 118140960795 + 7722403 * 2 ^ 59
def prefixEnd_7722403 : Nat := 4983230072969 + 3 ^ 40 * 7722403 * 2
def baseEnd_7722403 : Nat := 3965304546722654796447821

theorem tailTrace_7722403 : CollatzResearch.WordTrace tailWord_7722403 prefixEnd_7722403 3965304546722654796447821 := by
  unfold tailWord_7722403
  simp only [CollatzResearch.WordTrace]
  refine ⟨281659176642060287275995863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187772784428040191517330575 281659176642060287275995863)
  ·
    refine ⟨422488764963090430913993795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281659176642060287275995863 422488764963090430913993795)
    ·
      refine ⟨633733147444635646370990693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422488764963090430913993795 633733147444635646370990693)
      ·
        refine ⟨118824965145869183694560755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 633733147444635646370990693 118824965145869183694560755)
        ·
          refine ⟨178237447718803775541841133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118824965145869183694560755 178237447718803775541841133)
          ·
            refine ⟨66839042894551415828190425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178237447718803775541841133 66839042894551415828190425)
            ·
              refine ⟨50129282170913561871142819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66839042894551415828190425 50129282170913561871142819)
              ·
                refine ⟨75193923256370342806714229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50129282170913561871142819 75193923256370342806714229)
                ·
                  refine ⟨7049430305284719638129459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75193923256370342806714229 7049430305284719638129459)
                  ·
                    refine ⟨10574145457927079457194189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7049430305284719638129459 10574145457927079457194189)
                    ·
                      refine ⟨3965304546722654796447821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10574145457927079457194189 3965304546722654796447821)
                      ·
                        rfl

theorem cell23_7722403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_7722403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722403 prefixEnd_7722403 := by exact prefixLift 7722403
  have htrace : WordTrace (prefixWord ++ tailWord_7722403) baseStart_7722403 baseEnd_7722403 := by
    simpa [prefixWord, tailWord_7722403, baseEnd_7722403] using wordTrace_append hprefix tailTrace_7722403
  have hstable : (prefixWord ++ tailWord_7722403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722403).length < 2 ^ (prefixWord ++ tailWord_7722403).sum := by decide
  have hdescent : baseEnd_7722403 < baseStart_7722403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722453 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 1, 6]
def baseStart_7722453 : Nat := 118140960795 + 7722453 * 2 ^ 59
def prefixEnd_7722453 : Nat := 4983230072969 + 3 ^ 40 * 7722453 * 2
def baseEnd_7722453 : Nat := 1321776740251793200274197

theorem tailTrace_7722453 : CollatzResearch.WordTrace tailWord_7722453 prefixEnd_7722453 1321776740251793200274197 := by
  unfold tailWord_7722453
  simp only [CollatzResearch.WordTrace]
  refine ⟨281661000291879145815316013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187774000194586097210210675 281661000291879145815316013)
  ·
    refine ⟨105622875109454679680743505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281661000291879145815316013 105622875109454679680743505)
    ·
      refine ⟨79217156332091009760557629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105622875109454679680743505 79217156332091009760557629)
      ·
        refine ⟨29706433624534128660209111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79217156332091009760557629 29706433624534128660209111)
        ·
          refine ⟨44559650436801192990313667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29706433624534128660209111 44559650436801192990313667)
          ·
            refine ⟨66839475655201789485470501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44559650436801192990313667 66839475655201789485470501)
            ·
              refine ⟨12532401685350335528525719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66839475655201789485470501 12532401685350335528525719)
              ·
                refine ⟨18798602528025503292788579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12532401685350335528525719 18798602528025503292788579)
                ·
                  refine ⟨28197903792038254939182869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18798602528025503292788579 28197903792038254939182869)
                  ·
                    refine ⟨1321776740251793200274197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28197903792038254939182869 1321776740251793200274197)
                    ·
                      rfl

theorem cell23_7722453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_7722453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722453 prefixEnd_7722453 := by exact prefixLift 7722453
  have htrace : WordTrace (prefixWord ++ tailWord_7722453) baseStart_7722453 baseEnd_7722453 := by
    simpa [prefixWord, tailWord_7722453, baseEnd_7722453] using wordTrace_append hprefix tailTrace_7722453
  have hstable : (prefixWord ++ tailWord_7722453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722453).length < 2 ^ (prefixWord ++ tailWord_7722453).sum := by decide
  have hdescent : baseEnd_7722453 < baseStart_7722453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722456 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_7722456 : Nat := 118140960795 + 7722456 * 2 ^ 59
def prefixEnd_7722456 : Nat := 4983230072969 + 3 ^ 40 * 7722456 * 2
def baseEnd_7722456 : Nat := 3965331761197343089085077

theorem tailTrace_7722456 : CollatzResearch.WordTrace tailWord_7722456 prefixEnd_7722456 3965331761197343089085077 := by
  unfold tailWord_7722456
  simp only [CollatzResearch.WordTrace]
  refine ⟨140830554855434138663837611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187774073140578851551783481 140830554855434138663837611)
  ·
    refine ⟨211245832283151207995756417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140830554855434138663837611 211245832283151207995756417)
    ·
      refine ⟨158434374212363405996817313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211245832283151207995756417 158434374212363405996817313)
      ·
        refine ⟨118825780659272554497612985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158434374212363405996817313 118825780659272554497612985)
        ·
          refine ⟨89119335494454415873209739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118825780659272554497612985 89119335494454415873209739)
          ·
            refine ⟨133679003241681623809814609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89119335494454415873209739 133679003241681623809814609)
            ·
              refine ⟨100259252431261217857360957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133679003241681623809814609 100259252431261217857360957)
              ·
                refine ⟨37597219661722956696510359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100259252431261217857360957 37597219661722956696510359)
                ·
                  refine ⟨56395829492584435044765539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37597219661722956696510359 56395829492584435044765539)
                  ·
                    refine ⟨84593744238876652567148309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56395829492584435044765539 84593744238876652567148309)
                    ·
                      refine ⟨3965331761197343089085077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84593744238876652567148309 3965331761197343089085077)
                      ·
                        rfl

theorem cell23_7722456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_7722456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722456 prefixEnd_7722456 := by exact prefixLift 7722456
  have htrace : WordTrace (prefixWord ++ tailWord_7722456) baseStart_7722456 baseEnd_7722456 := by
    simpa [prefixWord, tailWord_7722456, baseEnd_7722456] using wordTrace_append hprefix tailTrace_7722456
  have hstable : (prefixWord ++ tailWord_7722456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722456).length < 2 ^ (prefixWord ++ tailWord_7722456).sum := by decide
  have hdescent : baseEnd_7722456 < baseStart_7722456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722463 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 3]
def baseStart_7722463 : Nat := 118140960795 + 7722463 * 2 ^ 59
def prefixEnd_7722463 : Nat := 4983230072969 + 3 ^ 40 * 7722463 * 2
def baseEnd_7722463 : Nat := 3965335355561924561697545

theorem tailTrace_7722463 : CollatzResearch.WordTrace tailWord_7722463 prefixEnd_7722463 3965335355561924561697545 := by
  unfold tailWord_7722463
  simp only [CollatzResearch.WordTrace]
  refine ⟨281661365021842917523180043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187774243347895278348786695 281661365021842917523180043)
  ·
    refine ⟨422492047532764376284770065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281661365021842917523180043 422492047532764376284770065)
    ·
      refine ⟨316869035649573282213577549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422492047532764376284770065 316869035649573282213577549)
      ·
        refine ⟨118825888368589980830091581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316869035649573282213577549 118825888368589980830091581)
        ·
          refine ⟨44559708138221242811284343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118825888368589980830091581 44559708138221242811284343)
          ·
            refine ⟨66839562207331864216926515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44559708138221242811284343 66839562207331864216926515)
            ·
              refine ⟨100259343310997796325389773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66839562207331864216926515 100259343310997796325389773)
              ·
                refine ⟨37597253741624173622021165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100259343310997796325389773 37597253741624173622021165)
                ·
                  refine ⟨14098970153109065108257937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37597253741624173622021165 14098970153109065108257937)
                  ·
                    refine ⟨10574227614831798831193453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14098970153109065108257937 10574227614831798831193453)
                    ·
                      refine ⟨3965335355561924561697545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10574227614831798831193453 3965335355561924561697545)
                      ·
                        rfl

theorem cell23_7722463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_7722463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722463 prefixEnd_7722463 := by exact prefixLift 7722463
  have htrace : WordTrace (prefixWord ++ tailWord_7722463) baseStart_7722463 baseEnd_7722463 := by
    simpa [prefixWord, tailWord_7722463, baseEnd_7722463] using wordTrace_append hprefix tailTrace_7722463
  have hstable : (prefixWord ++ tailWord_7722463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722463).length < 2 ^ (prefixWord ++ tailWord_7722463).sum := by decide
  have hdescent : baseEnd_7722463 < baseStart_7722463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722474 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 1, 5]
def baseStart_7722474 : Nat := 118140960795 + 7722474 * 2 ^ 59
def prefixEnd_7722474 : Nat := 4983230072969 + 3 ^ 40 * 7722474 * 2
def baseEnd_7722474 : Nat := 1321780334616374672886665

theorem tailTrace_7722474 : CollatzResearch.WordTrace tailWord_7722474 prefixEnd_7722474 1321780334616374672886665 := by
  unfold tailWord_7722474
  simp only [CollatzResearch.WordTrace]
  refine ⟨70415441556200766600457619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187774510816535377601220317 70415441556200766600457619)
  ·
    refine ⟨105623162334301149900686429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70415441556200766600457619 105623162334301149900686429)
    ·
      refine ⟨39608685875362931212757411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105623162334301149900686429 39608685875362931212757411)
      ·
        refine ⟨59413028813044396819136117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39608685875362931212757411 59413028813044396819136117)
        ·
          refine ⟨5569971451222912201794011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59413028813044396819136117 5569971451222912201794011)
          ·
            refine ⟨8354957176834368302691017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569971451222912201794011 8354957176834368302691017)
            ·
              refine ⟨6266217882625776227018263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8354957176834368302691017 6266217882625776227018263)
              ·
                refine ⟨9399326823938664340527395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6266217882625776227018263 9399326823938664340527395)
                ·
                  refine ⟨14098990235907996510791093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9399326823938664340527395 14098990235907996510791093)
                  ·
                    refine ⟨1321780334616374672886665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14098990235907996510791093 1321780334616374672886665)
                    ·
                      rfl

theorem cell23_7722474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_7722474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722474 prefixEnd_7722474 := by exact prefixLift 7722474
  have htrace : WordTrace (prefixWord ++ tailWord_7722474) baseStart_7722474 baseEnd_7722474 := by
    simpa [prefixWord, tailWord_7722474, baseEnd_7722474] using wordTrace_append hprefix tailTrace_7722474
  have hstable : (prefixWord ++ tailWord_7722474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722474).length < 2 ^ (prefixWord ++ tailWord_7722474).sum := by decide
  have hdescent : baseEnd_7722474 < baseStart_7722474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722477 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_7722477 : Nat := 118140960795 + 7722477 * 2 ^ 59
def prefixEnd_7722477 : Nat := 4983230072969 + 3 ^ 40 * 7722477 * 2
def baseEnd_7722477 : Nat := 3965342544291087506922481

theorem tailTrace_7722477 : CollatzResearch.WordTrace tailWord_7722477 prefixEnd_7722477 3965342544291087506922481 := by
  unfold tailWord_7722477
  simp only [CollatzResearch.WordTrace]
  refine ⟨281661875643792197914189685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187774583762528131942793123 281661875643792197914189685)
  ·
    refine ⟨26405800841605518554455283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281661875643792197914189685 26405800841605518554455283)
    ·
      refine ⟨39608701262408277831682925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26405800841605518554455283 39608701262408277831682925)
      ·
        refine ⟨14853262973403104186881097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39608701262408277831682925 14853262973403104186881097)
        ·
          refine ⟨11139947230052328140160823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14853262973403104186881097 11139947230052328140160823)
          ·
            refine ⟨16709920845078492210241235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11139947230052328140160823 16709920845078492210241235)
            ·
              refine ⟨25064881267617738315361853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16709920845078492210241235 25064881267617738315361853)
              ·
                refine ⟨9399330475356651868260695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25064881267617738315361853 9399330475356651868260695)
                ·
                  refine ⟨14098995713034977802391043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9399330475356651868260695 14098995713034977802391043)
                  ·
                    refine ⟨21148493569552466703586565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14098995713034977802391043 21148493569552466703586565)
                    ·
                      refine ⟨3965342544291087506922481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21148493569552466703586565 3965342544291087506922481)
                      ·
                        rfl

theorem cell23_7722477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_7722477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722477 prefixEnd_7722477 := by exact prefixLift 7722477
  have htrace : WordTrace (prefixWord ++ tailWord_7722477) baseStart_7722477 baseEnd_7722477 := by
    simpa [prefixWord, tailWord_7722477, baseEnd_7722477] using wordTrace_append hprefix tailTrace_7722477
  have hstable : (prefixWord ++ tailWord_7722477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722477).length < 2 ^ (prefixWord ++ tailWord_7722477).sum := by decide
  have hdescent : baseEnd_7722477 < baseStart_7722477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722480 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 3]
def baseStart_7722480 : Nat := 118140960795 + 7722480 * 2 ^ 59
def prefixEnd_7722480 : Nat := 4983230072969 + 3 ^ 40 * 7722480 * 2
def baseEnd_7722480 : Nat := 3965344084733050995184967

theorem tailTrace_7722480 : CollatzResearch.WordTrace tailWord_7722480 prefixEnd_7722480 3965344084733050995184967 := by
  unfold tailWord_7722480
  simp only [CollatzResearch.WordTrace]
  refine ⟨140830992531390664713274447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187774656708520886284365929 140830992531390664713274447)
  ·
    refine ⟨211246488797085997069911671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140830992531390664713274447 211246488797085997069911671)
    ·
      refine ⟨316869733195628995604867507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211246488797085997069911671 316869733195628995604867507)
      ·
        refine ⟨475304599793443493407301261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316869733195628995604867507 475304599793443493407301261)
        ·
          refine ⟨178239224922541310027737973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475304599793443493407301261 178239224922541310027737973)
          ·
            refine ⟨16709927336488247815100435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178239224922541310027737973 16709927336488247815100435)
            ·
              refine ⟨25064891004732371722650653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16709927336488247815100435 25064891004732371722650653)
              ·
                refine ⟨9399334126774639395993995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25064891004732371722650653 9399334126774639395993995)
                ·
                  refine ⟨14099001190161959093990993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9399334126774639395993995 14099001190161959093990993)
                  ·
                    refine ⟨10574250892621469320493245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14099001190161959093990993 10574250892621469320493245)
                    ·
                      refine ⟨3965344084733050995184967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10574250892621469320493245 3965344084733050995184967)
                      ·
                        rfl

theorem cell23_7722480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 3].length) (baseStart_7722480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722480 prefixEnd_7722480 := by exact prefixLift 7722480
  have htrace : WordTrace (prefixWord ++ tailWord_7722480) baseStart_7722480 baseEnd_7722480 := by
    simpa [prefixWord, tailWord_7722480, baseEnd_7722480] using wordTrace_append hprefix tailTrace_7722480
  have hstable : (prefixWord ++ tailWord_7722480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722480).length < 2 ^ (prefixWord ++ tailWord_7722480).sum := by decide
  have hdescent : baseEnd_7722480 < baseStart_7722480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722507 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 1, 2, 4]
def baseStart_7722507 : Nat := 118140960795 + 7722507 * 2 ^ 59
def prefixEnd_7722507 : Nat := 4983230072969 + 3 ^ 40 * 7722507 * 2
def baseEnd_7722507 : Nat := 3965357948710722389547343

theorem tailTrace_7722507 : CollatzResearch.WordTrace tailWord_7722507 prefixEnd_7722507 3965357948710722389547343 := by
  unfold tailWord_7722507
  simp only [CollatzResearch.WordTrace]
  refine ⟨281662969833683513037781775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187775313222455675358521183 281662969833683513037781775)
  ·
    refine ⟨422494454750525269556672663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281662969833683513037781775 422494454750525269556672663)
    ·
      refine ⟨633741682125787904335008995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422494454750525269556672663 633741682125787904335008995)
      ·
        refine ⟨950612523188681856502513493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633741682125787904335008995 950612523188681856502513493)
        ·
          refine ⟨5569995253058682752944415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 950612523188681856502513493 5569995253058682752944415)
          ·
            refine ⟨8354992879588024129416623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569995253058682752944415 8354992879588024129416623)
            ·
              refine ⟨12532489319382036194124935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354992879588024129416623 12532489319382036194124935)
              ·
                refine ⟨18798733979073054291187403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12532489319382036194124935 18798733979073054291187403)
                ·
                  refine ⟨28198100968609581436781105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18798733979073054291187403 28198100968609581436781105)
                  ·
                    refine ⟨21148575726457186077585829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28198100968609581436781105 21148575726457186077585829)
                    ·
                      refine ⟨3965357948710722389547343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21148575726457186077585829 3965357948710722389547343)
                      ·
                        rfl

theorem cell23_7722507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 2, 4].length) (baseStart_7722507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722507 prefixEnd_7722507 := by exact prefixLift 7722507
  have htrace : WordTrace (prefixWord ++ tailWord_7722507) baseStart_7722507 baseEnd_7722507 := by
    simpa [prefixWord, tailWord_7722507, baseEnd_7722507] using wordTrace_append hprefix tailTrace_7722507
  have hstable : (prefixWord ++ tailWord_7722507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722507).length < 2 ^ (prefixWord ++ tailWord_7722507).sum := by decide
  have hdescent : baseEnd_7722507 < baseStart_7722507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722657 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 2, 4, 2]
def baseStart_7722657 : Nat := 118140960795 + 7722657 * 2 ^ 59
def prefixEnd_7722657 : Nat := 4983230072969 + 3 ^ 40 * 7722657 * 2
def baseEnd_7722657 : Nat := 3965434970808896802671653

theorem tailTrace_7722657 : CollatzResearch.WordTrace tailWord_7722657 prefixEnd_7722657 3965434970808896802671653 := by
  unfold tailWord_7722657
  simp only [CollatzResearch.WordTrace]
  refine ⟨281668440783140088655742225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187778960522093392437161483 281668440783140088655742225)
  ·
    refine ⟨211251330587355066491806669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281668440783140088655742225 211251330587355066491806669)
    ·
      refine ⟨79219248970258149934427501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211251330587355066491806669 79219248970258149934427501)
      ·
        refine ⟨29707218363846806225410313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79219248970258149934427501 29707218363846806225410313)
        ·
          refine ⟨22280413772885104669057735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29707218363846806225410313 22280413772885104669057735)
          ·
            refine ⟨33420620659327657003586603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22280413772885104669057735 33420620659327657003586603)
            ·
              refine ⟨50130930988991485505379905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33420620659327657003586603 50130930988991485505379905)
              ·
                refine ⟨37598198241743614129034929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50130930988991485505379905 37598198241743614129034929)
                ·
                  refine ⟨28198648681307710596776197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37598198241743614129034929 28198648681307710596776197)
                  ·
                    refine ⟨5287246627745195736895537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28198648681307710596776197 5287246627745195736895537)
                    ·
                      refine ⟨3965434970808896802671653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5287246627745195736895537 3965434970808896802671653)
                      ·
                        rfl

theorem cell23_7722657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_7722657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722657 prefixEnd_7722657 := by exact prefixLift 7722657
  have htrace : WordTrace (prefixWord ++ tailWord_7722657) baseStart_7722657 baseEnd_7722657 := by
    simpa [prefixWord, tailWord_7722657, baseEnd_7722657] using wordTrace_append hprefix tailTrace_7722657
  have hstable : (prefixWord ++ tailWord_7722657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722657).length < 2 ^ (prefixWord ++ tailWord_7722657).sum := by decide
  have hdescent : baseEnd_7722657 < baseStart_7722657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722798 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_7722798 : Nat := 118140960795 + 7722798 * 2 ^ 59
def prefixEnd_7722798 : Nat := 4983230072969 + 3 ^ 40 * 7722798 * 2
def baseEnd_7722798 : Nat := 3965507371581180751008505

theorem tailTrace_7722798 : CollatzResearch.WordTrace tailWord_7722798 prefixEnd_7722798 3965507371581180751008505 := by
  unfold tailWord_7722798
  simp only [CollatzResearch.WordTrace]
  refine ⟨35209197934453658717078131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187782388983752846491083365 35209197934453658717078131)
  ·
    refine ⟨52813796901680488075617197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35209197934453658717078131 52813796901680488075617197)
    ·
      refine ⟨19805173838130183028356449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52813796901680488075617197 19805173838130183028356449)
      ·
        refine ⟨14853880378597637271267337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19805173838130183028356449 14853880378597637271267337)
        ·
          refine ⟨11140410283948227953450503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14853880378597637271267337 11140410283948227953450503)
          ·
            refine ⟨16710615425922341930175755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11140410283948227953450503 16710615425922341930175755)
            ·
              refine ⟨25065923138883512895263633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16710615425922341930175755 25065923138883512895263633)
              ·
                refine ⟨18799442354162634671447725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25065923138883512895263633 18799442354162634671447725)
                ·
                  refine ⟨7049790882810988001792897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18799442354162634671447725 7049790882810988001792897)
                  ·
                    refine ⟨5287343162108241001344673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7049790882810988001792897 5287343162108241001344673)
                    ·
                      refine ⟨3965507371581180751008505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5287343162108241001344673 3965507371581180751008505)
                      ·
                        rfl

theorem cell23_7722798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_7722798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722798 prefixEnd_7722798 := by exact prefixLift 7722798
  have htrace : WordTrace (prefixWord ++ tailWord_7722798) baseStart_7722798 baseEnd_7722798 := by
    simpa [prefixWord, tailWord_7722798, baseEnd_7722798] using wordTrace_append hprefix tailTrace_7722798
  have hstable : (prefixWord ++ tailWord_7722798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722798).length < 2 ^ (prefixWord ++ tailWord_7722798).sum := by decide
  have hdescent : baseEnd_7722798 < baseStart_7722798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722804 : List Nat := [2, 5, 1, 1, 2, 2, 3, 7]
def baseStart_7722804 : Nat := 118140960795 + 7722804 * 2 ^ 59
def prefixEnd_7722804 : Nat := 4983230072969 + 3 ^ 40 * 7722804 * 2
def baseEnd_7722804 : Nat := 146870757498707693612351

theorem tailTrace_7722804 : CollatzResearch.WordTrace tailWord_7722804 prefixEnd_7722804 146870757498707693612351 := by
  unfold tailWord_7722804
  simp only [CollatzResearch.WordTrace]
  refine ⟨140836901156803766380671733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187782534875738355174228977 140836901156803766380671733)
  ·
    refine ⟨13203459483450353098187975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140836901156803766380671733 13203459483450353098187975)
    ·
      refine ⟨19805189225175529647281963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13203459483450353098187975 19805189225175529647281963)
      ·
        refine ⟨29707783837763294470922945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19805189225175529647281963 29707783837763294470922945)
        ·
          refine ⟨22280837878322470853192209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29707783837763294470922945 22280837878322470853192209)
          ·
            refine ⟨16710628408741853139894157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22280837878322470853192209 16710628408741853139894157)
            ·
              refine ⟨6266485653278194927460309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16710628408741853139894157 6266485653278194927460309)
              ·
                refine ⟨146870757498707693612351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6266485653278194927460309 146870757498707693612351)
                ·
                  rfl

theorem cell23_7722804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 7].length) (baseStart_7722804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722804 prefixEnd_7722804 := by exact prefixLift 7722804
  have htrace : WordTrace (prefixWord ++ tailWord_7722804) baseStart_7722804 baseEnd_7722804 := by
    simpa [prefixWord, tailWord_7722804, baseEnd_7722804] using wordTrace_append hprefix tailTrace_7722804
  have hstable : (prefixWord ++ tailWord_7722804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722804).length < 2 ^ (prefixWord ++ tailWord_7722804).sum := by decide
  have hdescent : baseEnd_7722804 < baseStart_7722804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722814 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_7722814 : Nat := 118140960795 + 7722814 * 2 ^ 59
def prefixEnd_7722814 : Nat := 4983230072969 + 3 ^ 40 * 7722814 * 2
def baseEnd_7722814 : Nat := 3965515587271652688408431

theorem tailTrace_7722814 : CollatzResearch.WordTrace tailWord_7722814 prefixEnd_7722814 3965515587271652688408431 := by
  unfold tailWord_7722814
  simp only [CollatzResearch.WordTrace]
  refine ⟨35209270880446413058650937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187782778029047536312804997 35209270880446413058650937)
  ·
    refine ⟨26406953160334809793988203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35209270880446413058650937 26406953160334809793988203)
    ·
      refine ⟨39610429740502214690982305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26406953160334809793988203 39610429740502214690982305)
      ·
        refine ⟨29707822305376661018236729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39610429740502214690982305 29707822305376661018236729)
        ·
          refine ⟨22280866729032495763677547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29707822305376661018236729 22280866729032495763677547)
          ·
            refine ⟨33421300093548743645516321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22280866729032495763677547 33421300093548743645516321)
            ·
              refine ⟨25065975070161557734137241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33421300093548743645516321 25065975070161557734137241)
              ·
                refine ⟨18799481302621168300602931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25065975070161557734137241 18799481302621168300602931)
                ·
                  refine ⟨28199221953931752450904397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18799481302621168300602931 28199221953931752450904397)
                  ·
                    refine ⟨10574708232724407169089149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28199221953931752450904397 10574708232724407169089149)
                    ·
                      refine ⟨3965515587271652688408431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10574708232724407169089149 3965515587271652688408431)
                      ·
                        rfl

theorem cell23_7722814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_7722814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722814 prefixEnd_7722814 := by exact prefixLift 7722814
  have htrace : WordTrace (prefixWord ++ tailWord_7722814) baseStart_7722814 baseEnd_7722814 := by
    simpa [prefixWord, tailWord_7722814, baseEnd_7722814] using wordTrace_append hprefix tailTrace_7722814
  have hstable : (prefixWord ++ tailWord_7722814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722814).length < 2 ^ (prefixWord ++ tailWord_7722814).sum := by decide
  have hdescent : baseEnd_7722814 < baseStart_7722814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722840 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_7722840 : Nat := 118140960795 + 7722840 * 2 ^ 59
def prefixEnd_7722840 : Nat := 4983230072969 + 3 ^ 40 * 7722840 * 2
def baseEnd_7722840 : Nat := 3965528937768669586683311

theorem tailTrace_7722840 : CollatzResearch.WordTrace tailWord_7722840 prefixEnd_7722840 3965528937768669586683311 := by
  unfold tailWord_7722840
  simp only [CollatzResearch.WordTrace]
  refine ⟨140837557670738555454826987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187783410227651407273102649 140837557670738555454826987)
  ·
    refine ⟨211256336506107833182240481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140837557670738555454826987 211256336506107833182240481)
    ·
      refine ⟨158442252379580874886680361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211256336506107833182240481 158442252379580874886680361)
      ·
        refine ⟨118831689284685656165010271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158442252379580874886680361 118831689284685656165010271)
        ·
          refine ⟨178247533927028484247515407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118831689284685656165010271 178247533927028484247515407)
          ·
            refine ⟨267371300890542726371273111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178247533927028484247515407 267371300890542726371273111)
            ·
              refine ⟨401056951335814089556909667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267371300890542726371273111 401056951335814089556909667)
              ·
                refine ⟨601585427003721134335364501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401056951335814089556909667 601585427003721134335364501)
                ·
                  refine ⟨28199316890799428171970211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 601585427003721134335364501 28199316890799428171970211)
                  ·
                    refine ⟨42298975336199142257955317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28199316890799428171970211 42298975336199142257955317)
                    ·
                      refine ⟨3965528937768669586683311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42298975336199142257955317 3965528937768669586683311)
                      ·
                        rfl

theorem cell23_7722840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_7722840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722840 prefixEnd_7722840 := by exact prefixLift 7722840
  have htrace : WordTrace (prefixWord ++ tailWord_7722840) baseStart_7722840 baseEnd_7722840 := by
    simpa [prefixWord, tailWord_7722840, baseEnd_7722840] using wordTrace_append hprefix tailTrace_7722840
  have hstable : (prefixWord ++ tailWord_7722840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722840).length < 2 ^ (prefixWord ++ tailWord_7722840).sum := by decide
  have hdescent : baseEnd_7722840 < baseStart_7722840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722944 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 2, 4, 2]
def baseStart_7722944 : Nat := 118140960795 + 7722944 * 2 ^ 59
def prefixEnd_7722944 : Nat := 4983230072969 + 3 ^ 40 * 7722944 * 2
def baseEnd_7722944 : Nat := 3965582339756737179782833

theorem tailTrace_7722944 : CollatzResearch.WordTrace tailWord_7722944 prefixEnd_7722944 3965582339756737179782833 := by
  unfold tailWord_7722944
  simp only [CollatzResearch.WordTrace]
  refine ⟨140839454266550168335719943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187785939022066891114293257 140839454266550168335719943)
  ·
    refine ⟨211259181399825252503579915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140839454266550168335719943 211259181399825252503579915)
    ·
      refine ⟨316888772099737878755369873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211259181399825252503579915 316888772099737878755369873)
      ·
        refine ⟨237666579074803409066527405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316888772099737878755369873 237666579074803409066527405)
        ·
          refine ⟨89124967153051278399947777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237666579074803409066527405 89124967153051278399947777)
          ·
            refine ⟨66843725364788458799960833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89124967153051278399947777 66843725364788458799960833)
            ·
              refine ⟨50132794023591344099970625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66843725364788458799960833 50132794023591344099970625)
              ·
                refine ⟨37599595517693508074977969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50132794023591344099970625 37599595517693508074977969)
                ·
                  refine ⟨28199696638270131056233477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37599595517693508074977969 28199696638270131056233477)
                  ·
                    refine ⟨5287443119675649573043777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28199696638270131056233477 5287443119675649573043777)
                    ·
                      refine ⟨3965582339756737179782833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5287443119675649573043777 3965582339756737179782833)
                      ·
                        rfl

theorem cell23_7722944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 4, 2].length) (baseStart_7722944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722944 prefixEnd_7722944 := by exact prefixLift 7722944
  have htrace : WordTrace (prefixWord ++ tailWord_7722944) baseStart_7722944 baseEnd_7722944 := by
    simpa [prefixWord, tailWord_7722944, baseEnd_7722944] using wordTrace_append hprefix tailTrace_7722944
  have hstable : (prefixWord ++ tailWord_7722944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722944).length < 2 ^ (prefixWord ++ tailWord_7722944).sum := by decide
  have hdescent : baseEnd_7722944 < baseStart_7722944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722964 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_7722964 : Nat := 118140960795 + 7722964 * 2 ^ 59
def prefixEnd_7722964 : Nat := 4983230072969 + 3 ^ 40 * 7722964 * 2
def baseEnd_7722964 : Nat := 3965592609369827101532741

theorem tailTrace_7722964 : CollatzResearch.WordTrace tailWord_7722964 prefixEnd_7722964 3965592609369827101532741 := by
  unfold tailWord_7722964
  simp only [CollatzResearch.WordTrace]
  refine ⟨140839818996513940043583973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187786425328685253391445297 140839818996513940043583973)
  ·
    refine ⟨26407466061846363758171995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140839818996513940043583973 26407466061846363758171995)
    ·
      refine ⟨39611199092769545637257993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26407466061846363758171995 39611199092769545637257993)
      ·
        refine ⟨29708399319577159227943495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39611199092769545637257993 29708399319577159227943495)
        ·
          refine ⟨44562598979365738841915243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29708399319577159227943495 44562598979365738841915243)
          ·
            refine ⟨66843898469048608262872865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44562598979365738841915243 66843898469048608262872865)
            ·
              refine ⟨50132923851786456197154649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66843898469048608262872865 50132923851786456197154649)
              ·
                refine ⟨37599692888839842147865987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50132923851786456197154649 37599692888839842147865987)
                ·
                  refine ⟨56399539333259763221798981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37599692888839842147865987 56399539333259763221798981)
                  ·
                    refine ⟨10574913624986205604087309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56399539333259763221798981 10574913624986205604087309)
                    ·
                      refine ⟨3965592609369827101532741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10574913624986205604087309 3965592609369827101532741)
                      ·
                        rfl

theorem cell23_7722964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_7722964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722964 prefixEnd_7722964 := by exact prefixLift 7722964
  have htrace : WordTrace (prefixWord ++ tailWord_7722964) baseStart_7722964 baseEnd_7722964 := by
    simpa [prefixWord, tailWord_7722964, baseEnd_7722964] using wordTrace_append hprefix tailTrace_7722964
  have hstable : (prefixWord ++ tailWord_7722964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722964).length < 2 ^ (prefixWord ++ tailWord_7722964).sum := by decide
  have hdescent : baseEnd_7722964 < baseStart_7722964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7722967 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 6]
def baseStart_7722967 : Nat := 118140960795 + 7722967 * 2 ^ 59
def prefixEnd_7722967 : Nat := 4983230072969 + 3 ^ 40 * 7722967 * 2
def baseEnd_7722967 : Nat := 440621572201310065532803

theorem tailTrace_7722967 : CollatzResearch.WordTrace tailWord_7722967 prefixEnd_7722967 440621572201310065532803 := by
  unfold tailWord_7722967
  simp only [CollatzResearch.WordTrace]
  refine ⟨281679747412017011599527155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187786498274678007733018103 281679747412017011599527155)
  ·
    refine ⟨422519621118025517399290733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281679747412017011599527155 422519621118025517399290733)
    ·
      refine ⟨158444857919259569024734025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422519621118025517399290733 158444857919259569024734025)
      ·
        refine ⟨118833643439444676768550519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158444857919259569024734025 118833643439444676768550519)
        ·
          refine ⟨178250465159167015152825779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118833643439444676768550519 178250465159167015152825779)
          ·
            refine ⟨267375697738750522729238669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178250465159167015152825779 267375697738750522729238669)
            ·
              refine ⟨100265886652031446023464501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267375697738750522729238669 100265886652031446023464501)
              ·
                refine ⟨9399926873627948064699797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100265886652031446023464501 9399926873627948064699797)
                ·
                  refine ⟨440621572201310065532803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9399926873627948064699797 440621572201310065532803)
                  ·
                    rfl

theorem cell23_7722967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 6].length) (baseStart_7722967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7722967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7722967 prefixEnd_7722967 := by exact prefixLift 7722967
  have htrace : WordTrace (prefixWord ++ tailWord_7722967) baseStart_7722967 baseEnd_7722967 := by
    simpa [prefixWord, tailWord_7722967, baseEnd_7722967] using wordTrace_append hprefix tailTrace_7722967
  have hstable : (prefixWord ++ tailWord_7722967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7722967).length < 2 ^ (prefixWord ++ tailWord_7722967).sum := by decide
  have hdescent : baseEnd_7722967 < baseStart_7722967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7722967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723045 : List Nat := [1, 3, 1, 2, 2, 5, 1, 3, 1, 1, 3]
def baseStart_7723045 : Nat := 118140960795 + 7723045 * 2 ^ 59
def prefixEnd_7723045 : Nat := 4983230072969 + 3 ^ 40 * 7723045 * 2
def baseEnd_7723045 : Nat := 3965634201302841284619869

theorem tailTrace_7723045 : CollatzResearch.WordTrace tailWord_7723045 prefixEnd_7723045 3965634201302841284619869 := by
  unfold tailWord_7723045
  simp only [CollatzResearch.WordTrace]
  refine ⟨281682592305734430920866589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187788394870489620613911059 281682592305734430920866589)
  ·
    refine ⟨105630972114650411595324971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281682592305734430920866589 105630972114650411595324971)
    ·
      refine ⟨158446458171975617392987457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105630972114650411595324971 158446458171975617392987457)
      ·
        refine ⟨118834843628981713044740593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158446458171975617392987457 118834843628981713044740593)
        ·
          refine ⟨89126132721736284783555445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118834843628981713044740593 89126132721736284783555445)
          ·
            refine ⟨8355574942662776698458323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89126132721736284783555445 8355574942662776698458323)
            ·
              refine ⟨12533362413994165047687485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8355574942662776698458323 12533362413994165047687485)
              ·
                refine ⟨4700010905247811892882807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12533362413994165047687485 4700010905247811892882807)
                ·
                  refine ⟨7050016357871717839324211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700010905247811892882807 7050016357871717839324211)
                  ·
                    refine ⟨10575024536807576758986317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7050016357871717839324211 10575024536807576758986317)
                    ·
                      refine ⟨3965634201302841284619869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10575024536807576758986317 3965634201302841284619869)
                      ·
                        rfl

theorem cell23_7723045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_7723045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723045 prefixEnd_7723045 := by exact prefixLift 7723045
  have htrace : WordTrace (prefixWord ++ tailWord_7723045) baseStart_7723045 baseEnd_7723045 := by
    simpa [prefixWord, tailWord_7723045, baseEnd_7723045] using wordTrace_append hprefix tailTrace_7723045
  have hstable : (prefixWord ++ tailWord_7723045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723045).length < 2 ^ (prefixWord ++ tailWord_7723045).sum := by decide
  have hdescent : baseEnd_7723045 < baseStart_7723045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723057 : List Nat := [1, 2, 2, 3, 1, 3, 11]
def baseStart_7723057 : Nat := 118140960795 + 7723057 * 2 ^ 59
def prefixEnd_7723057 : Nat := 4983230072969 + 3 ^ 40 * 7723057 * 2
def baseEnd_7723057 : Nat := 48958523000872780711973

theorem tailTrace_7723057 : CollatzResearch.WordTrace tailWord_7723057 prefixEnd_7723057 48958523000872780711973 := by
  unfold tailWord_7723057
  simp only [CollatzResearch.WordTrace]
  refine ⟨281683029981690956970303425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187788686654460637980202283 281683029981690956970303425)
  ·
    refine ⟨211262272486268217727727569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281683029981690956970303425 211262272486268217727727569)
    ·
      refine ⟨158446704364701163295795677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211262272486268217727727569 158446704364701163295795677)
      ·
        refine ⟨59417514136762936235923379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158446704364701163295795677 59417514136762936235923379)
        ·
          refine ⟨89126271205144404353885069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59417514136762936235923379 89126271205144404353885069)
          ·
            refine ⟨33422351701929151632706901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89126271205144404353885069 33422351701929151632706901)
            ·
              refine ⟨48958523000872780711973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33422351701929151632706901 48958523000872780711973)
              ·
                rfl

theorem cell23_7723057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 11].length) (baseStart_7723057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723057 prefixEnd_7723057 := by exact prefixLift 7723057
  have htrace : WordTrace (prefixWord ++ tailWord_7723057) baseStart_7723057 baseEnd_7723057 := by
    simpa [prefixWord, tailWord_7723057, baseEnd_7723057] using wordTrace_append hprefix tailTrace_7723057
  have hstable : (prefixWord ++ tailWord_7723057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723057).length < 2 ^ (prefixWord ++ tailWord_7723057).sum := by decide
  have hdescent : baseEnd_7723057 < baseStart_7723057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723062 : List Nat := [5, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_7723062 : Nat := 118140960795 + 7723062 * 2 ^ 59
def prefixEnd_7723062 : Nat := 4983230072969 + 3 ^ 40 * 7723062 * 2
def baseEnd_7723062 : Nat := 3965642930473967718107291

theorem tailTrace_7723062 : CollatzResearch.WordTrace tailWord_7723062 prefixEnd_7723062 3965642930473967718107291 := by
  unfold tailWord_7723062
  simp only [CollatzResearch.WordTrace]
  refine ⟨17605200771667052676514715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187788808231115228549490293 17605200771667052676514715)
  ·
    refine ⟨26407801157500579014772073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17605200771667052676514715 26407801157500579014772073)
    ·
      refine ⟨19805850868125434261079055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26407801157500579014772073 19805850868125434261079055)
      ·
        refine ⟨29708776302188151391618583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19805850868125434261079055 29708776302188151391618583)
        ·
          refine ⟨44563164453282227087427875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29708776302188151391618583 44563164453282227087427875)
          ·
            refine ⟨66844746679923340631141813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44563164453282227087427875 66844746679923340631141813)
            ·
              refine ⟨6266695001242813184169545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66844746679923340631141813 6266695001242813184169545)
              ·
                refine ⟨4700021250932109888127159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6266695001242813184169545 4700021250932109888127159)
                ·
                  refine ⟨7050031876398164832190739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700021250932109888127159 7050031876398164832190739)
                  ·
                    refine ⟨10575047814597247248286109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7050031876398164832190739 10575047814597247248286109)
                    ·
                      refine ⟨3965642930473967718107291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10575047814597247248286109 3965642930473967718107291)
                      ·
                        rfl

theorem cell23_7723062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_7723062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723062 prefixEnd_7723062 := by exact prefixLift 7723062
  have htrace : WordTrace (prefixWord ++ tailWord_7723062) baseStart_7723062 baseEnd_7723062 := by
    simpa [prefixWord, tailWord_7723062, baseEnd_7723062] using wordTrace_append hprefix tailTrace_7723062
  have hstable : (prefixWord ++ tailWord_7723062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723062).length < 2 ^ (prefixWord ++ tailWord_7723062).sum := by decide
  have hdescent : baseEnd_7723062 < baseStart_7723062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723077 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_7723077 : Nat := 118140960795 + 7723077 * 2 ^ 59
def prefixEnd_7723077 : Nat := 4983230072969 + 3 ^ 40 * 7723077 * 2
def baseEnd_7723077 : Nat := 3965650632683785159419721

theorem tailTrace_7723077 : CollatzResearch.WordTrace tailWord_7723077 prefixEnd_7723077 3965650632683785159419721 := by
  unfold tailWord_7723077
  simp only [CollatzResearch.WordTrace]
  refine ⟨281683759441618500386031485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187789172961079000257354323 281683759441618500386031485)
  ·
    refine ⟨105631409790606937644761807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281683759441618500386031485 105631409790606937644761807)
    ·
      refine ⟨158447114685910406467142711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105631409790606937644761807 158447114685910406467142711)
      ·
        refine ⟨237670672028865609700714067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158447114685910406467142711 237670672028865609700714067)
        ·
          refine ⟨356506008043298414551071101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237670672028865609700714067 356506008043298414551071101)
          ·
            refine ⟨133689753016236905456651663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356506008043298414551071101 133689753016236905456651663)
            ·
              refine ⟨200534629524355358184977495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133689753016236905456651663 200534629524355358184977495)
              ·
                refine ⟨300801944286533037277466243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200534629524355358184977495 300801944286533037277466243)
                ·
                  refine ⟨451202916429799555916199365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300801944286533037277466243 451202916429799555916199365)
                  ·
                    refine ⟨84600546830587416734287381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 451202916429799555916199365 84600546830587416734287381)
                    ·
                      refine ⟨3965650632683785159419721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84600546830587416734287381 3965650632683785159419721)
                      ·
                        rfl

theorem cell23_7723077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_7723077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723077 prefixEnd_7723077 := by exact prefixLift 7723077
  have htrace : WordTrace (prefixWord ++ tailWord_7723077) baseStart_7723077 baseEnd_7723077 := by
    simpa [prefixWord, tailWord_7723077, baseEnd_7723077] using wordTrace_append hprefix tailTrace_7723077
  have hstable : (prefixWord ++ tailWord_7723077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723077).length < 2 ^ (prefixWord ++ tailWord_7723077).sum := by decide
  have hdescent : baseEnd_7723077 < baseStart_7723077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723087 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 2, 7]
def baseStart_7723087 : Nat := 118140960795 + 7723087 * 2 ^ 59
def prefixEnd_7723087 : Nat := 4983230072969 + 3 ^ 40 * 7723087 * 2
def baseEnd_7723087 : Nat := 1321885255830110040098225

theorem tailTrace_7723087 : CollatzResearch.WordTrace tailWord_7723087 prefixEnd_7723087 1321885255830110040098225 := by
  unfold tailWord_7723087
  simp only [CollatzResearch.WordTrace]
  refine ⟨281684124171582272093895515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187789416114388181395930343 281684124171582272093895515)
  ·
    refine ⟨422526186257373408140843273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281684124171582272093895515 422526186257373408140843273)
    ·
      refine ⟨316894639693030056105632455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422526186257373408140843273 316894639693030056105632455)
      ·
        refine ⟨475341959539545084158448683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316894639693030056105632455 475341959539545084158448683)
        ·
          refine ⟨713012939309317626237673025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475341959539545084158448683 713012939309317626237673025)
          ·
            refine ⟨534759704481988219678254769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713012939309317626237673025 534759704481988219678254769)
            ·
              refine ⟨401069778361491164758691077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534759704481988219678254769 401069778361491164758691077)
              ·
                refine ⟨75200583442779593392254577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401069778361491164758691077 75200583442779593392254577)
                ·
                  refine ⟨56400437582084695044190933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75200583442779593392254577 56400437582084695044190933)
                  ·
                    refine ⟨1321885255830110040098225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56400437582084695044190933 1321885255830110040098225)
                    ·
                      rfl

theorem cell23_7723087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_7723087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723087 prefixEnd_7723087 := by exact prefixLift 7723087
  have htrace : WordTrace (prefixWord ++ tailWord_7723087) baseStart_7723087 baseEnd_7723087 := by
    simpa [prefixWord, tailWord_7723087, baseEnd_7723087] using wordTrace_append hprefix tailTrace_7723087
  have hstable : (prefixWord ++ tailWord_7723087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723087).length < 2 ^ (prefixWord ++ tailWord_7723087).sum := by decide
  have hdescent : baseEnd_7723087 < baseStart_7723087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723164 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 9]
def baseStart_7723164 : Nat := 118140960795 + 7723164 * 2 ^ 59
def prefixEnd_7723164 : Nat := 4983230072969 + 3 ^ 40 * 7723164 * 2
def baseEnd_7723164 : Nat := 440632811722302924336869

theorem tailTrace_7723164 : CollatzResearch.WordTrace tailWord_7723164 prefixEnd_7723164 440632811722302924336869 := by
  unfold tailWord_7723164
  simp only [CollatzResearch.WordTrace]
  refine ⟨140843466296151657122224273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187791288394868876162965697 140843466296151657122224273)
  ·
    refine ⟨105632599722113742841668205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140843466296151657122224273 105632599722113742841668205)
    ·
      refine ⟨39612224895792653565625577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105632599722113742841668205 39612224895792653565625577)
      ·
        refine ⟨29709168671844490174219183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39612224895792653565625577 29709168671844490174219183)
        ·
          refine ⟨44563753007766735261328775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29709168671844490174219183 44563753007766735261328775)
          ·
            refine ⟨66845629511650102891993163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44563753007766735261328775 66845629511650102891993163)
            ·
              refine ⟨100268444267475154337989745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66845629511650102891993163 100268444267475154337989745)
              ·
                refine ⟨75201333200606365753492309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100268444267475154337989745 75201333200606365753492309)
                ·
                  refine ⟨440632811722302924336869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75201333200606365753492309 440632811722302924336869)
                  ·
                    rfl

theorem cell23_7723164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_7723164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723164 prefixEnd_7723164 := by exact prefixLift 7723164
  have htrace : WordTrace (prefixWord ++ tailWord_7723164) baseStart_7723164 baseEnd_7723164 := by
    simpa [prefixWord, tailWord_7723164, baseEnd_7723164] using wordTrace_append hprefix tailTrace_7723164
  have hstable : (prefixWord ++ tailWord_7723164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723164).length < 2 ^ (prefixWord ++ tailWord_7723164).sum := by decide
  have hdescent : baseEnd_7723164 < baseStart_7723164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723181 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 7]
def baseStart_7723181 : Nat := 118140960795 + 7723181 * 2 ^ 59
def prefixEnd_7723181 : Nat := 4983230072969 + 3 ^ 40 * 7723181 * 2
def baseEnd_7723181 : Nat := 440633781630205861391027

theorem tailTrace_7723181 : CollatzResearch.WordTrace tailWord_7723181 prefixEnd_7723181 440633781630205861391027 := by
  unfold tailWord_7723181
  simp only [CollatzResearch.WordTrace]
  refine ⟨281687552633241726147817397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187791701755494484098544931 281687552633241726147817397)
  ·
    refine ⟨26408208059366411826357881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281687552633241726147817397 26408208059366411826357881)
    ·
      refine ⟨19806156044524808869768411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26408208059366411826357881 19806156044524808869768411)
      ·
        refine ⟨29709234066787213304652617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19806156044524808869768411 29709234066787213304652617)
        ·
          refine ⟨22281925550090409978489463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29709234066787213304652617 22281925550090409978489463)
          ·
            refine ⟨33422888325135614967734195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22281925550090409978489463 33422888325135614967734195)
            ·
              refine ⟨50134332487703422451601293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33422888325135614967734195 50134332487703422451601293)
              ·
                refine ⟨18800374682888783419350485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50134332487703422451601293 18800374682888783419350485)
                ·
                  refine ⟨440633781630205861391027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18800374682888783419350485 440633781630205861391027)
                  ·
                    rfl

theorem cell23_7723181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_7723181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723181 prefixEnd_7723181 := by exact prefixLift 7723181
  have htrace : WordTrace (prefixWord ++ tailWord_7723181) baseStart_7723181 baseEnd_7723181 := by
    simpa [prefixWord, tailWord_7723181, baseEnd_7723181] using wordTrace_append hprefix tailTrace_7723181
  have hstable : (prefixWord ++ tailWord_7723181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723181).length < 2 ^ (prefixWord ++ tailWord_7723181).sum := by decide
  have hdescent : baseEnd_7723181 < baseStart_7723181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723191 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 3]
def baseStart_7723191 : Nat := 118140960795 + 7723191 * 2 ^ 59
def prefixEnd_7723191 : Nat := 4983230072969 + 3 ^ 40 * 7723191 * 2
def baseEnd_7723191 : Nat := 3965709169478397713394197

theorem tailTrace_7723191 : CollatzResearch.WordTrace tailWord_7723191 prefixEnd_7723191 3965709169478397713394197 := by
  unfold tailWord_7723191
  simp only [CollatzResearch.WordTrace]
  refine ⟨281687917363205497855681427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187791944908803665237120951 281687917363205497855681427)
  ·
    refine ⟨422531876044808246783522141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281687917363205497855681427 422531876044808246783522141)
    ·
      refine ⟨158449453516803092543820803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422531876044808246783522141 158449453516803092543820803)
      ·
        refine ⟨237674180275204638815731205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158449453516803092543820803 237674180275204638815731205)
        ·
          refine ⟨44563908801600869777949601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237674180275204638815731205 44563908801600869777949601)
          ·
            refine ⟨33422931601200652333462201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44563908801600869777949601 33422931601200652333462201)
            ·
              refine ⟨25067198700900489250096651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33422931601200652333462201 25067198700900489250096651)
              ·
                refine ⟨37600798051350733875144977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25067198700900489250096651 37600798051350733875144977)
                ·
                  refine ⟨28200598538513050406358733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37600798051350733875144977 28200598538513050406358733)
                  ·
                    refine ⟨10575224451942393902384525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28200598538513050406358733 10575224451942393902384525)
                    ·
                      refine ⟨3965709169478397713394197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10575224451942393902384525 3965709169478397713394197)
                      ·
                        rfl

theorem cell23_7723191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_7723191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723191 prefixEnd_7723191 := by exact prefixLift 7723191
  have htrace : WordTrace (prefixWord ++ tailWord_7723191) baseStart_7723191 baseEnd_7723191 := by
    simpa [prefixWord, tailWord_7723191, baseEnd_7723191] using wordTrace_append hprefix tailTrace_7723191
  have hstable : (prefixWord ++ tailWord_7723191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723191).length < 2 ^ (prefixWord ++ tailWord_7723191).sum := by decide
  have hdescent : baseEnd_7723191 < baseStart_7723191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723194 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_7723194 : Nat := 118140960795 + 7723194 * 2 ^ 59
def prefixEnd_7723194 : Nat := 4983230072969 + 3 ^ 40 * 7723194 * 2
def baseEnd_7723194 : Nat := 1321903569973453733885561

theorem tailTrace_7723194 : CollatzResearch.WordTrace tailWord_7723194 prefixEnd_7723194 1321903569973453733885561 := by
  unfold tailWord_7723194
  simp only [CollatzResearch.WordTrace]
  refine ⟨70422006695548657342010159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187792017854796419578693757 70422006695548657342010159)
  ·
    refine ⟨105633010043322986013015239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70422006695548657342010159 105633010043322986013015239)
    ·
      refine ⟨158449515064984479019522859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105633010043322986013015239 158449515064984479019522859)
      ·
        refine ⟨237674272597476718529284289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158449515064984479019522859 237674272597476718529284289)
        ·
          refine ⟨178255704448107538896963217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237674272597476718529284289 178255704448107538896963217)
          ·
            refine ⟨133691778336080654172722413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178255704448107538896963217 133691778336080654172722413)
            ·
              refine ⟨50134416876030245314770905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133691778336080654172722413 50134416876030245314770905)
              ·
                refine ⟨37600812657022683986078179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50134416876030245314770905 37600812657022683986078179)
                ·
                  refine ⟨56401218985534025979117269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37600812657022683986078179 56401218985534025979117269)
                  ·
                    refine ⟨1321903569973453733885561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56401218985534025979117269 1321903569973453733885561)
                    ·
                      rfl

theorem cell23_7723194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_7723194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723194 prefixEnd_7723194 := by exact prefixLift 7723194
  have htrace : WordTrace (prefixWord ++ tailWord_7723194) baseStart_7723194 baseEnd_7723194 := by
    simpa [prefixWord, tailWord_7723194, baseEnd_7723194] using wordTrace_append hprefix tailTrace_7723194
  have hstable : (prefixWord ++ tailWord_7723194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723194).length < 2 ^ (prefixWord ++ tailWord_7723194).sum := by decide
  have hdescent : baseEnd_7723194 < baseStart_7723194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723251 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 3]
def baseStart_7723251 : Nat := 118140960795 + 7723251 * 2 ^ 59
def prefixEnd_7723251 : Nat := 4983230072969 + 3 ^ 40 * 7723251 * 2
def baseEnd_7723251 : Nat := 3965739978317667478643921

theorem tailTrace_7723251 : CollatzResearch.WordTrace tailWord_7723251 prefixEnd_7723251 3965739978317667478643921 := by
  unfold tailWord_7723251
  simp only [CollatzResearch.WordTrace]
  refine ⟨281690105742988128102865607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187793403828658752068577071 281690105742988128102865607)
  ·
    refine ⟨422535158614482192154298411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281690105742988128102865607 422535158614482192154298411)
    ·
      refine ⟨633802737921723288231447617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422535158614482192154298411 633802737921723288231447617)
      ·
        refine ⟨475352053441292466173585713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633802737921723288231447617 475352053441292466173585713)
        ·
          refine ⟨356514040080969349630189285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475352053441292466173585713 356514040080969349630189285)
          ·
            refine ⟨66846382515181753055660491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356514040080969349630189285 66846382515181753055660491)
            ·
              refine ⟨100269573772772629583490737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66846382515181753055660491 100269573772772629583490737)
              ·
                refine ⟨75202180329579472187618053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100269573772772629583490737 75202180329579472187618053)
                ·
                  refine ⟨14100408811796151035178385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75202180329579472187618053 14100408811796151035178385)
                  ·
                    refine ⟨10575306608847113276383789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14100408811796151035178385 10575306608847113276383789)
                    ·
                      refine ⟨3965739978317667478643921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10575306608847113276383789 3965739978317667478643921)
                      ·
                        rfl

theorem cell23_7723251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 3].length) (baseStart_7723251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723251 prefixEnd_7723251 := by exact prefixLift 7723251
  have htrace : WordTrace (prefixWord ++ tailWord_7723251) baseStart_7723251 baseEnd_7723251 := by
    simpa [prefixWord, tailWord_7723251, baseEnd_7723251] using wordTrace_append hprefix tailTrace_7723251
  have hstable : (prefixWord ++ tailWord_7723251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723251).length < 2 ^ (prefixWord ++ tailWord_7723251).sum := by decide
  have hdescent : baseEnd_7723251 < baseStart_7723251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723308 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 4, 3, 2]
def baseStart_7723308 : Nat := 118140960795 + 7723308 * 2 ^ 59
def prefixEnd_7723308 : Nat := 4983230072969 + 3 ^ 40 * 7723308 * 2
def baseEnd_7723308 : Nat := 3965769246714973755631159

theorem tailTrace_7723308 : CollatzResearch.WordTrace tailWord_7723308 prefixEnd_7723308 3965769246714973755631159 := by
  unfold tailWord_7723308
  simp only [CollatzResearch.WordTrace]
  refine ⟨140846092351890813418845289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187794789802521084558460385 140846092351890813418845289)
  ·
    refine ⟨105634569263918110064133967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140846092351890813418845289 105634569263918110064133967)
    ·
      refine ⟨158451853895877165096200951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105634569263918110064133967 158451853895877165096200951)
      ·
        refine ⟨237677780843815747644301427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158451853895877165096200951 237677780843815747644301427)
        ·
          refine ⟨356516671265723621466452141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237677780843815747644301427 356516671265723621466452141)
          ·
            refine ⟨133693751724646358049919553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356516671265723621466452141 133693751724646358049919553)
            ·
              refine ⟨100270313793484768537439665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133693751724646358049919553 100270313793484768537439665)
              ·
                refine ⟨75202735345113576403079749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100270313793484768537439665 75202735345113576403079749)
                ·
                  refine ⟨14100512877208795575577453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75202735345113576403079749 14100512877208795575577453)
                  ·
                    refine ⟨5287692328953298340841545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14100512877208795575577453 5287692328953298340841545)
                    ·
                      refine ⟨3965769246714973755631159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5287692328953298340841545 3965769246714973755631159)
                      ·
                        rfl

theorem cell23_7723308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 3, 2].length) (baseStart_7723308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723308 prefixEnd_7723308 := by exact prefixLift 7723308
  have htrace : WordTrace (prefixWord ++ tailWord_7723308) baseStart_7723308 baseEnd_7723308 := by
    simpa [prefixWord, tailWord_7723308, baseEnd_7723308] using wordTrace_append hprefix tailTrace_7723308
  have hstable : (prefixWord ++ tailWord_7723308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723308).length < 2 ^ (prefixWord ++ tailWord_7723308).sum := by decide
  have hdescent : baseEnd_7723308 < baseStart_7723308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723331 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 1, 6]
def baseStart_7723331 : Nat := 118140960795 + 7723331 * 2 ^ 59
def prefixEnd_7723331 : Nat := 4983230072969 + 3 ^ 40 * 7723331 * 2
def baseEnd_7723331 : Nat := 1321927018923342388547851

theorem tailTrace_7723331 : CollatzResearch.WordTrace tailWord_7723331 prefixEnd_7723331 1321927018923342388547851 := by
  unfold tailWord_7723331
  simp only [CollatzResearch.WordTrace]
  refine ⟨281693023582698301765777847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187795349055132201177185231 281693023582698301765777847)
  ·
    refine ⟨422539535374047452648666771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281693023582698301765777847 422539535374047452648666771)
    ·
      refine ⟨633809303061071178973000157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422539535374047452648666771 633809303061071178973000157)
      ·
        refine ⟨237678488647901692114875059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 633809303061071178973000157 237678488647901692114875059)
        ·
          refine ⟨356517732971852538172312589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237678488647901692114875059 356517732971852538172312589)
          ·
            refine ⟨133694149864444701814617221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356517732971852538172312589 133694149864444701814617221)
            ·
              refine ⟨25067653099583381590240729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133694149864444701814617221 25067653099583381590240729)
              ·
                refine ⟨18800739824687536192680547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25067653099583381590240729 18800739824687536192680547)
                ·
                  refine ⟨28201109737031304289020821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18800739824687536192680547 28201109737031304289020821)
                  ·
                    refine ⟨1321927018923342388547851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28201109737031304289020821 1321927018923342388547851)
                    ·
                      rfl

theorem cell23_7723331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 6].length) (baseStart_7723331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723331 prefixEnd_7723331 := by exact prefixLift 7723331
  have htrace : WordTrace (prefixWord ++ tailWord_7723331) baseStart_7723331 baseEnd_7723331 := by
    simpa [prefixWord, tailWord_7723331, baseEnd_7723331] using wordTrace_append hprefix tailTrace_7723331
  have hstable : (prefixWord ++ tailWord_7723331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723331).length < 2 ^ (prefixWord ++ tailWord_7723331).sum := by decide
  have hdescent : baseEnd_7723331 < baseStart_7723331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723351 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_7723351 : Nat := 118140960795 + 7723351 * 2 ^ 59
def prefixEnd_7723351 : Nat := 4983230072969 + 3 ^ 40 * 7723351 * 2
def baseEnd_7723351 : Nat := 3965791326383117087393461

theorem tailTrace_7723351 : CollatzResearch.WordTrace tailWord_7723351 prefixEnd_7723351 3965791326383117087393461 := by
  unfold tailWord_7723351
  simp only [CollatzResearch.WordTrace]
  refine ⟨281693753042625845181505907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187795835361750563454337271 281693753042625845181505907)
  ·
    refine ⟨422540629563938767772258861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281693753042625845181505907 422540629563938767772258861)
    ·
      refine ⟨158452736086477037914597073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422540629563938767772258861 158452736086477037914597073)
      ·
        refine ⟨118839552064857778435947805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158452736086477037914597073 118839552064857778435947805)
        ·
          refine ⟨44564832024321666913480427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118839552064857778435947805 44564832024321666913480427)
          ·
            refine ⟨66847248036482500370220641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44564832024321666913480427 66847248036482500370220641)
            ·
              refine ⟨50135436027361875277665481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66847248036482500370220641 50135436027361875277665481)
              ·
                refine ⟨37601577020521406458249111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50135436027361875277665481 37601577020521406458249111)
                ·
                  refine ⟨56402365530782109687373667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37601577020521406458249111 56402365530782109687373667)
                  ·
                    refine ⟨84603548296173164531060501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56402365530782109687373667 84603548296173164531060501)
                    ·
                      refine ⟨3965791326383117087393461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84603548296173164531060501 3965791326383117087393461)
                      ·
                        rfl

theorem cell23_7723351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_7723351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723351 prefixEnd_7723351 := by exact prefixLift 7723351
  have htrace : WordTrace (prefixWord ++ tailWord_7723351) baseStart_7723351 baseEnd_7723351 := by
    simpa [prefixWord, tailWord_7723351, baseEnd_7723351] using wordTrace_append hprefix tailTrace_7723351
  have hstable : (prefixWord ++ tailWord_7723351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723351).length < 2 ^ (prefixWord ++ tailWord_7723351).sum := by decide
  have hdescent : baseEnd_7723351 < baseStart_7723351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723368 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7723368 : Nat := 118140960795 + 7723368 * 2 ^ 59
def prefixEnd_7723368 : Nat := 4983230072969 + 3 ^ 40 * 7723368 * 2
def baseEnd_7723368 : Nat := 3965800055554243520880883

theorem tailTrace_7723368 : CollatzResearch.WordTrace tailWord_7723368 prefixEnd_7723368 3965800055554243520880883 := by
  unfold tailWord_7723368
  simp only [CollatzResearch.WordTrace]
  refine ⟨140847186541782128542437379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187796248722376171389916505 140847186541782128542437379)
  ·
    refine ⟨211270779812673192813656069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140847186541782128542437379 211270779812673192813656069)
    ·
      refine ⟨39613271214876223652560513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211270779812673192813656069 39613271214876223652560513)
      ·
        refine ⟨29709953411157167739420385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39613271214876223652560513 29709953411157167739420385)
        ·
          refine ⟨22282465058367875804565289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29709953411157167739420385 22282465058367875804565289)
          ·
            refine ⟨16711848793775906853423967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22282465058367875804565289 16711848793775906853423967)
            ·
              refine ⟨25067773190663860280135951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16711848793775906853423967 25067773190663860280135951)
              ·
                refine ⟨37601659785995790420203927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25067773190663860280135951 37601659785995790420203927)
                ·
                  refine ⟨56402489678993685630305891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37601659785995790420203927 56402489678993685630305891)
                  ·
                    refine ⟨84603734518490528445458837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56402489678993685630305891 84603734518490528445458837)
                    ·
                      refine ⟨3965800055554243520880883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84603734518490528445458837 3965800055554243520880883)
                      ·
                        rfl

theorem cell23_7723368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7723368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723368 prefixEnd_7723368 := by exact prefixLift 7723368
  have htrace : WordTrace (prefixWord ++ tailWord_7723368) baseStart_7723368 baseEnd_7723368 := by
    simpa [prefixWord, tailWord_7723368, baseEnd_7723368] using wordTrace_append hprefix tailTrace_7723368
  have hstable : (prefixWord ++ tailWord_7723368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723368).length < 2 ^ (prefixWord ++ tailWord_7723368).sum := by decide
  have hdescent : baseEnd_7723368 < baseStart_7723368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723378 : List Nat := [3, 2, 1, 2, 1, 3, 4, 7]
def baseStart_7723378 : Nat := 118140960795 + 7723378 * 2 ^ 59
def prefixEnd_7723378 : Nat := 4983230072969 + 3 ^ 40 * 7723378 * 2
def baseEnd_7723378 : Nat := 146881673717066240065031

theorem tailTrace_7723378 : CollatzResearch.WordTrace tailWord_7723378 prefixEnd_7723378 146881673717066240065031 := by
  unfold tailWord_7723378
  simp only [CollatzResearch.WordTrace]
  refine ⟨70423684453382007198184697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187796491875685352528492525 70423684453382007198184697)
  ·
    refine ⟨52817763340036505398638523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70423684453382007198184697 52817763340036505398638523)
    ·
      refine ⟨79226645010054758097957785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52817763340036505398638523 79226645010054758097957785)
      ·
        refine ⟨59419983757541068573468339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79226645010054758097957785 59419983757541068573468339)
        ·
          refine ⟨89129975636311602860202509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59419983757541068573468339 89129975636311602860202509)
          ·
            refine ⟨33423740863616851072575941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89129975636311602860202509 33423740863616851072575941)
            ·
              refine ⟨6266951411928159576107989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33423740863616851072575941 6266951411928159576107989)
              ·
                refine ⟨146881673717066240065031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6266951411928159576107989 146881673717066240065031)
                ·
                  rfl

theorem cell23_7723378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 7].length) (baseStart_7723378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723378 prefixEnd_7723378 := by exact prefixLift 7723378
  have htrace : WordTrace (prefixWord ++ tailWord_7723378) baseStart_7723378 baseEnd_7723378 := by
    simpa [prefixWord, tailWord_7723378, baseEnd_7723378] using wordTrace_append hprefix tailTrace_7723378
  have hstable : (prefixWord ++ tailWord_7723378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723378).length < 2 ^ (prefixWord ++ tailWord_7723378).sum := by decide
  have hdescent : baseEnd_7723378 < baseStart_7723378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723389 : List Nat := [1, 4, 1, 1, 2, 3, 3, 3, 1, 2, 2]
def baseStart_7723389 : Nat := 118140960795 + 7723389 * 2 ^ 59
def prefixEnd_7723389 : Nat := 4983230072969 + 3 ^ 40 * 7723389 * 2
def baseEnd_7723389 : Nat := 3965810838647987938718287

theorem tailTrace_7723389 : CollatzResearch.WordTrace tailWord_7723389 prefixEnd_7723389 3965810838647987938718287 := by
  unfold tailWord_7723389
  simp only [CollatzResearch.WordTrace]
  refine ⟨281695139016488177671389221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187796759344325451780926147 281695139016488177671389221)
  ·
    refine ⟨52817838565591533313385479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281695139016488177671389221 52817838565591533313385479)
    ·
      refine ⟨79226757848387299970078219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52817838565591533313385479 79226757848387299970078219)
      ·
        refine ⟨118840136772580949955117329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79226757848387299970078219 118840136772580949955117329)
        ·
          refine ⟨89130102579435712466337997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118840136772580949955117329 89130102579435712466337997)
          ·
            refine ⟨33423788467288392174876749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89130102579435712466337997 33423788467288392174876749)
            ·
              refine ⟨12533920675233147065578781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33423788467288392174876749 12533920675233147065578781)
              ·
                refine ⟨4700220253212430149592043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12533920675233147065578781 4700220253212430149592043)
                ·
                  refine ⟨7050330379818645224388065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700220253212430149592043 7050330379818645224388065)
                  ·
                    refine ⟨5287747784863983918291049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7050330379818645224388065 5287747784863983918291049)
                    ·
                      refine ⟨3965810838647987938718287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5287747784863983918291049 3965810838647987938718287)
                      ·
                        rfl

theorem cell23_7723389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_7723389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723389 prefixEnd_7723389 := by exact prefixLift 7723389
  have htrace : WordTrace (prefixWord ++ tailWord_7723389) baseStart_7723389 baseEnd_7723389 := by
    simpa [prefixWord, tailWord_7723389, baseEnd_7723389] using wordTrace_append hprefix tailTrace_7723389
  have hstable : (prefixWord ++ tailWord_7723389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723389).length < 2 ^ (prefixWord ++ tailWord_7723389).sum := by decide
  have hdescent : baseEnd_7723389 < baseStart_7723389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723449 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 1, 3, 2]
def baseStart_7723449 : Nat := 118140960795 + 7723449 * 2 ^ 59
def prefixEnd_7723449 : Nat := 4983230072969 + 3 ^ 40 * 7723449 * 2
def baseEnd_7723449 : Nat := 3965841647487257703968011

theorem tailTrace_7723449 : CollatzResearch.WordTrace tailWord_7723449 prefixEnd_7723449 3965841647487257703968011 := by
  unfold tailWord_7723449
  simp only [CollatzResearch.WordTrace]
  refine ⟨281697327396270807918573401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187798218264180538612382267 281697327396270807918573401)
  ·
    refine ⟨211272995547203105938930051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281697327396270807918573401 211272995547203105938930051)
    ·
      refine ⟨316909493320804658908395077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211272995547203105938930051 316909493320804658908395077)
      ·
        refine ⟨59420529997650873545324077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316909493320804658908395077 59420529997650873545324077)
        ·
          refine ⟨22282698749119077579496529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59420529997650873545324077 22282698749119077579496529)
          ·
            refine ⟨16712024061839308184622397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22282698749119077579496529 16712024061839308184622397)
            ·
              refine ⟨6267009023189740569233399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16712024061839308184622397 6267009023189740569233399)
              ·
                refine ⟨9400513534784610853850099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6267009023189740569233399 9400513534784610853850099)
                ·
                  refine ⟨14100770302176916280775149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9400513534784610853850099 14100770302176916280775149)
                  ·
                    refine ⟨5287788863316343605290681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14100770302176916280775149 5287788863316343605290681)
                    ·
                      refine ⟨3965841647487257703968011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5287788863316343605290681 3965841647487257703968011)
                      ·
                        rfl

theorem cell23_7723449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_7723449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723449 prefixEnd_7723449 := by exact prefixLift 7723449
  have htrace : WordTrace (prefixWord ++ tailWord_7723449) baseStart_7723449 baseEnd_7723449 := by
    simpa [prefixWord, tailWord_7723449, baseEnd_7723449] using wordTrace_append hprefix tailTrace_7723449
  have hstable : (prefixWord ++ tailWord_7723449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723449).length < 2 ^ (prefixWord ++ tailWord_7723449).sum := by decide
  have hdescent : baseEnd_7723449 < baseStart_7723449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723457 : List Nat := [1, 2, 7, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7723457 : Nat := 118140960795 + 7723457 * 2 ^ 59
def prefixEnd_7723457 : Nat := 4983230072969 + 3 ^ 40 * 7723457 * 2
def baseEnd_7723457 : Nat := 3965845755332493672667975

theorem tailTrace_7723457 : CollatzResearch.WordTrace tailWord_7723457 prefixEnd_7723457 3965845755332493672667975 := by
  unfold tailWord_7723457
  simp only [CollatzResearch.WordTrace]
  refine ⟨281697619180241825284864625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187798412786827883523243083 281697619180241825284864625)
  ·
    refine ⟨211273214385181368963648469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281697619180241825284864625 211273214385181368963648469)
    ·
      refine ⟨4951715962152688335085511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 211273214385181368963648469 4951715962152688335085511)
      ·
        refine ⟨7427573943229032502628267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4951715962152688335085511 7427573943229032502628267)
        ·
          refine ⟨11141360914843548753942401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7427573943229032502628267 11141360914843548753942401)
          ·
            refine ⟨8356020686132661565456801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11141360914843548753942401 8356020686132661565456801)
            ·
              refine ⟨6267015514599496174092601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8356020686132661565456801 6267015514599496174092601)
              ·
                refine ⟨4700261635949622130569451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6267015514599496174092601 4700261635949622130569451)
                ·
                  refine ⟨7050392453924433195854177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700261635949622130569451 7050392453924433195854177)
                  ·
                    refine ⟨5287794340443324896890633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7050392453924433195854177 5287794340443324896890633)
                    ·
                      refine ⟨3965845755332493672667975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5287794340443324896890633 3965845755332493672667975)
                      ·
                        rfl

theorem cell23_7723457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7723457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723457 prefixEnd_7723457 := by exact prefixLift 7723457
  have htrace : WordTrace (prefixWord ++ tailWord_7723457) baseStart_7723457 baseEnd_7723457 := by
    simpa [prefixWord, tailWord_7723457, baseEnd_7723457] using wordTrace_append hprefix tailTrace_7723457
  have hstable : (prefixWord ++ tailWord_7723457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723457).length < 2 ^ (prefixWord ++ tailWord_7723457).sum := by decide
  have hdescent : baseEnd_7723457 < baseStart_7723457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723471 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_7723471 : Nat := 118140960795 + 7723471 * 2 ^ 59
def prefixEnd_7723471 : Nat := 4983230072969 + 3 ^ 40 * 7723471 * 2
def baseEnd_7723471 : Nat := 3965852944061656617892909

theorem tailTrace_7723471 : CollatzResearch.WordTrace tailWord_7723471 prefixEnd_7723471 3965852944061656617892909 := by
  unfold tailWord_7723471
  simp only [CollatzResearch.WordTrace]
  refine ⟨281698129802191105675874267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187798753201460737117249511 281698129802191105675874267)
  ·
    refine ⟨422547194703286658513811401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281698129802191105675874267 422547194703286658513811401)
    ·
      refine ⟨316910396027464993885358551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422547194703286658513811401 316910396027464993885358551)
      ·
        refine ⟨475365594041197490828037827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316910396027464993885358551 475365594041197490828037827)
        ·
          refine ⟨713048391061796236242056741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475365594041197490828037827 713048391061796236242056741)
          ·
            refine ⟨133696573324086794295385639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 713048391061796236242056741 133696573324086794295385639)
            ·
              refine ⟨200544859986130191443078459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133696573324086794295385639 200544859986130191443078459)
              ·
                refine ⟨300817289979195287164617689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200544859986130191443078459 300817289979195287164617689)
                ·
                  refine ⟨225612967484396465373463267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300817289979195287164617689 225612967484396465373463267)
                  ·
                    refine ⟨338419451226594698060194901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225612967484396465373463267 338419451226594698060194901)
                    ·
                      refine ⟨3965852944061656617892909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 338419451226594698060194901 3965852944061656617892909)
                      ·
                        rfl

theorem cell23_7723471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_7723471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723471 prefixEnd_7723471 := by exact prefixLift 7723471
  have htrace : WordTrace (prefixWord ++ tailWord_7723471) baseStart_7723471 baseEnd_7723471 := by
    simpa [prefixWord, tailWord_7723471, baseEnd_7723471] using wordTrace_append hprefix tailTrace_7723471
  have hstable : (prefixWord ++ tailWord_7723471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723471).length < 2 ^ (prefixWord ++ tailWord_7723471).sum := by decide
  have hdescent : baseEnd_7723471 < baseStart_7723471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723502 : List Nat := [4, 1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_7723502 : Nat := 118140960795 + 7723502 * 2 ^ 59
def prefixEnd_7723502 : Nat := 4983230072969 + 3 ^ 40 * 7723502 * 2
def baseEnd_7723502 : Nat := 440652095773549555178363

theorem tailTrace_7723502 : CollatzResearch.WordTrace tailWord_7723502 prefixEnd_7723502 440652095773549555178363 := by
  unfold tailWord_7723502
  simp only [CollatzResearch.WordTrace]
  refine ⟨35212407558134849746281595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187799506976719198646835173 35212407558134849746281595)
  ·
    refine ⟨52818611337202274619422393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35212407558134849746281595 52818611337202274619422393)
    ·
      refine ⟨39613958502901705964566795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52818611337202274619422393 39613958502901705964566795)
      ·
        refine ⟨59420937754352558946850193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39613958502901705964566795 59420937754352558946850193)
        ·
          refine ⟨44565703315764419210137645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59420937754352558946850193 44565703315764419210137645)
          ·
            refine ⟨16712138743411657203801617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44565703315764419210137645 16712138743411657203801617)
            ·
              refine ⟨12534104057558742902851213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16712138743411657203801617 12534104057558742902851213)
              ·
                refine ⟨4700289021584528588569205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12534104057558742902851213 4700289021584528588569205)
                ·
                  refine ⟨440652095773549555178363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4700289021584528588569205 440652095773549555178363)
                  ·
                    rfl

theorem cell23_7723502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_7723502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723502 prefixEnd_7723502 := by exact prefixLift 7723502
  have htrace : WordTrace (prefixWord ++ tailWord_7723502) baseStart_7723502 baseEnd_7723502 := by
    simpa [prefixWord, tailWord_7723502, baseEnd_7723502] using wordTrace_append hprefix tailTrace_7723502
  have hstable : (prefixWord ++ tailWord_7723502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723502).length < 2 ^ (prefixWord ++ tailWord_7723502).sum := by decide
  have hdescent : baseEnd_7723502 < baseStart_7723502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723555 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 3]
def baseStart_7723555 : Nat := 118140960795 + 7723555 * 2 ^ 59
def prefixEnd_7723555 : Nat := 4983230072969 + 3 ^ 40 * 7723555 * 2
def baseEnd_7723555 : Nat := 3965896076436634289242523

theorem tailTrace_7723555 : CollatzResearch.WordTrace tailWord_7723555 prefixEnd_7723555 3965896076436634289242523 := by
  unfold tailWord_7723555
  simp only [CollatzResearch.WordTrace]
  refine ⟨281701193533886788021932119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187800795689257858681288079 281701193533886788021932119)
  ·
    refine ⟨422551790300830182032898179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281701193533886788021932119 422551790300830182032898179)
    ·
      refine ⟨633827685451245273049347269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422551790300830182032898179 633827685451245273049347269)
      ·
        refine ⟨118842691022108488696752613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 633827685451245273049347269 118842691022108488696752613)
        ·
          refine ⟨22283004566645341630641115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118842691022108488696752613 22283004566645341630641115)
          ·
            refine ⟨33424506849968012445961673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22283004566645341630641115 33424506849968012445961673)
            ·
              refine ⟨25068380137476009334471255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33424506849968012445961673 25068380137476009334471255)
              ·
                refine ⟨37602570206214014001706883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25068380137476009334471255 37602570206214014001706883)
                ·
                  refine ⟨56403855309321021002560325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37602570206214014001706883 56403855309321021002560325)
                  ·
                    refine ⟨10575722870497691437980061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56403855309321021002560325 10575722870497691437980061)
                    ·
                      refine ⟨3965896076436634289242523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10575722870497691437980061 3965896076436634289242523)
                      ·
                        rfl

theorem cell23_7723555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_7723555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723555 prefixEnd_7723555 := by exact prefixLift 7723555
  have htrace : WordTrace (prefixWord ++ tailWord_7723555) baseStart_7723555 baseEnd_7723555 := by
    simpa [prefixWord, tailWord_7723555, baseEnd_7723555] using wordTrace_append hprefix tailTrace_7723555
  have hstable : (prefixWord ++ tailWord_7723555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723555).length < 2 ^ (prefixWord ++ tailWord_7723555).sum := by decide
  have hdescent : baseEnd_7723555 < baseStart_7723555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
