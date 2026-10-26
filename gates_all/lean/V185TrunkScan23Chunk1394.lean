import V185TrunkScan23Chunk1393

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8256581 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 3, 2, 3]
def baseStart_8256581 : Nat := 118140960795 + 8256581 * 2 ^ 59
def prefixEnd_8256581 : Nat := 4983230072969 + 3 ^ 40 * 8256581 * 2
def baseEnd_8256581 : Nat := 4239594615780065822566181

theorem tailTrace_8256581 : CollatzResearch.WordTrace tailWord_8256581 prefixEnd_8256581 4239594615780065822566181 := by
  unfold tailWord_8256581
  simp only [CollatzResearch.WordTrace]
  refine ⟨301142248900824623615177597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200761499267216415743451731 301142248900824623615177597)
  ·
    refine ⟨112928343337809233855691599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301142248900824623615177597 112928343337809233855691599)
    ·
      refine ⟨169392515006713850783537399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112928343337809233855691599 169392515006713850783537399)
      ·
        refine ⟨254088772510070776175306099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169392515006713850783537399 254088772510070776175306099)
        ·
          refine ⟨381133158765106164262959149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254088772510070776175306099 381133158765106164262959149)
          ·
            refine ⟨142924934536914811598609681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381133158765106164262959149 142924934536914811598609681)
            ·
              refine ⟨107193700902686108698957261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142924934536914811598609681 107193700902686108698957261)
              ·
                refine ⟨40197637838507290762108973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107193700902686108698957261 40197637838507290762108973)
                ·
                  refine ⟨15074114189440234035790865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40197637838507290762108973 15074114189440234035790865)
                  ·
                    refine ⟨11305585642080175526843149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15074114189440234035790865 11305585642080175526843149)
                    ·
                      refine ⟨4239594615780065822566181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11305585642080175526843149 4239594615780065822566181)
                      ·
                        rfl

theorem cell23_8256581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_8256581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256581 prefixEnd_8256581 := by exact prefixLift 8256581
  have htrace : WordTrace (prefixWord ++ tailWord_8256581) baseStart_8256581 baseEnd_8256581 := by
    simpa [prefixWord, tailWord_8256581, baseEnd_8256581] using wordTrace_append hprefix tailTrace_8256581
  have hstable : (prefixWord ++ tailWord_8256581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256581).length < 2 ^ (prefixWord ++ tailWord_8256581).sum := by decide
  have hdescent : baseEnd_8256581 < baseStart_8256581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256584 : List Nat := [2, 1, 3, 1, 1, 1, 5, 9]
def baseStart_8256584 : Nat := 118140960795 + 8256584 * 2 ^ 59
def prefixEnd_8256584 : Nat := 4983230072969 + 3 ^ 40 * 8256584 * 2
def baseEnd_8256584 : Nat := 157022079860075159660321

theorem tailTrace_8256584 : CollatzResearch.WordTrace tailWord_8256584 prefixEnd_8256584 157022079860075159660321 := by
  unfold tailWord_8256584
  simp only [CollatzResearch.WordTrace]
  refine ⟨150571179159906877563768403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200761572213209170085024537 150571179159906877563768403)
  ·
    refine ⟨225856768739860316345652605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150571179159906877563768403 225856768739860316345652605)
    ·
      refine ⟨84696288277447618629619727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225856768739860316345652605 84696288277447618629619727)
      ·
        refine ⟨127044432416171427944429591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84696288277447618629619727 127044432416171427944429591)
        ·
          refine ⟨190566648624257141916644387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127044432416171427944429591 190566648624257141916644387)
          ·
            refine ⟨285849972936385712874966581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190566648624257141916644387 285849972936385712874966581)
            ·
              refine ⟨26798434962786160582028117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285849972936385712874966581 26798434962786160582028117)
              ·
                refine ⟨157022079860075159660321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26798434962786160582028117 157022079860075159660321)
                ·
                  rfl

theorem cell23_8256584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 9].length) (baseStart_8256584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256584 prefixEnd_8256584 := by exact prefixLift 8256584
  have htrace : WordTrace (prefixWord ++ tailWord_8256584) baseStart_8256584 baseEnd_8256584 := by
    simpa [prefixWord, tailWord_8256584, baseEnd_8256584] using wordTrace_append hprefix tailTrace_8256584
  have hstable : (prefixWord ++ tailWord_8256584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256584).length < 2 ^ (prefixWord ++ tailWord_8256584).sum := by decide
  have hdescent : baseEnd_8256584 < baseStart_8256584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256589 : List Nat := [1, 6, 1, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_8256589 : Nat := 118140960795 + 8256589 * 2 ^ 59
def prefixEnd_8256589 : Nat := 4983230072969 + 3 ^ 40 * 8256589 * 2
def baseEnd_8256589 : Nat := 4239598723625301791266145

theorem tailTrace_8256589 : CollatzResearch.WordTrace tailWord_8256589 prefixEnd_8256589 4239598723625301791266145 := by
  unfold tailWord_8256589
  simp only [CollatzResearch.WordTrace]
  refine ⟨301142540684795640981468821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200761693789863760654312547 301142540684795640981468821)
  ·
    refine ⟨14116056594599795671006351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 301142540684795640981468821 14116056594599795671006351)
    ·
      refine ⟨21174084891899693506509527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14116056594599795671006351 21174084891899693506509527)
      ·
        refine ⟨31761127337849540259764291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21174084891899693506509527 31761127337849540259764291)
        ·
          refine ⟨47641691006774310389646437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31761127337849540259764291 47641691006774310389646437)
          ·
            refine ⟨8932817063770183198058707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47641691006774310389646437 8932817063770183198058707)
            ·
              refine ⟨13399225595655274797088061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8932817063770183198058707 13399225595655274797088061)
              ·
                refine ⟨5024709598370728048908023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13399225595655274797088061 5024709598370728048908023)
                ·
                  refine ⟨7537064397556092073362035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024709598370728048908023 7537064397556092073362035)
                  ·
                    refine ⟨11305596596334138110043053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7537064397556092073362035 11305596596334138110043053)
                    ·
                      refine ⟨4239598723625301791266145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11305596596334138110043053 4239598723625301791266145)
                      ·
                        rfl

theorem cell23_8256589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_8256589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256589 prefixEnd_8256589 := by exact prefixLift 8256589
  have htrace : WordTrace (prefixWord ++ tailWord_8256589) baseStart_8256589 baseEnd_8256589 := by
    simpa [prefixWord, tailWord_8256589, baseEnd_8256589] using wordTrace_append hprefix tailTrace_8256589
  have hstable : (prefixWord ++ tailWord_8256589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256589).length < 2 ^ (prefixWord ++ tailWord_8256589).sum := by decide
  have hdescent : baseEnd_8256589 < baseStart_8256589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256622 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_8256622 : Nat := 118140960795 + 8256622 * 2 ^ 59
def prefixEnd_8256622 : Nat := 4983230072969 + 3 ^ 40 * 8256622 * 2
def baseEnd_8256622 : Nat := 1413205222828966720717831

theorem tailTrace_8256622 : CollatzResearch.WordTrace tailWord_8256622 prefixEnd_8256622 1413205222828966720717831 := by
  unfold tailWord_8256622
  simp only [CollatzResearch.WordTrace]
  refine ⟨37642968036709510952177515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200762496195784058411613413 37642968036709510952177515)
  ·
    refine ⟨56464452055064266428266273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37642968036709510952177515 56464452055064266428266273)
    ·
      refine ⟨42348339041298199821199705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56464452055064266428266273 42348339041298199821199705)
      ·
        refine ⟨31761254280973649865899779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42348339041298199821199705 31761254280973649865899779)
        ·
          refine ⟨47641881421460474798849669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31761254280973649865899779 47641881421460474798849669)
          ·
            refine ⟨8932852766523839024784313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47641881421460474798849669 8932852766523839024784313)
            ·
              refine ⟨6699639574892879268588235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8932852766523839024784313 6699639574892879268588235)
              ·
                refine ⟨10049459362339318902882353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699639574892879268588235 10049459362339318902882353)
                ·
                  refine ⟨7537094521754489177161765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10049459362339318902882353 7537094521754489177161765)
                  ·
                    refine ⟨1413205222828966720717831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7537094521754489177161765 1413205222828966720717831)
                    ·
                      rfl

theorem cell23_8256622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_8256622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256622 prefixEnd_8256622 := by exact prefixLift 8256622
  have htrace : WordTrace (prefixWord ++ tailWord_8256622) baseStart_8256622 baseEnd_8256622 := by
    simpa [prefixWord, tailWord_8256622, baseEnd_8256622] using wordTrace_append hprefix tailTrace_8256622
  have hstable : (prefixWord ++ tailWord_8256622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256622).length < 2 ^ (prefixWord ++ tailWord_8256622).sum := by decide
  have hdescent : baseEnd_8256622 < baseStart_8256622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256629 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_8256629 : Nat := 118140960795 + 8256629 * 2 ^ 59
def prefixEnd_8256629 : Nat := 4983230072969 + 3 ^ 40 * 8256629 * 2
def baseEnd_8256629 : Nat := 4239619262851481634765961

theorem tailTrace_8256629 : CollatzResearch.WordTrace tailWord_8256629 prefixEnd_8256629 4239619262851481634765961 := by
  unfold tailWord_8256629
  simp only [CollatzResearch.WordTrace]
  refine ⟨301143999604650727812924941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200762666403100485208616627 301143999604650727812924941)
  ·
    refine ⟨112928999851744022929846853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301143999604650727812924941 112928999851744022929846853)
    ·
      refine ⟨21174187472202004299346285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112928999851744022929846853 21174187472202004299346285)
      ·
        refine ⟨7940320302075751612254857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21174187472202004299346285 7940320302075751612254857)
        ·
          refine ⟨5955240226556813709191143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7940320302075751612254857 5955240226556813709191143)
          ·
            refine ⟨8932860339835220563786715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5955240226556813709191143 8932860339835220563786715)
            ·
              refine ⟨13399290509752830845680073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8932860339835220563786715 13399290509752830845680073)
              ·
                refine ⟨10049467882314623134260055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13399290509752830845680073 10049467882314623134260055)
                ·
                  refine ⟨15074201823471934701390083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10049467882314623134260055 15074201823471934701390083)
                  ·
                    refine ⟨22611302735207902052085125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15074201823471934701390083 22611302735207902052085125)
                    ·
                      refine ⟨4239619262851481634765961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22611302735207902052085125 4239619262851481634765961)
                      ·
                        rfl

theorem cell23_8256629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_8256629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256629 prefixEnd_8256629 := by exact prefixLift 8256629
  have htrace : WordTrace (prefixWord ++ tailWord_8256629) baseStart_8256629 baseEnd_8256629 := by
    simpa [prefixWord, tailWord_8256629, baseEnd_8256629] using wordTrace_append hprefix tailTrace_8256629
  have hstable : (prefixWord ++ tailWord_8256629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256629).length < 2 ^ (prefixWord ++ tailWord_8256629).sum := by decide
  have hdescent : baseEnd_8256629 < baseStart_8256629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256706 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_8256706 : Nat := 118140960795 + 8256706 * 2 ^ 59
def prefixEnd_8256706 : Nat := 4983230072969 + 3 ^ 40 * 8256706 * 2
def baseEnd_8256706 : Nat := 4239658800861877833503107

theorem tailTrace_8256706 : CollatzResearch.WordTrace tailWord_8256706 prefixEnd_8256706 4239658800861877833503107 := by
  unfold tailWord_8256706
  simp only [CollatzResearch.WordTrace]
  refine ⟨75286702006342942490869493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200764538683581179975651981 75286702006342942490869493)
  ·
    refine ⟨7058128313094650858519015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75286702006342942490869493 7058128313094650858519015)
    ·
      refine ⟨10587192469641976287778523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7058128313094650858519015 10587192469641976287778523)
      ·
        refine ⟨15880788704462964431667785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10587192469641976287778523 15880788704462964431667785)
        ·
          refine ⟨11910591528347223323750839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15880788704462964431667785 11910591528347223323750839)
          ·
            refine ⟨17865887292520834985626259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11910591528347223323750839 17865887292520834985626259)
            ·
              refine ⟨26798830938781252478439389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17865887292520834985626259 26798830938781252478439389)
              ·
                refine ⟨10049561602042969679414771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26798830938781252478439389 10049561602042969679414771)
                ·
                  refine ⟨15074342403064454519122157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10049561602042969679414771 15074342403064454519122157)
                  ·
                    refine ⟨5652878401149170444670809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15074342403064454519122157 5652878401149170444670809)
                    ·
                      refine ⟨4239658800861877833503107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652878401149170444670809 4239658800861877833503107)
                      ·
                        rfl

theorem cell23_8256706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_8256706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256706 prefixEnd_8256706 := by exact prefixLift 8256706
  have htrace : WordTrace (prefixWord ++ tailWord_8256706) baseStart_8256706 baseEnd_8256706 := by
    simpa [prefixWord, tailWord_8256706, baseEnd_8256706] using wordTrace_append hprefix tailTrace_8256706
  have hstable : (prefixWord ++ tailWord_8256706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256706).length < 2 ^ (prefixWord ++ tailWord_8256706).sum := by decide
  have hdescent : baseEnd_8256706 < baseStart_8256706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256721 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 4, 5]
def baseStart_8256721 : Nat := 118140960795 + 8256721 * 2 ^ 59
def prefixEnd_8256721 : Nat := 4983230072969 + 3 ^ 40 * 8256721 * 2
def baseEnd_8256721 : Nat := 1413222167690565091605179

theorem tailTrace_8256721 : CollatzResearch.WordTrace tailWord_8256721 prefixEnd_8256721 1413222167690565091605179 := by
  unfold tailWord_8256721
  simp only [CollatzResearch.WordTrace]
  refine ⟨301147355120317427525274017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200764903413544951683516011 301147355120317427525274017)
  ·
    refine ⟨225860516340238070643955513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301147355120317427525274017 225860516340238070643955513)
    ·
      refine ⟨169395387255178552982966635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225860516340238070643955513 169395387255178552982966635)
      ·
        refine ⟨254093080882767829474449953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169395387255178552982966635 254093080882767829474449953)
        ·
          refine ⟨190569810662075872105837465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254093080882767829474449953 190569810662075872105837465)
          ·
            refine ⟨142927357996556904079378099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190569810662075872105837465 142927357996556904079378099)
            ·
              refine ⟨214391036994835356119067149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142927357996556904079378099 214391036994835356119067149)
              ·
                refine ⟨80396638873063258544650181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214391036994835356119067149 80396638873063258544650181)
                ·
                  refine ⟨15074369788699360977121909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80396638873063258544650181 15074369788699360977121909)
                  ·
                    refine ⟨1413222167690565091605179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15074369788699360977121909 1413222167690565091605179)
                    ·
                      rfl

theorem cell23_8256721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_8256721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256721 prefixEnd_8256721 := by exact prefixLift 8256721
  have htrace : WordTrace (prefixWord ++ tailWord_8256721) baseStart_8256721 baseEnd_8256721 := by
    simpa [prefixWord, tailWord_8256721, baseEnd_8256721] using wordTrace_append hprefix tailTrace_8256721
  have hstable : (prefixWord ++ tailWord_8256721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256721).length < 2 ^ (prefixWord ++ tailWord_8256721).sum := by decide
  have hdescent : baseEnd_8256721 < baseStart_8256721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256725 : List Nat := [1, 3, 2, 4, 1, 1, 2, 4, 5]
def baseStart_8256725 : Nat := 118140960795 + 8256725 * 2 ^ 59
def prefixEnd_8256725 : Nat := 4983230072969 + 3 ^ 40 * 8256725 * 2
def baseEnd_8256725 : Nat := 471074284110479251018391

theorem tailTrace_8256725 : CollatzResearch.WordTrace tailWord_8256725 prefixEnd_8256725 471074284110479251018391 := by
  unfold tailWord_8256725
  simp only [CollatzResearch.WordTrace]
  refine ⟨301147501012302936208419629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200765000674868624138946419 301147501012302936208419629)
  ·
    refine ⟨112930312879613601078157361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301147501012302936208419629 112930312879613601078157361)
    ·
      refine ⟨84697734659710200808618021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112930312879613601078157361 84697734659710200808618021)
      ·
        refine ⟨15880825248695662651615879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84697734659710200808618021 15880825248695662651615879)
        ·
          refine ⟨23821237873043493977423819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15880825248695662651615879 23821237873043493977423819)
          ·
            refine ⟨35731856809565240966135729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23821237873043493977423819 35731856809565240966135729)
            ·
              refine ⟨26798892607173930724601797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35731856809565240966135729 26798892607173930724601797)
              ·
                refine ⟨5024792363845112010862837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26798892607173930724601797 5024792363845112010862837)
                ·
                  refine ⟨471074284110479251018391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5024792363845112010862837 471074284110479251018391)
                  ·
                    rfl

theorem cell23_8256725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_8256725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256725 prefixEnd_8256725 := by exact prefixLift 8256725
  have htrace : WordTrace (prefixWord ++ tailWord_8256725) baseStart_8256725 baseEnd_8256725 := by
    simpa [prefixWord, tailWord_8256725, baseEnd_8256725] using wordTrace_append hprefix tailTrace_8256725
  have hstable : (prefixWord ++ tailWord_8256725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256725).length < 2 ^ (prefixWord ++ tailWord_8256725).sum := by decide
  have hdescent : baseEnd_8256725 < baseStart_8256725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256836 : List Nat := [2, 3, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_8256836 : Nat := 118140960795 + 8256836 * 2 ^ 59
def prefixEnd_8256836 : Nat := 4983230072969 + 3 ^ 40 * 8256836 * 2
def baseEnd_8256836 : Nat := 1413241851115654108292503

theorem tailTrace_8256836 : CollatzResearch.WordTrace tailWord_8256836 prefixEnd_8256836 1413241851115654108292503 := by
  unfold tailWord_8256836
  simp only [CollatzResearch.WordTrace]
  refine ⟨150575774757450401082855181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200767699676600534777140241 150575774757450401082855181)
  ·
    refine ⟨56465915534043900406070693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150575774757450401082855181 56465915534043900406070693)
    ·
      refine ⟨10587359162633231326138255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56465915534043900406070693 10587359162633231326138255)
      ·
        refine ⟨15881038743949846989207383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10587359162633231326138255 15881038743949846989207383)
        ·
          refine ⟨23821558115924770483811075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15881038743949846989207383 23821558115924770483811075)
          ·
            refine ⟨35732337173887155725716613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23821558115924770483811075 35732337173887155725716613)
            ·
              refine ⟨6699813220103841698571865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35732337173887155725716613 6699813220103841698571865)
              ·
                refine ⟨5024859915077881273928899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6699813220103841698571865 5024859915077881273928899)
                ·
                  refine ⟨7537289872616821910893349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024859915077881273928899 7537289872616821910893349)
                  ·
                    refine ⟨1413241851115654108292503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7537289872616821910893349 1413241851115654108292503)
                    ·
                      rfl

theorem cell23_8256836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_8256836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256836 prefixEnd_8256836 := by exact prefixLift 8256836
  have htrace : WordTrace (prefixWord ++ tailWord_8256836) baseStart_8256836 baseEnd_8256836 := by
    simpa [prefixWord, tailWord_8256836, baseEnd_8256836] using wordTrace_append hprefix tailTrace_8256836
  have hstable : (prefixWord ++ tailWord_8256836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256836).length < 2 ^ (prefixWord ++ tailWord_8256836).sum := by decide
  have hdescent : baseEnd_8256836 < baseStart_8256836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256848 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 4]
def baseStart_8256848 : Nat := 118140960795 + 8256848 * 2 ^ 59
def prefixEnd_8256848 : Nat := 4983230072969 + 3 ^ 40 * 8256848 * 2
def baseEnd_8256848 : Nat := 4239731715114816277927453

theorem tailTrace_8256848 : CollatzResearch.WordTrace tailWord_8256848 prefixEnd_8256848 4239731715114816277927453 := by
  unfold tailWord_8256848
  simp only [CollatzResearch.WordTrace]
  refine ⟨150575993595428664107573599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200767991460571552143431465 150575993595428664107573599)
  ·
    refine ⟨225863990393142996161360399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150575993595428664107573599 225863990393142996161360399)
    ·
      refine ⟨338795985589714494242040599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225863990393142996161360399 338795985589714494242040599)
      ·
        refine ⟨508193978384571741363060899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338795985589714494242040599 508193978384571741363060899)
        ·
          refine ⟨762290967576857612044591349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508193978384571741363060899 762290967576857612044591349)
          ·
            refine ⟨71464778210330401129180439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 762290967576857612044591349 71464778210330401129180439)
            ·
              refine ⟨107197167315495601693770659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71464778210330401129180439 107197167315495601693770659)
              ·
                refine ⟨160795750973243402540655989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107197167315495601693770659 160795750973243402540655989)
                ·
                  refine ⟨15074601653741568988186499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160795750973243402540655989 15074601653741568988186499)
                  ·
                    refine ⟨22611902480612353482279749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15074601653741568988186499 22611902480612353482279749)
                    ·
                      refine ⟨4239731715114816277927453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22611902480612353482279749 4239731715114816277927453)
                      ·
                        rfl

theorem cell23_8256848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_8256848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256848 prefixEnd_8256848 := by exact prefixLift 8256848
  have htrace : WordTrace (prefixWord ++ tailWord_8256848) baseStart_8256848 baseEnd_8256848 := by
    simpa [prefixWord, tailWord_8256848, baseEnd_8256848] using wordTrace_append hprefix tailTrace_8256848
  have hstable : (prefixWord ++ tailWord_8256848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256848).length < 2 ^ (prefixWord ++ tailWord_8256848).sum := by decide
  have hdescent : baseEnd_8256848 < baseStart_8256848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256858 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_8256858 : Nat := 118140960795 + 8256858 * 2 ^ 59
def prefixEnd_8256858 : Nat := 4983230072969 + 3 ^ 40 * 8256858 * 2
def baseEnd_8256858 : Nat := 1413245616640453746267469

theorem tailTrace_8256858 : CollatzResearch.WordTrace tailWord_8256858 prefixEnd_8256858 1413245616640453746267469 := by
  unfold tailWord_8256858
  simp only [CollatzResearch.WordTrace]
  refine ⟨75288087980205274980752807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200768234613880733282007485 75288087980205274980752807)
  ·
    refine ⟨112932131970307912471129211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75288087980205274980752807 112932131970307912471129211)
    ·
      refine ⟨169398197955461868706693817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112932131970307912471129211 169398197955461868706693817)
      ·
        refine ⟨127048648466596401530020363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169398197955461868706693817 127048648466596401530020363)
        ·
          refine ⟨190572972699894602295030545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127048648466596401530020363 190572972699894602295030545)
          ·
            refine ⟨142929729524920951721272909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190572972699894602295030545 142929729524920951721272909)
            ·
              refine ⟨53598648571845356895477341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142929729524920951721272909 53598648571845356895477341)
              ·
                refine ⟨20099493214442008835804003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53598648571845356895477341 20099493214442008835804003)
                ·
                  refine ⟨30149239821663013253706005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20099493214442008835804003 30149239821663013253706005)
                  ·
                    refine ⟨1413245616640453746267469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30149239821663013253706005 1413245616640453746267469)
                    ·
                      rfl

theorem cell23_8256858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_8256858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256858 prefixEnd_8256858 := by exact prefixLift 8256858
  have htrace : WordTrace (prefixWord ++ tailWord_8256858) baseStart_8256858 baseEnd_8256858 := by
    simpa [prefixWord, tailWord_8256858, baseEnd_8256858] using wordTrace_append hprefix tailTrace_8256858
  have hstable : (prefixWord ++ tailWord_8256858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256858).length < 2 ^ (prefixWord ++ tailWord_8256858).sum := by decide
  have hdescent : baseEnd_8256858 < baseStart_8256858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256882 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 5, 2, 2]
def baseStart_8256882 : Nat := 118140960795 + 8256882 * 2 ^ 59
def prefixEnd_8256882 : Nat := 4983230072969 + 3 ^ 40 * 8256882 * 2
def baseEnd_8256882 : Nat := 4239749173457069144902297

theorem tailTrace_8256882 : CollatzResearch.WordTrace tailWord_8256882 prefixEnd_8256882 4239749173457069144902297 := by
  unfold tailWord_8256882
  simp only [CollatzResearch.WordTrace]
  refine ⟨75288306818183538005471225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200768818181822768014589933 75288306818183538005471225)
  ·
    refine ⟨56466230113637653504103419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75288306818183538005471225 56466230113637653504103419)
    ·
      refine ⟨84699345170456480256155129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56466230113637653504103419 84699345170456480256155129)
      ·
        refine ⟨63524508877842360192116347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84699345170456480256155129 63524508877842360192116347)
        ·
          refine ⟨95286763316763540288174521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63524508877842360192116347 95286763316763540288174521)
          ·
            refine ⟨71465072487572655216130891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95286763316763540288174521 71465072487572655216130891)
            ·
              refine ⟨107197608731358982824196337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71465072487572655216130891 107197608731358982824196337)
              ·
                refine ⟨80398206548519237118147253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107197608731358982824196337 80398206548519237118147253)
                ·
                  refine ⟨7537331863923678479826305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80398206548519237118147253 7537331863923678479826305)
                  ·
                    refine ⟨5652998897942758859869729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7537331863923678479826305 5652998897942758859869729)
                    ·
                      refine ⟨4239749173457069144902297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5652998897942758859869729 4239749173457069144902297)
                      ·
                        rfl

theorem cell23_8256882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_8256882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256882 prefixEnd_8256882 := by exact prefixLift 8256882
  have htrace : WordTrace (prefixWord ++ tailWord_8256882) baseStart_8256882 baseEnd_8256882 := by
    simpa [prefixWord, tailWord_8256882, baseEnd_8256882] using wordTrace_append hprefix tailTrace_8256882
  have hstable : (prefixWord ++ tailWord_8256882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256882).length < 2 ^ (prefixWord ++ tailWord_8256882).sum := by decide
  have hdescent : baseEnd_8256882 < baseStart_8256882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256899 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 3, 2, 2]
def baseStart_8256899 : Nat := 118140960795 + 8256899 * 2 ^ 59
def prefixEnd_8256899 : Nat := 4983230072969 + 3 ^ 40 * 8256899 * 2
def baseEnd_8256899 : Nat := 4239757902628195578389719

theorem tailTrace_8256899 : CollatzResearch.WordTrace tailWord_8256899 prefixEnd_8256899 4239757902628195578389719 := by
  unfold tailWord_8256899
  simp only [CollatzResearch.WordTrace]
  refine ⟨301153847313672563925253751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200769231542448375950169167 301153847313672563925253751)
  ·
    refine ⟨451730770970508845887880627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301153847313672563925253751 451730770970508845887880627)
    ·
      refine ⟨677596156455763268831820941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451730770970508845887880627 677596156455763268831820941)
      ·
        refine ⟨254098558670911225811932853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677596156455763268831820941 254098558670911225811932853)
        ·
          refine ⟨23821739875397927419868705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254098558670911225811932853 23821739875397927419868705)
          ·
            refine ⟨17866304906548445564901529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23821739875397927419868705 17866304906548445564901529)
            ·
              refine ⟨13399728679911334173676147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17866304906548445564901529 13399728679911334173676147)
              ·
                refine ⟨20099593019867001260514221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13399728679911334173676147 20099593019867001260514221)
                ·
                  refine ⟨7537347382450125472692833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20099593019867001260514221 7537347382450125472692833)
                  ·
                    refine ⟨5653010536837594104519625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7537347382450125472692833 5653010536837594104519625)
                    ·
                      refine ⟨4239757902628195578389719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653010536837594104519625 4239757902628195578389719)
                      ·
                        rfl

theorem cell23_8256899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 2, 2].length) (baseStart_8256899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256899 prefixEnd_8256899 := by exact prefixLift 8256899
  have htrace : WordTrace (prefixWord ++ tailWord_8256899) baseStart_8256899 baseEnd_8256899 := by
    simpa [prefixWord, tailWord_8256899, baseEnd_8256899] using wordTrace_append hprefix tailTrace_8256899
  have hstable : (prefixWord ++ tailWord_8256899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256899).length < 2 ^ (prefixWord ++ tailWord_8256899).sum := by decide
  have hdescent : baseEnd_8256899 < baseStart_8256899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256928 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_8256928 : Nat := 118140960795 + 8256928 * 2 ^ 59
def prefixEnd_8256928 : Nat := 4983230072969 + 3 ^ 40 * 8256928 * 2
def baseEnd_8256928 : Nat := 4239772793567175964927085

theorem tailTrace_8256928 : CollatzResearch.WordTrace tailWord_8256928 prefixEnd_8256928 4239772793567175964927085 := by
  unfold tailWord_8256928
  simp only [CollatzResearch.WordTrace]
  refine ⟨150577452515283750939029719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200769936687045001252039625 150577452515283750939029719)
  ·
    refine ⟨225866178772925626408544579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150577452515283750939029719 225866178772925626408544579)
    ·
      refine ⟨338799268159388439612816869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225866178772925626408544579 338799268159388439612816869)
      ·
        refine ⟨63524862779885332427403163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338799268159388439612816869 63524862779885332427403163)
        ·
          refine ⟨95287294169827998641104745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63524862779885332427403163 95287294169827998641104745)
          ·
            refine ⟨71465470627370998980828559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95287294169827998641104745 71465470627370998980828559)
            ·
              refine ⟨107198205941056498471242839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71465470627370998980828559 107198205941056498471242839)
              ·
                refine ⟨160797308911584747706864259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107198205941056498471242839 160797308911584747706864259)
                ·
                  refine ⟨241195963367377121560296389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160797308911584747706864259 241195963367377121560296389)
                  ·
                    refine ⟨45224243131383210292555573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241195963367377121560296389 45224243131383210292555573)
                    ·
                      refine ⟨4239772793567175964927085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45224243131383210292555573 4239772793567175964927085)
                      ·
                        rfl

theorem cell23_8256928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_8256928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256928 prefixEnd_8256928 := by exact prefixLift 8256928
  have htrace : WordTrace (prefixWord ++ tailWord_8256928) baseStart_8256928 baseEnd_8256928 := by
    simpa [prefixWord, tailWord_8256928, baseEnd_8256928] using wordTrace_append hprefix tailTrace_8256928
  have hstable : (prefixWord ++ tailWord_8256928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256928).length < 2 ^ (prefixWord ++ tailWord_8256928).sum := by decide
  have hdescent : baseEnd_8256928 < baseStart_8256928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8256989 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_8256989 : Nat := 118140960795 + 8256989 * 2 ^ 59
def prefixEnd_8256989 : Nat := 4983230072969 + 3 ^ 40 * 8256989 * 2
def baseEnd_8256989 : Nat := 4239804115887100226264305

theorem tailTrace_8256989 : CollatzResearch.WordTrace tailWord_8256989 prefixEnd_8256989 4239804115887100226264305 := by
  unfold tailWord_8256989
  simp only [CollatzResearch.WordTrace]
  refine ⟨301157129883346509296030021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200771419922231006197353347 301157129883346509296030021)
  ·
    refine ⟨56466961853127470493005629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301157129883346509296030021 56466961853127470493005629)
    ·
      refine ⟨21175110694922801434877111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56466961853127470493005629 21175110694922801434877111)
      ·
        refine ⟨31762666042384202152315667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21175110694922801434877111 31762666042384202152315667)
        ·
          refine ⟨47643999063576303228473501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31762666042384202152315667 47643999063576303228473501)
          ·
            refine ⟨17866499648841113710677563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47643999063576303228473501 17866499648841113710677563)
            ·
              refine ⟨26799749473261670566016345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17866499648841113710677563 26799749473261670566016345)
              ·
                refine ⟨20099812104946252924512259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26799749473261670566016345 20099812104946252924512259)
                ·
                  refine ⟨30149718157419379386768389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20099812104946252924512259 30149718157419379386768389)
                  ·
                    refine ⟨5653072154516133635019073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30149718157419379386768389 5653072154516133635019073)
                    ·
                      refine ⟨4239804115887100226264305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653072154516133635019073 4239804115887100226264305)
                      ·
                        rfl

theorem cell23_8256989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_8256989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8256989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8256989 prefixEnd_8256989 := by exact prefixLift 8256989
  have htrace : WordTrace (prefixWord ++ tailWord_8256989) baseStart_8256989 baseEnd_8256989 := by
    simpa [prefixWord, tailWord_8256989, baseEnd_8256989] using wordTrace_append hprefix tailTrace_8256989
  have hstable : (prefixWord ++ tailWord_8256989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8256989).length < 2 ^ (prefixWord ++ tailWord_8256989).sum := by decide
  have hdescent : baseEnd_8256989 < baseStart_8256989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8256989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257006 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_8257006 : Nat := 118140960795 + 8257006 * 2 ^ 59
def prefixEnd_8257006 : Nat := 4983230072969 + 3 ^ 40 * 8257006 * 2
def baseEnd_8257006 : Nat := 4239812845058226659751727

theorem tailTrace_8257006 : CollatzResearch.WordTrace tailWord_8257006 prefixEnd_8257006 4239812845058226659751727 := by
  unfold tailWord_8257006
  simp only [CollatzResearch.WordTrace]
  refine ⟨37644718740535615149924859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200771833282856614132932581 37644718740535615149924859)
  ·
    refine ⟨56467078110803422724887289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37644718740535615149924859 56467078110803422724887289)
    ·
      refine ⟨42350308583102567043665467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56467078110803422724887289 42350308583102567043665467)
      ·
        refine ⟨63525462874653850565498201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42350308583102567043665467 63525462874653850565498201)
        ·
          refine ⟨47644097155990387924123651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63525462874653850565498201 47644097155990387924123651)
          ·
            refine ⟨71466145733985581886185477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47644097155990387924123651 71466145733985581886185477)
            ·
              refine ⟨13399902325122296603659777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71466145733985581886185477 13399902325122296603659777)
              ·
                refine ⟨10049926743841722452744833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13399902325122296603659777 10049926743841722452744833)
                ·
                  refine ⟨7537445057881291839558625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10049926743841722452744833 7537445057881291839558625)
                  ·
                    refine ⟨5653083793410968879668969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7537445057881291839558625 5653083793410968879668969)
                    ·
                      refine ⟨4239812845058226659751727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653083793410968879668969 4239812845058226659751727)
                      ·
                        rfl

theorem cell23_8257006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_8257006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257006 prefixEnd_8257006 := by exact prefixLift 8257006
  have htrace : WordTrace (prefixWord ++ tailWord_8257006) baseStart_8257006 baseEnd_8257006 := by
    simpa [prefixWord, tailWord_8257006, baseEnd_8257006] using wordTrace_append hprefix tailTrace_8257006
  have hstable : (prefixWord ++ tailWord_8257006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257006).length < 2 ^ (prefixWord ++ tailWord_8257006).sum := by decide
  have hdescent : baseEnd_8257006 < baseStart_8257006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257106 : List Nat := [3, 2, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_8257106 : Nat := 118140960795 + 8257106 * 2 ^ 59
def prefixEnd_8257106 : Nat := 4983230072969 + 3 ^ 40 * 8257106 * 2
def baseEnd_8257106 : Nat := 1413288064374558756167089

theorem tailTrace_8257106 : CollatzResearch.WordTrace tailWord_8257106 prefixEnd_8257106 1413288064374558756167089 := by
  unfold tailWord_8257106
  simp only [CollatzResearch.WordTrace]
  refine ⟨75290349305980659569509793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200774264815948425518692781 75290349305980659569509793)
  ·
    refine ⟨56467761979485494677132345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75290349305980659569509793 56467761979485494677132345)
    ·
      refine ⟨42350821484614121007849259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56467761979485494677132345 42350821484614121007849259)
      ·
        refine ⟨63526232226921181511773889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42350821484614121007849259 63526232226921181511773889)
        ·
          refine ⟨47644674170190886133830417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63526232226921181511773889 47644674170190886133830417)
          ·
            refine ⟨35733505627643164600372813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47644674170190886133830417 35733505627643164600372813)
            ·
              refine ⟨13400064610366186725139805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35733505627643164600372813 13400064610366186725139805)
              ·
                refine ⟨5025024228887320021927427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13400064610366186725139805 5025024228887320021927427)
                ·
                  refine ⟨7537536343330980032891141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025024228887320021927427 7537536343330980032891141)
                  ·
                    refine ⟨1413288064374558756167089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7537536343330980032891141 1413288064374558756167089)
                    ·
                      rfl

theorem cell23_8257106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_8257106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257106 prefixEnd_8257106 := by exact prefixLift 8257106
  have htrace : WordTrace (prefixWord ++ tailWord_8257106) baseStart_8257106 baseEnd_8257106 := by
    simpa [prefixWord, tailWord_8257106, baseEnd_8257106] using wordTrace_append hprefix tailTrace_8257106
  have hstable : (prefixWord ++ tailWord_8257106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257106).length < 2 ^ (prefixWord ++ tailWord_8257106).sum := by decide
  have hdescent : baseEnd_8257106 < baseStart_8257106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257129 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 3, 1, 3]
def baseStart_8257129 : Nat := 118140960795 + 8257129 * 2 ^ 59
def prefixEnd_8257129 : Nat := 4983230072969 + 3 ^ 40 * 8257129 * 2
def baseEnd_8257129 : Nat := 4239876003178729678513661

theorem tailTrace_8257129 : CollatzResearch.WordTrace tailWord_8257129 prefixEnd_8257129 4239876003178729678513661 := by
  unfold tailWord_8257129
  simp only [CollatzResearch.WordTrace]
  refine ⟨301162236102839313206126441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200774824068559542137417627 301162236102839313206126441)
  ·
    refine ⟨225871677077129484904594831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301162236102839313206126441 225871677077129484904594831)
    ·
      refine ⟨338807515615694227356892247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225871677077129484904594831 338807515615694227356892247)
      ·
        refine ⟨508211273423541341035338371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338807515615694227356892247 508211273423541341035338371)
        ·
          refine ⟨762316910135312011553007557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508211273423541341035338371 762316910135312011553007557)
          ·
            refine ⟨142934420650371002166188917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 762316910135312011553007557 142934420650371002166188917)
            ·
              refine ⟨13400101935972281453080211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142934420650371002166188917 13400101935972281453080211)
              ·
                refine ⟨20100152903958422179620317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13400101935972281453080211 20100152903958422179620317)
                ·
                  refine ⟨7537557338984408317357619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20100152903958422179620317 7537557338984408317357619)
                  ·
                    refine ⟨11306336008476612476036429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7537557338984408317357619 11306336008476612476036429)
                    ·
                      refine ⟨4239876003178729678513661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11306336008476612476036429 4239876003178729678513661)
                      ·
                        rfl

theorem cell23_8257129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 1, 3].length) (baseStart_8257129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257129 prefixEnd_8257129 := by exact prefixLift 8257129
  have htrace : WordTrace (prefixWord ++ tailWord_8257129) baseStart_8257129 baseEnd_8257129 := by
    simpa [prefixWord, tailWord_8257129, baseEnd_8257129] using wordTrace_append hprefix tailTrace_8257129
  have hstable : (prefixWord ++ tailWord_8257129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257129).length < 2 ^ (prefixWord ++ tailWord_8257129).sum := by decide
  have hdescent : baseEnd_8257129 < baseStart_8257129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257135 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 4]
def baseStart_8257135 : Nat := 118140960795 + 8257135 * 2 ^ 59
def prefixEnd_8257135 : Nat := 4983230072969 + 3 ^ 40 * 8257135 * 2
def baseEnd_8257135 : Nat := 4239879084062656655038633

theorem tailTrace_8257135 : CollatzResearch.WordTrace tailWord_8257135 prefixEnd_8257135 4239879084062656655038633 := by
  unfold tailWord_8257135
  simp only [CollatzResearch.WordTrace]
  refine ⟨301162454940817576230844859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200774969960545050820563239 301162454940817576230844859)
  ·
    refine ⟨451743682411226364346267289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301162454940817576230844859 451743682411226364346267289)
    ·
      refine ⟨338807761808419773259700467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451743682411226364346267289 338807761808419773259700467)
      ·
        refine ⟨508211642712629659889550701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338807761808419773259700467 508211642712629659889550701)
        ·
          refine ⟨190579366017236122458581513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508211642712629659889550701 190579366017236122458581513)
          ·
            refine ⟨142934524512927091843936135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190579366017236122458581513 142934524512927091843936135)
            ·
              refine ⟨214401786769390637765904203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142934524512927091843936135 214401786769390637765904203)
              ·
                refine ⟨321602680154085956648856305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214401786769390637765904203 321602680154085956648856305)
                ·
                  refine ⟨241202010115564467486642229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321602680154085956648856305 241202010115564467486642229)
                  ·
                    refine ⟨22612688448334168826872709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 241202010115564467486642229 22612688448334168826872709)
                    ·
                      refine ⟨4239879084062656655038633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22612688448334168826872709 4239879084062656655038633)
                      ·
                        rfl

theorem cell23_8257135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_8257135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257135 prefixEnd_8257135 := by exact prefixLift 8257135
  have htrace : WordTrace (prefixWord ++ tailWord_8257135) baseStart_8257135 baseEnd_8257135 := by
    simpa [prefixWord, tailWord_8257135, baseEnd_8257135] using wordTrace_append hprefix tailTrace_8257135
  have hstable : (prefixWord ++ tailWord_8257135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257135).length < 2 ^ (prefixWord ++ tailWord_8257135).sum := by decide
  have hdescent : baseEnd_8257135 < baseStart_8257135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257149 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_8257149 : Nat := 118140960795 + 8257149 * 2 ^ 59
def prefixEnd_8257149 : Nat := 4983230072969 + 3 ^ 40 * 8257149 * 2
def baseEnd_8257149 : Nat := 1413295424263939866754523

theorem tailTrace_8257149 : CollatzResearch.WordTrace tailWord_8257149 prefixEnd_8257149 1413295424263939866754523 := by
  unfold tailWord_8257149
  simp only [CollatzResearch.WordTrace]
  refine ⟨301162965562766856621854501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200775310375177904414569667 301162965562766856621854501)
  ·
    refine ⟨56468056043018785616597719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301162965562766856621854501 56468056043018785616597719)
    ·
      refine ⟨84702084064528178424896579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56468056043018785616597719 84702084064528178424896579)
      ·
        refine ⟨127053126096792267637344869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84702084064528178424896579 127053126096792267637344869)
        ·
          refine ⟨23822461143148550182002163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127053126096792267637344869 23822461143148550182002163)
          ·
            refine ⟨35733691714722825273003245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23822461143148550182002163 35733691714722825273003245)
            ·
              refine ⟨13400134393021059477376217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35733691714722825273003245 13400134393021059477376217)
              ·
                refine ⟨10050100794765794608032163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13400134393021059477376217 10050100794765794608032163)
                ·
                  refine ⟨15075151192148691912048245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10050100794765794608032163 15075151192148691912048245)
                  ·
                    refine ⟨1413295424263939866754523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15075151192148691912048245 1413295424263939866754523)
                    ·
                      rfl

theorem cell23_8257149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_8257149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257149 prefixEnd_8257149 := by exact prefixLift 8257149
  have htrace : WordTrace (prefixWord ++ tailWord_8257149) baseStart_8257149 baseEnd_8257149 := by
    simpa [prefixWord, tailWord_8257149, baseEnd_8257149] using wordTrace_append hprefix tailTrace_8257149
  have hstable : (prefixWord ++ tailWord_8257149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257149).length < 2 ^ (prefixWord ++ tailWord_8257149).sum := by decide
  have hdescent : baseEnd_8257149 < baseStart_8257149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257152 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 4]
def baseStart_8257152 : Nat := 118140960795 + 8257152 * 2 ^ 59
def prefixEnd_8257152 : Nat := 4983230072969 + 3 ^ 40 * 8257152 * 2
def baseEnd_8257152 : Nat := 4239887813233783088526055

theorem tailTrace_8257152 : CollatzResearch.WordTrace tailWord_8257152 prefixEnd_8257152 4239887813233783088526055 := by
  unfold tailWord_8257152
  simp only [CollatzResearch.WordTrace]
  refine ⟨150581537490877994067106855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200775383321170658756142473 150581537490877994067106855)
  ·
    refine ⟨225872306236316991100660283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150581537490877994067106855 225872306236316991100660283)
    ·
      refine ⟨338808459354475486650990425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225872306236316991100660283 338808459354475486650990425)
      ·
        refine ⟨254106344515856614988242819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338808459354475486650990425 254106344515856614988242819)
        ·
          refine ⟨381159516773784922482364229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254106344515856614988242819 381159516773784922482364229)
          ·
            refine ⟨71467409395084672965443293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 381159516773784922482364229 71467409395084672965443293)
            ·
              refine ⟨26800278523156752362041235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71467409395084672965443293 26800278523156752362041235)
              ·
                refine ⟨40200417784735128543061853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26800278523156752362041235 40200417784735128543061853)
                ·
                  refine ⟨15075156669275673203648195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40200417784735128543061853 15075156669275673203648195)
                  ·
                    refine ⟨22612735003913509805472293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15075156669275673203648195 22612735003913509805472293)
                    ·
                      refine ⟨4239887813233783088526055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22612735003913509805472293 4239887813233783088526055)
                      ·
                        rfl

theorem cell23_8257152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_8257152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257152 prefixEnd_8257152 := by exact prefixLift 8257152
  have htrace : WordTrace (prefixWord ++ tailWord_8257152) baseStart_8257152 baseEnd_8257152 := by
    simpa [prefixWord, tailWord_8257152, baseEnd_8257152] using wordTrace_append hprefix tailTrace_8257152
  have hstable : (prefixWord ++ tailWord_8257152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257152).length < 2 ^ (prefixWord ++ tailWord_8257152).sum := by decide
  have hdescent : baseEnd_8257152 < baseStart_8257152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257162 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_8257162 : Nat := 118140960795 + 8257162 * 2 ^ 59
def prefixEnd_8257162 : Nat := 4983230072969 + 3 ^ 40 * 8257162 * 2
def baseEnd_8257162 : Nat := 1413297649346776016467003

theorem tailTrace_8257162 : CollatzResearch.WordTrace tailWord_8257162 prefixEnd_8257162 1413297649346776016467003 := by
  unfold tailWord_8257162
  simp only [CollatzResearch.WordTrace]
  refine ⟨75290859927929939960519435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200775626474479839894718493 75290859927929939960519435)
  ·
    refine ⟨112936289891894909940779153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75290859927929939960519435 112936289891894909940779153)
    ·
      refine ⟨84702217418921182455584365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112936289891894909940779153 84702217418921182455584365)
      ·
        refine ⟨31763331532095443420844137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84702217418921182455584365 31763331532095443420844137)
        ·
          refine ⟨23822498649071582565633103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31763331532095443420844137 23822498649071582565633103)
          ·
            refine ⟨35733747973607373848449655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23822498649071582565633103 35733747973607373848449655)
            ·
              refine ⟨53600621960411060772674483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35733747973607373848449655 53600621960411060772674483)
              ·
                refine ⟨80400932940616591159011725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53600621960411060772674483 80400932940616591159011725)
                ·
                  refine ⟨30150349852731221684629397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80400932940616591159011725 30150349852731221684629397)
                  ·
                    refine ⟨1413297649346776016467003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30150349852731221684629397 1413297649346776016467003)
                    ·
                      rfl

theorem cell23_8257162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_8257162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257162 prefixEnd_8257162 := by exact prefixLift 8257162
  have htrace : WordTrace (prefixWord ++ tailWord_8257162) baseStart_8257162 baseEnd_8257162 := by
    simpa [prefixWord, tailWord_8257162, baseEnd_8257162] using wordTrace_append hprefix tailTrace_8257162
  have hstable : (prefixWord ++ tailWord_8257162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257162).length < 2 ^ (prefixWord ++ tailWord_8257162).sum := by decide
  have hdescent : baseEnd_8257162 < baseStart_8257162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257166 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_8257166 : Nat := 118140960795 + 8257166 * 2 ^ 59
def prefixEnd_8257166 : Nat := 4983230072969 + 3 ^ 40 * 8257166 * 2
def baseEnd_8257166 : Nat := 1413298333987648677916997

theorem tailTrace_8257166 : CollatzResearch.WordTrace tailWord_8257166 prefixEnd_8257166 1413298333987648677916997 := by
  unfold tailWord_8257166
  simp only [CollatzResearch.WordTrace]
  refine ⟨37645448200463158565652919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200775723735803512350148901 37645448200463158565652919)
  ·
    refine ⟨56468172300694737848479379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37645448200463158565652919 56468172300694737848479379)
    ·
      refine ⟨84702258451042106772719069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56468172300694737848479379 84702258451042106772719069)
      ·
        refine ⟨31763346919140790039769651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84702258451042106772719069 31763346919140790039769651)
        ·
          refine ⟨47645020378711185059654477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31763346919140790039769651 47645020378711185059654477)
          ·
            refine ⟨17866882642016694397370429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47645020378711185059654477 17866882642016694397370429)
            ·
              refine ⟨6700080990756260399013911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17866882642016694397370429 6700080990756260399013911)
              ·
                refine ⟨10050121486134390598520867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6700080990756260399013911 10050121486134390598520867)
                ·
                  refine ⟨15075182229201585897781301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10050121486134390598520867 15075182229201585897781301)
                  ·
                    refine ⟨1413298333987648677916997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15075182229201585897781301 1413298333987648677916997)
                    ·
                      rfl

theorem cell23_8257166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_8257166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257166 prefixEnd_8257166 := by exact prefixLift 8257166
  have htrace : WordTrace (prefixWord ++ tailWord_8257166) baseStart_8257166 baseEnd_8257166 := by
    simpa [prefixWord, tailWord_8257166, baseEnd_8257166] using wordTrace_append hprefix tailTrace_8257166
  have hstable : (prefixWord ++ tailWord_8257166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257166).length < 2 ^ (prefixWord ++ tailWord_8257166).sum := by decide
  have hdescent : baseEnd_8257166 < baseStart_8257166 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257169 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 7, 2, 2]
def baseStart_8257169 : Nat := 118140960795 + 8257169 * 2 ^ 59
def prefixEnd_8257169 : Nat := 4983230072969 + 3 ^ 40 * 8257169 * 2
def baseEnd_8257169 : Nat := 4239896542404909522013477

theorem tailTrace_8257169 : CollatzResearch.WordTrace tailWord_8257169 prefixEnd_8257169 4239896542404909522013477 := by
  unfold tailWord_8257169
  simp only [CollatzResearch.WordTrace]
  refine ⟨301163695022694400037582561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200775796681796266691721707 301163695022694400037582561)
  ·
    refine ⟨225872771267020800028186921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301163695022694400037582561 225872771267020800028186921)
    ·
      refine ⟨169404578450265600021140191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225872771267020800028186921 169404578450265600021140191)
      ·
        refine ⟨254106867675398400031710287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169404578450265600021140191 254106867675398400031710287)
        ·
          refine ⟨381160301513097600047565431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254106867675398400031710287 381160301513097600047565431)
          ·
            refine ⟨571740452269646400071348147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381160301513097600047565431 571740452269646400071348147)
            ·
              refine ⟨857610678404469600107022221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571740452269646400071348147 857610678404469600107022221)
              ·
                refine ⟨321604004401676100040133333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 857610678404469600107022221 321604004401676100040133333)
                ·
                  refine ⟨7537593853164283594690625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 321604004401676100040133333 7537593853164283594690625)
                  ·
                    refine ⟨5653195389873212696017969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7537593853164283594690625 5653195389873212696017969)
                    ·
                      refine ⟨4239896542404909522013477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653195389873212696017969 4239896542404909522013477)
                      ·
                        rfl

theorem cell23_8257169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 2, 2].length) (baseStart_8257169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257169 prefixEnd_8257169 := by exact prefixLift 8257169
  have htrace : WordTrace (prefixWord ++ tailWord_8257169) baseStart_8257169 baseEnd_8257169 := by
    simpa [prefixWord, tailWord_8257169, baseEnd_8257169] using wordTrace_append hprefix tailTrace_8257169
  have hstable : (prefixWord ++ tailWord_8257169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257169).length < 2 ^ (prefixWord ++ tailWord_8257169).sum := by decide
  have hdescent : baseEnd_8257169 < baseStart_8257169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257175 : List Nat := [1, 1, 3, 3, 2, 13]
def baseStart_8257175 : Nat := 118140960795 + 8257175 * 2 ^ 59
def prefixEnd_8257175 : Nat := 4983230072969 + 3 ^ 40 * 8257175 * 2
def baseEnd_8257175 : Nat := 17448146597896446496043

theorem tailTrace_8257175 : CollatzResearch.WordTrace tailWord_8257175 prefixEnd_8257175 17448146597896446496043 := by
  unfold tailWord_8257175
  simp only [CollatzResearch.WordTrace]
  refine ⟨301163913860672663062300979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200775942573781775374867319 301163913860672663062300979)
  ·
    refine ⟨451745870791008994593451469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301163913860672663062300979 451745870791008994593451469)
    ·
      refine ⟨169404701546628372972544301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451745870791008994593451469 169404701546628372972544301)
      ·
        refine ⟨63526763079985639864704113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169404701546628372972544301 63526763079985639864704113)
        ·
          refine ⟨47645072309989229898528085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63526763079985639864704113 47645072309989229898528085)
          ·
            refine ⟨17448146597896446496043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 47645072309989229898528085 17448146597896446496043)
            ·
              rfl

theorem cell23_8257175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 13].length) (baseStart_8257175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257175 prefixEnd_8257175 := by exact prefixLift 8257175
  have htrace : WordTrace (prefixWord ++ tailWord_8257175) baseStart_8257175 baseEnd_8257175 := by
    simpa [prefixWord, tailWord_8257175, baseEnd_8257175] using wordTrace_append hprefix tailTrace_8257175
  have hstable : (prefixWord ++ tailWord_8257175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257175).length < 2 ^ (prefixWord ++ tailWord_8257175).sum := by decide
  have hdescent : baseEnd_8257175 < baseStart_8257175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257220 : List Nat := [2, 3, 3, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_8257220 : Nat := 118140960795 + 8257220 * 2 ^ 59
def prefixEnd_8257220 : Nat := 4983230072969 + 3 ^ 40 * 8257220 * 2
def baseEnd_8257220 : Nat := 4239922729918288822475743

theorem tailTrace_8257220 : CollatzResearch.WordTrace tailWord_8257220 prefixEnd_8257220 4239922729918288822475743 := by
  unfold tailWord_8257220
  simp only [CollatzResearch.WordTrace]
  refine ⟨150582777572754817873844557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200777036763673090498459409 150582777572754817873844557)
  ·
    refine ⟨56468541589783056702691709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150582777572754817873844557 56468541589783056702691709)
    ·
      refine ⟨21175703096168646263509391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56468541589783056702691709 21175703096168646263509391)
      ·
        refine ⟨31763554644252969395264087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21175703096168646263509391 31763554644252969395264087)
        ·
          refine ⟨47645331966379454092896131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31763554644252969395264087 47645331966379454092896131)
          ·
            refine ⟨71467997949569181139344197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47645331966379454092896131 71467997949569181139344197)
            ·
              refine ⟨13400249615544221463627037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71467997949569181139344197 13400249615544221463627037)
              ·
                refine ⟨5025093605829083048860139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13400249615544221463627037 5025093605829083048860139)
                ·
                  refine ⟨7537640408743624573290209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025093605829083048860139 7537640408743624573290209)
                  ·
                    refine ⟨5653230306557718429967657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7537640408743624573290209 5653230306557718429967657)
                    ·
                      refine ⟨4239922729918288822475743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653230306557718429967657 4239922729918288822475743)
                      ·
                        rfl

theorem cell23_8257220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_8257220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257220 prefixEnd_8257220 := by exact prefixLift 8257220
  have htrace : WordTrace (prefixWord ++ tailWord_8257220) baseStart_8257220 baseEnd_8257220 := by
    simpa [prefixWord, tailWord_8257220, baseEnd_8257220] using wordTrace_append hprefix tailTrace_8257220
  have hstable : (prefixWord ++ tailWord_8257220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257220).length < 2 ^ (prefixWord ++ tailWord_8257220).sum := by decide
  have hdescent : baseEnd_8257220 < baseStart_8257220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257252 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_8257252 : Nat := 118140960795 + 8257252 * 2 ^ 59
def prefixEnd_8257252 : Nat := 4983230072969 + 3 ^ 40 * 8257252 * 2
def baseEnd_8257252 : Nat := 1413313053766410899091865

theorem tailTrace_8257252 : CollatzResearch.WordTrace tailWord_8257252 prefixEnd_8257252 1413313053766410899091865 := by
  unfold tailWord_8257252
  simp only [CollatzResearch.WordTrace]
  refine ⟨150583361140696852606427005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200777814854262470141902673 150583361140696852606427005)
  ·
    refine ⟨56468760427761319727410127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150583361140696852606427005 56468760427761319727410127)
    ·
      refine ⟨84703140641641979591115191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56468760427761319727410127 84703140641641979591115191)
      ·
        refine ⟨127054710962462969386672787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84703140641641979591115191 127054710962462969386672787)
        ·
          refine ⟨190582066443694454080009181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127054710962462969386672787 190582066443694454080009181)
          ·
            refine ⟨71468274916385420280003443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190582066443694454080009181 71468274916385420280003443)
            ·
              refine ⟨107202412374578130420005165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71468274916385420280003443 107202412374578130420005165)
              ·
                refine ⟨40200904640466798907501937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107202412374578130420005165 40200904640466798907501937)
                ·
                  refine ⟨30150678480350099180626453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40200904640466798907501937 30150678480350099180626453)
                  ·
                    refine ⟨1413313053766410899091865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30150678480350099180626453 1413313053766410899091865)
                    ·
                      rfl

theorem cell23_8257252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_8257252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257252 prefixEnd_8257252 := by exact prefixLift 8257252
  have htrace : WordTrace (prefixWord ++ tailWord_8257252) baseStart_8257252 baseEnd_8257252 := by
    simpa [prefixWord, tailWord_8257252, baseEnd_8257252] using wordTrace_append hprefix tailTrace_8257252
  have hstable : (prefixWord ++ tailWord_8257252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257252).length < 2 ^ (prefixWord ++ tailWord_8257252).sum := by decide
  have hdescent : baseEnd_8257252 < baseStart_8257252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257253 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 2, 1, 3]
def baseStart_8257253 : Nat := 118140960795 + 8257253 * 2 ^ 59
def prefixEnd_8257253 : Nat := 4983230072969 + 3 ^ 40 * 8257253 * 2
def baseEnd_8257253 : Nat := 4239939674779887193363091

theorem tailTrace_8257253 : CollatzResearch.WordTrace tailWord_8257253 prefixEnd_8257253 4239939674779887193363091 := by
  unfold tailWord_8257253
  simp only [CollatzResearch.WordTrace]
  refine ⟨301166758754390082383640413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200777839169593388255760275 301166758754390082383640413)
  ·
    refine ⟨112937534532896280893865155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301166758754390082383640413 112937534532896280893865155)
    ·
      refine ⟨169406301799344421340797733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112937534532896280893865155 169406301799344421340797733)
      ·
        refine ⟨31763681587377079001399575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169406301799344421340797733 31763681587377079001399575)
        ·
          refine ⟨47645522381065618502099363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31763681587377079001399575 47645522381065618502099363)
          ·
            refine ⟨71468283571598427753149045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47645522381065618502099363 71468283571598427753149045)
            ·
              refine ⟨6700151584837352601857723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71468283571598427753149045 6700151584837352601857723)
              ·
                refine ⟨10050227377256028902786585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6700151584837352601857723 10050227377256028902786585)
                ·
                  refine ⟨7537670532942021677089939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10050227377256028902786585 7537670532942021677089939)
                  ·
                    refine ⟨11306505799413032515634909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7537670532942021677089939 11306505799413032515634909)
                    ·
                      refine ⟨4239939674779887193363091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11306505799413032515634909 4239939674779887193363091)
                      ·
                        rfl

theorem cell23_8257253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_8257253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257253 prefixEnd_8257253 := by exact prefixLift 8257253
  have htrace : WordTrace (prefixWord ++ tailWord_8257253) baseStart_8257253 baseEnd_8257253 := by
    simpa [prefixWord, tailWord_8257253, baseEnd_8257253] using wordTrace_append hprefix tailTrace_8257253
  have hstable : (prefixWord ++ tailWord_8257253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257253).length < 2 ^ (prefixWord ++ tailWord_8257253).sum := by decide
  have hdescent : baseEnd_8257253 < baseStart_8257253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257272 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_8257272 : Nat := 118140960795 + 8257272 * 2 ^ 59
def prefixEnd_8257272 : Nat := 4983230072969 + 3 ^ 40 * 8257272 * 2
def baseEnd_8257272 : Nat := 4239949430912322619025503

theorem tailTrace_8257272 : CollatzResearch.WordTrace tailWord_8257272 prefixEnd_8257272 4239949430912322619025503 := by
  unfold tailWord_8257272
  simp only [CollatzResearch.WordTrace]
  refine ⟨150583725870660624314291035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200778301160880832419054713 150583725870660624314291035)
  ·
    refine ⟨225875588805990936471436553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150583725870660624314291035 225875588805990936471436553)
    ·
      refine ⟨169406691604493202353577415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225875588805990936471436553 169406691604493202353577415)
      ·
        refine ⟨254110037406739803530366123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169406691604493202353577415 254110037406739803530366123)
        ·
          refine ⟨381165056110109705295549185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254110037406739803530366123 381165056110109705295549185)
          ·
            refine ⟨285873792082582278971661889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381165056110109705295549185 285873792082582278971661889)
            ·
              refine ⟨214405344061936709228746417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285873792082582278971661889 214405344061936709228746417)
              ·
                refine ⟨160804008046452531921559813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214405344061936709228746417 160804008046452531921559813)
                ·
                  refine ⟨30150751508709849735292465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160804008046452531921559813 30150751508709849735292465)
                  ·
                    refine ⟨22613063631532387301469349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30150751508709849735292465 22613063631532387301469349)
                    ·
                      refine ⟨4239949430912322619025503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22613063631532387301469349 4239949430912322619025503)
                      ·
                        rfl

theorem cell23_8257272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_8257272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257272 prefixEnd_8257272 := by exact prefixLift 8257272
  have htrace : WordTrace (prefixWord ++ tailWord_8257272) baseStart_8257272 baseEnd_8257272 := by
    simpa [prefixWord, tailWord_8257272, baseEnd_8257272] using wordTrace_append hprefix tailTrace_8257272
  have hstable : (prefixWord ++ tailWord_8257272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257272).length < 2 ^ (prefixWord ++ tailWord_8257272).sum := by decide
  have hdescent : baseEnd_8257272 < baseStart_8257272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257276 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 6, 2, 2]
def baseStart_8257276 : Nat := 118140960795 + 8257276 * 2 ^ 59
def prefixEnd_8257276 : Nat := 4983230072969 + 3 ^ 40 * 8257276 * 2
def baseEnd_8257276 : Nat := 4239951484834940603375485

theorem tailTrace_8257276 : CollatzResearch.WordTrace tailWord_8257276 prefixEnd_8257276 4239951484834940603375485 := by
  unfold tailWord_8257276
  simp only [CollatzResearch.WordTrace]
  refine ⟨150583798816653378655863841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200778398422204504874485121 150583798816653378655863841)
  ·
    refine ⟨112937849112490033991897881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150583798816653378655863841 112937849112490033991897881)
    ·
      refine ⟨84703386834367525493923411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112937849112490033991897881 84703386834367525493923411)
      ·
        refine ⟨127055080251551288240885117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84703386834367525493923411 127055080251551288240885117)
        ·
          refine ⟨47645655094331733090331919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127055080251551288240885117 47645655094331733090331919)
          ·
            refine ⟨71468482641497599635497879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47645655094331733090331919 71468482641497599635497879)
            ·
              refine ⟨107202723962246399453246819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71468482641497599635497879 107202723962246399453246819)
              ·
                refine ⟨160804085943369599179870229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107202723962246399453246819 160804085943369599179870229)
                ·
                  refine ⟨7537691528595449961556417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160804085943369599179870229 7537691528595449961556417)
                  ·
                    refine ⟨5653268646446587471167313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7537691528595449961556417 5653268646446587471167313)
                    ·
                      refine ⟨4239951484834940603375485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653268646446587471167313 4239951484834940603375485)
                      ·
                        rfl

theorem cell23_8257276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_8257276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257276 prefixEnd_8257276 := by exact prefixLift 8257276
  have htrace : WordTrace (prefixWord ++ tailWord_8257276) baseStart_8257276 baseEnd_8257276 := by
    simpa [prefixWord, tailWord_8257276, baseEnd_8257276] using wordTrace_append hprefix tailTrace_8257276
  have hstable : (prefixWord ++ tailWord_8257276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257276).length < 2 ^ (prefixWord ++ tailWord_8257276).sum := by decide
  have hdescent : baseEnd_8257276 < baseStart_8257276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257329 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 2, 5]
def baseStart_8257329 : Nat := 118140960795 + 8257329 * 2 ^ 59
def prefixEnd_8257329 : Nat := 4983230072969 + 3 ^ 40 * 8257329 * 2
def baseEnd_8257329 : Nat := 1413326233103209632004247

theorem tailTrace_8257329 : CollatzResearch.WordTrace tailWord_8257329 prefixEnd_8257329 1413326233103209632004247 := by
  unfold tailWord_8257329
  simp only [CollatzResearch.WordTrace]
  refine ⟨301169530702114747363407041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200779687134743164908938027 301169530702114747363407041)
  ·
    refine ⟨225877148026586060522555281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301169530702114747363407041 225877148026586060522555281)
    ·
      refine ⟨169407861019939545391916461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225877148026586060522555281 169407861019939545391916461)
      ·
        refine ⟨63527947882477329521968673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169407861019939545391916461 63527947882477329521968673)
        ·
          refine ⟨47645960911857997141476505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63527947882477329521968673 47645960911857997141476505)
          ·
            refine ⟨35734470683893497856107379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47645960911857997141476505 35734470683893497856107379)
            ·
              refine ⟨53601706025840246784161069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35734470683893497856107379 53601706025840246784161069)
              ·
                refine ⟨20100639759690092544060401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53601706025840246784161069 20100639759690092544060401)
                ·
                  refine ⟨15075479819767569408045301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20100639759690092544060401 15075479819767569408045301)
                  ·
                    refine ⟨1413326233103209632004247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15075479819767569408045301 1413326233103209632004247)
                    ·
                      rfl

theorem cell23_8257329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_8257329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257329 prefixEnd_8257329 := by exact prefixLift 8257329
  have htrace : WordTrace (prefixWord ++ tailWord_8257329) baseStart_8257329 baseEnd_8257329 := by
    simpa [prefixWord, tailWord_8257329, baseEnd_8257329] using wordTrace_append hprefix tailTrace_8257329
  have hstable : (prefixWord ++ tailWord_8257329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257329).length < 2 ^ (prefixWord ++ tailWord_8257329).sum := by decide
  have hdescent : baseEnd_8257329 < baseStart_8257329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257349 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_8257349 : Nat := 118140960795 + 8257349 * 2 ^ 59
def prefixEnd_8257349 : Nat := 4983230072969 + 3 ^ 40 * 8257349 * 2
def baseEnd_8257349 : Nat := 4239988968922718817762649

theorem tailTrace_8257349 : CollatzResearch.WordTrace tailWord_8257349 prefixEnd_8257349 4239988968922718817762649 := by
  unfold tailWord_8257349
  simp only [CollatzResearch.WordTrace]
  refine ⟨301170260162042290779135101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200780173441361527186090067 301170260162042290779135101)
  ·
    refine ⟨112938847560765859042175663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301170260162042290779135101 112938847560765859042175663)
    ·
      refine ⟨169408271341148788563263495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112938847560765859042175663 169408271341148788563263495)
      ·
        refine ⟨254112407011723182844895243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169408271341148788563263495 254112407011723182844895243)
        ·
          refine ⟨381168610517584774267342865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254112407011723182844895243 381168610517584774267342865)
          ·
            refine ⟨285876457888188580700507149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381168610517584774267342865 285876457888188580700507149)
            ·
              refine ⟨107203671708070717762690181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285876457888188580700507149 107203671708070717762690181)
              ·
                refine ⟨20100688445263259580504409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107203671708070717762690181 20100688445263259580504409)
                ·
                  refine ⟨15075516333947444685378307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20100688445263259580504409 15075516333947444685378307)
                  ·
                    refine ⟨22613274500921167028067461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15075516333947444685378307 22613274500921167028067461)
                    ·
                      refine ⟨4239988968922718817762649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22613274500921167028067461 4239988968922718817762649)
                      ·
                        rfl

theorem cell23_8257349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_8257349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257349 prefixEnd_8257349 := by exact prefixLift 8257349
  have htrace : WordTrace (prefixWord ++ tailWord_8257349) baseStart_8257349 baseEnd_8257349 := by
    simpa [prefixWord, tailWord_8257349, baseEnd_8257349] using wordTrace_append hprefix tailTrace_8257349
  have hstable : (prefixWord ++ tailWord_8257349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257349).length < 2 ^ (prefixWord ++ tailWord_8257349).sum := by decide
  have hdescent : baseEnd_8257349 < baseStart_8257349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257350 : List Nat := [6, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_8257350 : Nat := 118140960795 + 8257350 * 2 ^ 59
def prefixEnd_8257350 : Nat := 4983230072969 + 3 ^ 40 * 8257350 * 2
def baseEnd_8257350 : Nat := 471109942489263701538905

theorem tailTrace_8257350 : CollatzResearch.WordTrace tailWord_8257350 prefixEnd_8257350 471109942489263701538905 := by
  unfold tailWord_8257350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9411571769844958373435047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 200780197756692445299947669 9411571769844958373435047)
  ·
    refine ⟨14117357654767437560152571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9411571769844958373435047 14117357654767437560152571)
    ·
      refine ⟨21176036482151156340228857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14117357654767437560152571 21176036482151156340228857)
      ·
        refine ⟨15882027361613367255171643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21176036482151156340228857 15882027361613367255171643)
        ·
          refine ⟨23823041042420050882757465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15882027361613367255171643 23823041042420050882757465)
          ·
            refine ⟨17867280781815038162068099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23823041042420050882757465 17867280781815038162068099)
            ·
              refine ⟨26800921172722557243102149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17867280781815038162068099 26800921172722557243102149)
              ·
                refine ⟨5025172719885479483081653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26800921172722557243102149 5025172719885479483081653)
                ·
                  refine ⟨471109942489263701538905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5025172719885479483081653 471109942489263701538905)
                  ·
                    rfl

theorem cell23_8257350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_8257350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257350 prefixEnd_8257350 := by exact prefixLift 8257350
  have htrace : WordTrace (prefixWord ++ tailWord_8257350) baseStart_8257350 baseEnd_8257350 := by
    simpa [prefixWord, tailWord_8257350, baseEnd_8257350] using wordTrace_append hprefix tailTrace_8257350
  have hstable : (prefixWord ++ tailWord_8257350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257350).length < 2 ^ (prefixWord ++ tailWord_8257350).sum := by decide
  have hdescent : baseEnd_8257350 < baseStart_8257350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257369 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 1, 4, 3]
def baseStart_8257369 : Nat := 118140960795 + 8257369 * 2 ^ 59
def prefixEnd_8257369 : Nat := 4983230072969 + 3 ^ 40 * 8257369 * 2
def baseEnd_8257369 : Nat := 4239999238535808739512557

theorem tailTrace_8257369 : CollatzResearch.WordTrace tailWord_8257369 prefixEnd_8257369 4239999238535808739512557 := by
  unfold tailWord_8257369
  simp only [CollatzResearch.WordTrace]
  refine ⟨301170989621969834194863161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200780659747979889463242107 301170989621969834194863161)
  ·
    refine ⟨225878242216477375646147371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301170989621969834194863161 225878242216477375646147371)
    ·
      refine ⟨338817363324716063469221057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225878242216477375646147371 338817363324716063469221057)
      ·
        refine ⟨254113022493537047601915793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338817363324716063469221057 254113022493537047601915793)
        ·
          refine ⟨190584766870152785701436845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254113022493537047601915793 190584766870152785701436845)
          ·
            refine ⟨71469287576307294638038817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190584766870152785701436845 71469287576307294638038817)
            ·
              refine ⟨53601965682230470978529113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71469287576307294638038817 53601965682230470978529113)
              ·
                refine ⟨40201474261672853233896835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53601965682230470978529113 40201474261672853233896835)
                ·
                  refine ⟨60302211392509279850845253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40201474261672853233896835 60302211392509279850845253)
                  ·
                    refine ⟨11306664636095489972033485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60302211392509279850845253 11306664636095489972033485)
                    ·
                      refine ⟨4239999238535808739512557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11306664636095489972033485 4239999238535808739512557)
                      ·
                        rfl

theorem cell23_8257369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_8257369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257369 prefixEnd_8257369 := by exact prefixLift 8257369
  have htrace : WordTrace (prefixWord ++ tailWord_8257369) baseStart_8257369 baseEnd_8257369 := by
    simpa [prefixWord, tailWord_8257369, baseEnd_8257369] using wordTrace_append hprefix tailTrace_8257369
  have hstable : (prefixWord ++ tailWord_8257369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257369).length < 2 ^ (prefixWord ++ tailWord_8257369).sum := by decide
  have hdescent : baseEnd_8257369 < baseStart_8257369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257376 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 3, 4]
def baseStart_8257376 : Nat := 118140960795 + 8257376 * 2 ^ 59
def prefixEnd_8257376 : Nat := 4983230072969 + 3 ^ 40 * 8257376 * 2
def baseEnd_8257376 : Nat := 1413334277633463404041675

theorem tailTrace_8257376 : CollatzResearch.WordTrace tailWord_8257376 prefixEnd_8257376 1413334277633463404041675 := by
  unfold tailWord_8257376
  simp only [CollatzResearch.WordTrace]
  refine ⟨150585622466472237195183991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200780829955296316260245321 150585622466472237195183991)
  ·
    refine ⟨225878433699708355792775987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150585622466472237195183991 225878433699708355792775987)
    ·
      refine ⟨338817650549562533689163981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225878433699708355792775987 338817650549562533689163981)
      ·
        refine ⟨127056618956085950133436493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338817650549562533689163981 127056618956085950133436493)
        ·
          refine ⟨47646232108532231300038685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127056618956085950133436493 47646232108532231300038685)
          ·
            refine ⟨17867337040699586737514507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47646232108532231300038685 17867337040699586737514507)
            ·
              refine ⟨26801005561049380106271761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17867337040699586737514507 26801005561049380106271761)
              ·
                refine ⟨20100754170787035079703821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26801005561049380106271761 20100754170787035079703821)
                ·
                  refine ⟨7537782814045138154888933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20100754170787035079703821 7537782814045138154888933)
                  ·
                    refine ⟨1413334277633463404041675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7537782814045138154888933 1413334277633463404041675)
                    ·
                      rfl

theorem cell23_8257376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3, 4].length) (baseStart_8257376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257376 prefixEnd_8257376 := by exact prefixLift 8257376
  have htrace : WordTrace (prefixWord ++ tailWord_8257376) baseStart_8257376 baseEnd_8257376 := by
    simpa [prefixWord, tailWord_8257376, baseEnd_8257376] using wordTrace_append hprefix tailTrace_8257376
  have hstable : (prefixWord ++ tailWord_8257376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257376).length < 2 ^ (prefixWord ++ tailWord_8257376).sum := by decide
  have hdescent : baseEnd_8257376 < baseStart_8257376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257393 : List Nat := [1, 2, 2, 2, 1, 3, 4, 3, 1, 4]
def baseStart_8257393 : Nat := 118140960795 + 8257393 * 2 ^ 59
def prefixEnd_8257393 : Nat := 4983230072969 + 3 ^ 40 * 8257393 * 2
def baseEnd_8257393 : Nat := 1413337187357172215204149

theorem tailTrace_8257393 : CollatzResearch.WordTrace tailWord_8257393 prefixEnd_8257393 1413337187357172215204149 := by
  unfold tailWord_8257393
  simp only [CollatzResearch.WordTrace]
  refine ⟨301171864973882886293736833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200781243315921924195824555 301171864973882886293736833)
  ·
    refine ⟨225878898730412164720302625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301171864973882886293736833 225878898730412164720302625)
    ·
      refine ⟨169409174047809123540226969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225878898730412164720302625 169409174047809123540226969)
      ·
        refine ⟨127056880535856842655170227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169409174047809123540226969 127056880535856842655170227)
        ·
          refine ⟨190585320803785263982755341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127056880535856842655170227 190585320803785263982755341)
          ·
            refine ⟨71469495301419473993533253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190585320803785263982755341 71469495301419473993533253)
            ·
              refine ⟨13400530369016151373787485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71469495301419473993533253 13400530369016151373787485)
              ·
                refine ⟨5025198888381056765170307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13400530369016151373787485 5025198888381056765170307)
                ·
                  refine ⟨7537798332571585147755461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025198888381056765170307 7537798332571585147755461)
                  ·
                    refine ⟨1413337187357172215204149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7537798332571585147755461 1413337187357172215204149)
                    ·
                      rfl

theorem cell23_8257393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_8257393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257393 prefixEnd_8257393 := by exact prefixLift 8257393
  have htrace : WordTrace (prefixWord ++ tailWord_8257393) baseStart_8257393 baseEnd_8257393 := by
    simpa [prefixWord, tailWord_8257393, baseEnd_8257393] using wordTrace_append hprefix tailTrace_8257393
  have hstable : (prefixWord ++ tailWord_8257393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257393).length < 2 ^ (prefixWord ++ tailWord_8257393).sum := by decide
  have hdescent : baseEnd_8257393 < baseStart_8257393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257486 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_8257486 : Nat := 118140960795 + 8257486 * 2 ^ 59
def prefixEnd_8257486 : Nat := 4983230072969 + 3 ^ 40 * 8257486 * 2
def baseEnd_8257486 : Nat := 4240059315772384781749519

theorem tailTrace_8257486 : CollatzResearch.WordTrace tailWord_8257486 prefixEnd_8257486 4240059315772384781749519 := by
  unfold tailWord_8257486
  simp only [CollatzResearch.WordTrace]
  refine ⟨37646907120318245397109039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200783504641697308784581541 37646907120318245397109039)
  ·
    refine ⟨56470360680477368095663559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37646907120318245397109039 56470360680477368095663559)
    ·
      refine ⟨84705541020716052143495339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56470360680477368095663559 84705541020716052143495339)
      ·
        refine ⟨127058311531074078215243009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84705541020716052143495339 127058311531074078215243009)
        ·
          refine ⟨95293733648305558661432257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127058311531074078215243009 95293733648305558661432257)
          ·
            refine ⟨71470300236229168996074193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95293733648305558661432257 71470300236229168996074193)
            ·
              refine ⟨53602725177171876747055645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71470300236229168996074193 53602725177171876747055645)
              ·
                refine ⟨20101021941439453780145867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53602725177171876747055645 20101021941439453780145867)
                ·
                  refine ⟨30151532912159180670218801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20101021941439453780145867 30151532912159180670218801)
                  ·
                    refine ⟨22613649684119385502664101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30151532912159180670218801 22613649684119385502664101)
                    ·
                      refine ⟨4240059315772384781749519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22613649684119385502664101 4240059315772384781749519)
                      ·
                        rfl

theorem cell23_8257486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_8257486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257486 prefixEnd_8257486 := by exact prefixLift 8257486
  have htrace : WordTrace (prefixWord ++ tailWord_8257486) baseStart_8257486 baseEnd_8257486 := by
    simpa [prefixWord, tailWord_8257486, baseEnd_8257486] using wordTrace_append hprefix tailTrace_8257486
  have hstable : (prefixWord ++ tailWord_8257486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257486).length < 2 ^ (prefixWord ++ tailWord_8257486).sum := by decide
  have hdescent : baseEnd_8257486 < baseStart_8257486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257493 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_8257493 : Nat := 118140960795 + 8257493 * 2 ^ 59
def prefixEnd_8257493 : Nat := 4983230072969 + 3 ^ 40 * 8257493 * 2
def baseEnd_8257493 : Nat := 4240062910136966254361987

theorem tailTrace_8257493 : CollatzResearch.WordTrace tailWord_8257493 prefixEnd_8257493 4240062910136966254361987 := by
  unfold tailWord_8257493
  simp only [CollatzResearch.WordTrace]
  refine ⟨301175512273520603372377133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200783674849013735581584755 301175512273520603372377133)
  ·
    refine ⟨112940817102570226264641425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301175512273520603372377133 112940817102570226264641425)
    ·
      refine ⟨84705612826927669698481069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112940817102570226264641425 84705612826927669698481069)
      ·
        refine ⟨31764604810097876136930401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84705612826927669698481069 31764604810097876136930401)
        ·
          refine ⟨23823453607573407102697801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31764604810097876136930401 23823453607573407102697801)
          ·
            refine ⟨17867590205680055327023351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23823453607573407102697801 17867590205680055327023351)
            ·
              refine ⟨26801385308520082990535027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17867590205680055327023351 26801385308520082990535027)
              ·
                refine ⟨40202077962780124485802541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26801385308520082990535027 40202077962780124485802541)
                ·
                  refine ⟨15075779236042546682175953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40202077962780124485802541 15075779236042546682175953)
                  ·
                    refine ⟨11306834427031910011631965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15075779236042546682175953 11306834427031910011631965)
                    ·
                      refine ⟨4240062910136966254361987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11306834427031910011631965 4240062910136966254361987)
                      ·
                        rfl

theorem cell23_8257493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_8257493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257493 prefixEnd_8257493 := by exact prefixLift 8257493
  have htrace : WordTrace (prefixWord ++ tailWord_8257493) baseStart_8257493 baseEnd_8257493 := by
    simpa [prefixWord, tailWord_8257493, baseEnd_8257493] using wordTrace_append hprefix tailTrace_8257493
  have hstable : (prefixWord ++ tailWord_8257493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257493).length < 2 ^ (prefixWord ++ tailWord_8257493).sum := by decide
  have hdescent : baseEnd_8257493 < baseStart_8257493 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257517 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_8257517 : Nat := 118140960795 + 8257517 * 2 ^ 59
def prefixEnd_8257517 : Nat := 4983230072969 + 3 ^ 40 * 8257517 * 2
def baseEnd_8257517 : Nat := 1413358411224224720153959

theorem tailTrace_8257517 : CollatzResearch.WordTrace tailWord_8257517 prefixEnd_8257517 1413358411224224720153959 := by
  unfold tailWord_8257517
  simp only [CollatzResearch.WordTrace]
  refine ⟨301176387625433655471250805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200784258416955770314167203 301176387625433655471250805)
  ·
    refine ⟨28235286339884405200429763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301176387625433655471250805 28235286339884405200429763)
    ·
      refine ⟨42352929509826607800644645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28235286339884405200429763 42352929509826607800644645)
      ·
        refine ⟨7941174283092488962620871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42352929509826607800644645 7941174283092488962620871)
        ·
          refine ⟨11911761424638733443931307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941174283092488962620871 11911761424638733443931307)
          ·
            refine ⟨17867642136958100165896961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11911761424638733443931307 17867642136958100165896961)
            ·
              refine ⟨13400731602718575124422721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17867642136958100165896961 13400731602718575124422721)
              ·
                refine ⟨10050548702038931343317041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13400731602718575124422721 10050548702038931343317041)
                ·
                  refine ⟨7537911526529198507487781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10050548702038931343317041 7537911526529198507487781)
                  ·
                    refine ⟨1413358411224224720153959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7537911526529198507487781 1413358411224224720153959)
                    ·
                      rfl

theorem cell23_8257517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_8257517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257517 prefixEnd_8257517 := by exact prefixLift 8257517
  have htrace : WordTrace (prefixWord ++ tailWord_8257517) baseStart_8257517 baseEnd_8257517 := by
    simpa [prefixWord, tailWord_8257517, baseEnd_8257517] using wordTrace_append hprefix tailTrace_8257517
  have hstable : (prefixWord ++ tailWord_8257517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257517).length < 2 ^ (prefixWord ++ tailWord_8257517).sum := by decide
  have hdescent : baseEnd_8257517 < baseStart_8257517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257533 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 3, 3, 2]
def baseStart_8257533 : Nat := 118140960795 + 8257533 * 2 ^ 59
def prefixEnd_8257533 : Nat := 4983230072969 + 3 ^ 40 * 8257533 * 2
def baseEnd_8257533 : Nat := 4240083449363146097861803

theorem tailTrace_8257533 : CollatzResearch.WordTrace tailWord_8257533 prefixEnd_8257533 4240083449363146097861803 := by
  unfold tailWord_8257533
  simp only [CollatzResearch.WordTrace]
  refine ⟨301176971193375690203833253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200784647462250460135888835 301176971193375690203833253)
  ·
    refine ⟨56470682098757941913218735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301176971193375690203833253 56470682098757941913218735)
    ·
      refine ⟨84706023148136912869828103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56470682098757941913218735 84706023148136912869828103)
      ·
        refine ⟨127059034722205369304742155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84706023148136912869828103 127059034722205369304742155)
        ·
          refine ⟨190588552083308053957113233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127059034722205369304742155 190588552083308053957113233)
          ·
            refine ⟨142941414062481040467834925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190588552083308053957113233 142941414062481040467834925)
            ·
              refine ⟨53603030273430390175438097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142941414062481040467834925 53603030273430390175438097)
              ·
                refine ⟨40202272705072792631578573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53603030273430390175438097 40202272705072792631578573)
                ·
                  refine ⟨15075852264402297236841965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40202272705072792631578573 15075852264402297236841965)
                  ·
                    refine ⟨5653444599150861463815737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15075852264402297236841965 5653444599150861463815737)
                    ·
                      refine ⟨4240083449363146097861803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653444599150861463815737 4240083449363146097861803)
                      ·
                        rfl

theorem cell23_8257533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_8257533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257533 prefixEnd_8257533 := by exact prefixLift 8257533
  have htrace : WordTrace (prefixWord ++ tailWord_8257533) baseStart_8257533 baseEnd_8257533 := by
    simpa [prefixWord, tailWord_8257533, baseEnd_8257533] using wordTrace_append hprefix tailTrace_8257533
  have hstable : (prefixWord ++ tailWord_8257533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257533).length < 2 ^ (prefixWord ++ tailWord_8257533).sum := by decide
  have hdescent : baseEnd_8257533 < baseStart_8257533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257550 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2]
def baseStart_8257550 : Nat := 118140960795 + 8257550 * 2 ^ 59
def prefixEnd_8257550 : Nat := 4983230072969 + 3 ^ 40 * 8257550 * 2
def baseEnd_8257550 : Nat := 4240092178534272531349225

theorem tailTrace_8257550 : CollatzResearch.WordTrace tailWord_8257550 prefixEnd_8257550 4240092178534272531349225 := by
  unfold tailWord_8257550
  simp only [CollatzResearch.WordTrace]
  refine ⟨37647198904289262763400263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200785060822876068071468069 37647198904289262763400263)
  ·
    refine ⟨56470798356433894145100395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37647198904289262763400263 56470798356433894145100395)
    ·
      refine ⟨84706197534650841217650593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56470798356433894145100395 84706197534650841217650593)
      ·
        refine ⟨63529648150988130913237945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84706197534650841217650593 63529648150988130913237945)
        ·
          refine ⟨47647236113241098184928459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63529648150988130913237945 47647236113241098184928459)
          ·
            refine ⟨71470854169861647277392689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47647236113241098184928459 71470854169861647277392689)
            ·
              refine ⟨53603140627396235458044517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71470854169861647277392689 53603140627396235458044517)
              ·
                refine ⟨10050588867636794148383347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53603140627396235458044517 10050588867636794148383347)
                ·
                  refine ⟨15075883301455191222575021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10050588867636794148383347 15075883301455191222575021)
                  ·
                    refine ⟨5653456238045696708465633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15075883301455191222575021 5653456238045696708465633)
                    ·
                      refine ⟨4240092178534272531349225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653456238045696708465633 4240092178534272531349225)
                      ·
                        rfl

theorem cell23_8257550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_8257550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257550 prefixEnd_8257550 := by exact prefixLift 8257550
  have htrace : WordTrace (prefixWord ++ tailWord_8257550) baseStart_8257550 baseEnd_8257550 := by
    simpa [prefixWord, tailWord_8257550, baseEnd_8257550] using wordTrace_append hprefix tailTrace_8257550
  have hstable : (prefixWord ++ tailWord_8257550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257550).length < 2 ^ (prefixWord ++ tailWord_8257550).sum := by decide
  have hdescent : baseEnd_8257550 < baseStart_8257550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257579 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 9]
def baseStart_8257579 : Nat := 118140960795 + 8257579 * 2 ^ 59
def prefixEnd_8257579 : Nat := 4983230072969 + 3 ^ 40 * 8257579 * 2
def baseEnd_8257579 : Nat := 4240107069473252917886591

theorem tailTrace_8257579 : CollatzResearch.WordTrace tailWord_8257579 prefixEnd_8257579 4240107069473252917886591 := by
  unfold tailWord_8257579
  simp only [CollatzResearch.WordTrace]
  refine ⟨301178648951209040060007791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200785765967472693373338527 301178648951209040060007791)
  ·
    refine ⟨451767973426813560090011687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301178648951209040060007791 451767973426813560090011687)
    ·
      refine ⟨677651960140220340135017531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451767973426813560090011687 677651960140220340135017531)
      ·
        refine ⟨1016477940210330510202526297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677651960140220340135017531 1016477940210330510202526297)
        ·
          refine ⟨762358455157747882651894723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1016477940210330510202526297 762358455157747882651894723)
          ·
            refine ⟨1143537682736621823977842085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762358455157747882651894723 1143537682736621823977842085)
            ·
              refine ⟨214413315513116591995845391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1143537682736621823977842085 214413315513116591995845391)
              ·
                refine ⟨321619973269674887993768087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214413315513116591995845391 321619973269674887993768087)
                ·
                  refine ⟨482429959904512331990652131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321619973269674887993768087 482429959904512331990652131)
                  ·
                    refine ⟨723644939856768497985978197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 482429959904512331990652131 723644939856768497985978197)
                    ·
                      refine ⟨4240107069473252917886591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 723644939856768497985978197 4240107069473252917886591)
                      ·
                        rfl

theorem cell23_8257579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_8257579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257579 prefixEnd_8257579 := by exact prefixLift 8257579
  have htrace : WordTrace (prefixWord ++ tailWord_8257579) baseStart_8257579 baseEnd_8257579 := by
    simpa [prefixWord, tailWord_8257579, baseEnd_8257579] using wordTrace_append hprefix tailTrace_8257579
  have hstable : (prefixWord ++ tailWord_8257579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257579).length < 2 ^ (prefixWord ++ tailWord_8257579).sum := by decide
  have hdescent : baseEnd_8257579 < baseStart_8257579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257580 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 2, 2, 2]
def baseStart_8257580 : Nat := 118140960795 + 8257580 * 2 ^ 59
def prefixEnd_8257580 : Nat := 4983230072969 + 3 ^ 40 * 8257580 * 2
def baseEnd_8257580 : Nat := 4240107582953907413974087

theorem tailTrace_8257580 : CollatzResearch.WordTrace tailWord_8257580 prefixEnd_8257580 4240107582953907413974087 := by
  unfold tailWord_8257580
  simp only [CollatzResearch.WordTrace]
  refine ⟨150589342712102708615397097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200785790282803611487196129 150589342712102708615397097)
  ·
    refine ⟨112942007034077031461547823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150589342712102708615397097 112942007034077031461547823)
    ·
      refine ⟨169413010551115547192321735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112942007034077031461547823 169413010551115547192321735)
      ·
        refine ⟨254119515826673320788482603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169413010551115547192321735 254119515826673320788482603)
        ·
          refine ⟨381179273740009981182723905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254119515826673320788482603 381179273740009981182723905)
          ·
            refine ⟨285884455305007485887042929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381179273740009981182723905 285884455305007485887042929)
            ·
              refine ⟨214413341478755614415282197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285884455305007485887042929 214413341478755614415282197)
              ·
                refine ⟨10050625381816669425716353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214413341478755614415282197 10050625381816669425716353)
                ·
                  refine ⟨7537969036362502069287265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10050625381816669425716353 7537969036362502069287265)
                  ·
                    refine ⟨5653476777271876551965449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7537969036362502069287265 5653476777271876551965449)
                    ·
                      refine ⟨4240107582953907413974087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653476777271876551965449 4240107582953907413974087)
                      ·
                        rfl

theorem cell23_8257580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 2, 2].length) (baseStart_8257580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257580 prefixEnd_8257580 := by exact prefixLift 8257580
  have htrace : WordTrace (prefixWord ++ tailWord_8257580) baseStart_8257580 baseEnd_8257580 := by
    simpa [prefixWord, tailWord_8257580, baseEnd_8257580] using wordTrace_append hprefix tailTrace_8257580
  have hstable : (prefixWord ++ tailWord_8257580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257580).length < 2 ^ (prefixWord ++ tailWord_8257580).sum := by decide
  have hdescent : baseEnd_8257580 < baseStart_8257580 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257586 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 7]
def baseStart_8257586 : Nat := 118140960795 + 8257586 * 2 ^ 59
def prefixEnd_8257586 : Nat := 4983230072969 + 3 ^ 40 * 8257586 * 2
def baseEnd_8257586 : Nat := 471123407093092710055451

theorem tailTrace_8257586 : CollatzResearch.WordTrace tailWord_8257586 prefixEnd_8257586 471123407093092710055451 := by
  unfold tailWord_8257586
  simp only [CollatzResearch.WordTrace]
  refine ⟨75294726065545920063878153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200785936174789120170341741 75294726065545920063878153)
  ·
    refine ⟨56471044549159440047908615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75294726065545920063878153 56471044549159440047908615)
    ·
      refine ⟨84706566823739160071862923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56471044549159440047908615 84706566823739160071862923)
      ·
        refine ⟨127059850235608740107794385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84706566823739160071862923 127059850235608740107794385)
        ·
          refine ⟨95294887676706555080845789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127059850235608740107794385 95294887676706555080845789)
          ·
            refine ⟨35735582878764958155317171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95294887676706555080845789 35735582878764958155317171)
            ·
              refine ⟨53603374318147437232975757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35735582878764958155317171 53603374318147437232975757)
              ·
                refine ⟨20101265369305288962365909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53603374318147437232975757 20101265369305288962365909)
                ·
                  refine ⟨471123407093092710055451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20101265369305288962365909 471123407093092710055451)
                  ·
                    rfl

theorem cell23_8257586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_8257586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257586 prefixEnd_8257586 := by exact prefixLift 8257586
  have htrace : WordTrace (prefixWord ++ tailWord_8257586) baseStart_8257586 baseEnd_8257586 := by
    simpa [prefixWord, tailWord_8257586, baseEnd_8257586] using wordTrace_append hprefix tailTrace_8257586
  have hstable : (prefixWord ++ tailWord_8257586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257586).length < 2 ^ (prefixWord ++ tailWord_8257586).sum := by decide
  have hdescent : baseEnd_8257586 < baseStart_8257586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257626 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_8257626 : Nat := 118140960795 + 8257626 * 2 ^ 59
def prefixEnd_8257626 : Nat := 4983230072969 + 3 ^ 40 * 8257626 * 2
def baseEnd_8257626 : Nat := 4240131203064014233998875

theorem tailTrace_8257626 : CollatzResearch.WordTrace tailWord_8257626 prefixEnd_8257626 4240131203064014233998875 := by
  unfold tailWord_8257626
  simp only [CollatzResearch.WordTrace]
  refine ⟨75295090795509691771742183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200786908788025844724645821 75295090795509691771742183)
  ·
    refine ⟨112942636193264537657613275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75295090795509691771742183 112942636193264537657613275)
    ·
      refine ⟨169413954289896806486419913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112942636193264537657613275 169413954289896806486419913)
      ·
        refine ⟨127060465717422604864814935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169413954289896806486419913 127060465717422604864814935)
        ·
          refine ⟨190590698576133907297222403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127060465717422604864814935 190590698576133907297222403)
          ·
            refine ⟨285886047864200860945833605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190590698576133907297222403 285886047864200860945833605)
            ·
              refine ⟨53603633974537661427343801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285886047864200860945833605 53603633974537661427343801)
              ·
                refine ⟨40202725480903246070507851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53603633974537661427343801 40202725480903246070507851)
                ·
                  refine ⟨60304088221354869105761777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40202725480903246070507851 60304088221354869105761777)
                  ·
                    refine ⟨45228066166016151829321333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60304088221354869105761777 45228066166016151829321333)
                    ·
                      refine ⟨4240131203064014233998875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45228066166016151829321333 4240131203064014233998875)
                      ·
                        rfl

theorem cell23_8257626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_8257626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257626 prefixEnd_8257626 := by exact prefixLift 8257626
  have htrace : WordTrace (prefixWord ++ tailWord_8257626) baseStart_8257626 baseEnd_8257626 := by
    simpa [prefixWord, tailWord_8257626, baseEnd_8257626] using wordTrace_append hprefix tailTrace_8257626
  have hstable : (prefixWord ++ tailWord_8257626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257626).length < 2 ^ (prefixWord ++ tailWord_8257626).sum := by decide
  have hdescent : baseEnd_8257626 < baseStart_8257626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257680 : List Nat := [2, 1, 1, 1, 1, 1, 6, 5, 1, 4]
def baseStart_8257680 : Nat := 118140960795 + 8257680 * 2 ^ 59
def prefixEnd_8257680 : Nat := 4983230072969 + 3 ^ 40 * 8257680 * 2
def baseEnd_8257680 : Nat := 1413386310339785674241209

theorem tailTrace_8257680 : CollatzResearch.WordTrace tailWord_8257680 prefixEnd_8257680 1413386310339785674241209 := by
  unfold tailWord_8257680
  simp only [CollatzResearch.WordTrace]
  refine ⟨150591166361921567154717247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200788221815895422872956329 150591166361921567154717247)
  ·
    refine ⟨225886749542882350732075871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150591166361921567154717247 225886749542882350732075871)
    ·
      refine ⟨338830124314323526098113807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225886749542882350732075871 338830124314323526098113807)
      ·
        refine ⟨508245186471485289147170711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338830124314323526098113807 508245186471485289147170711)
        ·
          refine ⟨762367779707227933720756067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508245186471485289147170711 762367779707227933720756067)
          ·
            refine ⟨1143551669560841900581134101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762367779707227933720756067 1143551669560841900581134101)
            ·
              refine ⟨53603984510664464089740661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1143551669560841900581134101 53603984510664464089740661)
              ·
                refine ⟨5025373547874793508413187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53603984510664464089740661 5025373547874793508413187)
                ·
                  refine ⟨7538060321812190262619781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025373547874793508413187 7538060321812190262619781)
                  ·
                    refine ⟨1413386310339785674241209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7538060321812190262619781 1413386310339785674241209)
                    ·
                      rfl

theorem cell23_8257680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 1, 4].length) (baseStart_8257680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257680 prefixEnd_8257680 := by exact prefixLift 8257680
  have htrace : WordTrace (prefixWord ++ tailWord_8257680) baseStart_8257680 baseEnd_8257680 := by
    simpa [prefixWord, tailWord_8257680, baseEnd_8257680] using wordTrace_append hprefix tailTrace_8257680
  have hstable : (prefixWord ++ tailWord_8257680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257680).length < 2 ^ (prefixWord ++ tailWord_8257680).sum := by decide
  have hdescent : baseEnd_8257680 < baseStart_8257680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257693 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 6]
def baseStart_8257693 : Nat := 118140960795 + 8257693 * 2 ^ 59
def prefixEnd_8257693 : Nat := 4983230072969 + 3 ^ 40 * 8257693 * 2
def baseEnd_8257693 : Nat := 471129511807540607984563

theorem tailTrace_8257693 : CollatzResearch.WordTrace tailWord_8257693 prefixEnd_8257693 471129511807540607984563 := by
  unfold tailWord_8257693
  simp only [CollatzResearch.WordTrace]
  refine ⟨301182806872796037529657733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200788537915197358353105155 301182806872796037529657733)
  ·
    refine ⟨56471776288649257036810825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301182806872796037529657733 56471776288649257036810825)
    ·
      refine ⟨42353832216486942777608119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56471776288649257036810825 42353832216486942777608119)
      ·
        refine ⟨63530748324730414166412179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42353832216486942777608119 63530748324730414166412179)
        ·
          refine ⟨95296122487095621249618269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63530748324730414166412179 95296122487095621249618269)
          ·
            refine ⟨35736045932660857968606851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95296122487095621249618269 35736045932660857968606851)
            ·
              refine ⟨53604068898991286952910277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35736045932660857968606851 53604068898991286952910277)
              ·
                refine ⟨10050762918560866303670677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53604068898991286952910277 10050762918560866303670677)
                ·
                  refine ⟨471129511807540607984563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10050762918560866303670677 471129511807540607984563)
                  ·
                    rfl

theorem cell23_8257693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_8257693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257693 prefixEnd_8257693 := by exact prefixLift 8257693
  have htrace : WordTrace (prefixWord ++ tailWord_8257693) baseStart_8257693 baseEnd_8257693 := by
    simpa [prefixWord, tailWord_8257693, baseEnd_8257693] using wordTrace_append hprefix tailTrace_8257693
  have hstable : (prefixWord ++ tailWord_8257693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257693).length < 2 ^ (prefixWord ++ tailWord_8257693).sum := by decide
  have hdescent : baseEnd_8257693 < baseStart_8257693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257697 : List Nat := [1, 2, 3, 3, 1, 3, 1, 4, 1, 4]
def baseStart_8257697 : Nat := 118140960795 + 8257697 * 2 ^ 59
def prefixEnd_8257697 : Nat := 4983230072969 + 3 ^ 40 * 8257697 * 2
def baseEnd_8257697 : Nat := 1413389220063494485403683

theorem tailTrace_8257697 : CollatzResearch.WordTrace tailWord_8257697 prefixEnd_8257697 1413389220063494485403683 := by
  unfold tailWord_8257697
  simp only [CollatzResearch.WordTrace]
  refine ⟨301182952764781546212803345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200788635176521030808535563 301182952764781546212803345)
  ·
    refine ⟨225887214573586159659602509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301182952764781546212803345 225887214573586159659602509)
    ·
      refine ⟨84707705465094809872350941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225887214573586159659602509 84707705465094809872350941)
      ·
        refine ⟨31765389549410553702131603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84707705465094809872350941 31765389549410553702131603)
        ·
          refine ⟨47648084324115830553197405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31765389549410553702131603 47648084324115830553197405)
          ·
            refine ⟨17868031621543436457449027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47648084324115830553197405 17868031621543436457449027)
            ·
              refine ⟨26802047432315154686173541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17868031621543436457449027 26802047432315154686173541)
              ·
                refine ⟨5025383893559091503657539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26802047432315154686173541 5025383893559091503657539)
                ·
                  refine ⟨7538075840338637255486309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025383893559091503657539 7538075840338637255486309)
                  ·
                    refine ⟨1413389220063494485403683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7538075840338637255486309 1413389220063494485403683)
                    ·
                      rfl

theorem cell23_8257697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_8257697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257697 prefixEnd_8257697 := by exact prefixLift 8257697
  have htrace : WordTrace (prefixWord ++ tailWord_8257697) baseStart_8257697 baseEnd_8257697 := by
    simpa [prefixWord, tailWord_8257697, baseEnd_8257697] using wordTrace_append hprefix tailTrace_8257697
  have hstable : (prefixWord ++ tailWord_8257697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257697).length < 2 ^ (prefixWord ++ tailWord_8257697).sum := by decide
  have hdescent : baseEnd_8257697 < baseStart_8257697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257720 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 3, 1, 3]
def baseStart_8257720 : Nat := 118140960795 + 8257720 * 2 ^ 59
def prefixEnd_8257720 : Nat := 4983230072969 + 3 ^ 40 * 8257720 * 2
def baseEnd_8257720 : Nat := 4240179470245536866223443

theorem tailTrace_8257720 : CollatzResearch.WordTrace tailWord_8257720 prefixEnd_8257720 4240179470245536866223443 := by
  unfold tailWord_8257720
  simp only [CollatzResearch.WordTrace]
  refine ⟨150591895821849110570445307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200789194429132147427260409 150591895821849110570445307)
  ·
    refine ⟨225887843732773665855667961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150591895821849110570445307 225887843732773665855667961)
    ·
      refine ⟨169415882799580249391750971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225887843732773665855667961 169415882799580249391750971)
      ·
        refine ⟨254123824199370374087626457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169415882799580249391750971 254123824199370374087626457)
        ·
          refine ⟨190592868149527780565719843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254123824199370374087626457 190592868149527780565719843)
          ·
            refine ⟨285889302224291670848579765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190592868149527780565719843 285889302224291670848579765)
            ·
              refine ⟨26802122083527344142054353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285889302224291670848579765 26802122083527344142054353)
              ·
                refine ⟨20101591562645508106540765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26802122083527344142054353 20101591562645508106540765)
                ·
                  refine ⟨7538096835992065539952787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20101591562645508106540765 7538096835992065539952787)
                  ·
                    refine ⟨11307145253988098309929181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7538096835992065539952787 11307145253988098309929181)
                    ·
                      refine ⟨4240179470245536866223443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11307145253988098309929181 4240179470245536866223443)
                      ·
                        rfl

theorem cell23_8257720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_8257720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257720 prefixEnd_8257720 := by exact prefixLift 8257720
  have htrace : WordTrace (prefixWord ++ tailWord_8257720) baseStart_8257720 baseEnd_8257720 := by
    simpa [prefixWord, tailWord_8257720, baseEnd_8257720] using wordTrace_append hprefix tailTrace_8257720
  have hstable : (prefixWord ++ tailWord_8257720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257720).length < 2 ^ (prefixWord ++ tailWord_8257720).sum := by decide
  have hdescent : baseEnd_8257720 < baseStart_8257720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257723 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 1, 5]
def baseStart_8257723 : Nat := 118140960795 + 8257723 * 2 ^ 59
def prefixEnd_8257723 : Nat := 4983230072969 + 3 ^ 40 * 8257723 * 2
def baseEnd_8257723 : Nat := 1413393670229166784828643

theorem tailTrace_8257723 : CollatzResearch.WordTrace tailWord_8257723 prefixEnd_8257723 1413393670229166784828643 := by
  unfold tailWord_8257723
  simp only [CollatzResearch.WordTrace]
  refine ⟨301183901062687352653249823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200789267375124901768833215 301183901062687352653249823)
  ·
    refine ⟨451775851594031028979874735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301183901062687352653249823 451775851594031028979874735)
    ·
      refine ⟨677663777391046543469812103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451775851594031028979874735 677663777391046543469812103)
      ·
        refine ⟨1016495666086569815204718155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677663777391046543469812103 1016495666086569815204718155)
        ·
          refine ⟨1524743499129854722807077233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016495666086569815204718155 1524743499129854722807077233)
          ·
            refine ⟨1143557624347391042105307925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1524743499129854722807077233 1143557624347391042105307925)
            ·
              refine ⟨53604263641283955098686309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1143557624347391042105307925 53604263641283955098686309)
              ·
                refine ⟨10050799432740741581003683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53604263641283955098686309 10050799432740741581003683)
                ·
                  refine ⟨15076199149111112371505525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10050799432740741581003683 15076199149111112371505525)
                  ·
                    refine ⟨1413393670229166784828643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15076199149111112371505525 1413393670229166784828643)
                    ·
                      rfl

theorem cell23_8257723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 5].length) (baseStart_8257723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257723 prefixEnd_8257723 := by exact prefixLift 8257723
  have htrace : WordTrace (prefixWord ++ tailWord_8257723) baseStart_8257723 baseEnd_8257723 := by
    simpa [prefixWord, tailWord_8257723, baseEnd_8257723] using wordTrace_append hprefix tailTrace_8257723
  have hstable : (prefixWord ++ tailWord_8257723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257723).length < 2 ^ (prefixWord ++ tailWord_8257723).sum := by decide
  have hdescent : baseEnd_8257723 < baseStart_8257723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257724 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 2, 2, 3]
def baseStart_8257724 : Nat := 118140960795 + 8257724 * 2 ^ 59
def prefixEnd_8257724 : Nat := 4983230072969 + 3 ^ 40 * 8257724 * 2
def baseEnd_8257724 : Nat := 4240181524168154850573425

theorem tailTrace_8257724 : CollatzResearch.WordTrace tailWord_8257724 prefixEnd_8257724 4240181524168154850573425 := by
  unfold tailWord_8257724
  simp only [CollatzResearch.WordTrace]
  refine ⟨150591968767841864912018113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200789291690455819882690817 150591968767841864912018113)
  ·
    refine ⟨112943976575881398684013585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150591968767841864912018113 112943976575881398684013585)
    ·
      refine ⟨84707982431911049013010189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112943976575881398684013585 84707982431911049013010189)
      ·
        refine ⟨31765493411966643379878821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84707982431911049013010189 31765493411966643379878821)
        ·
          refine ⟨5956030014743745633727279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31765493411966643379878821 5956030014743745633727279)
          ·
            refine ⟨8934045022115618450590919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956030014743745633727279 8934045022115618450590919)
            ·
              refine ⟨13401067533173427675886379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8934045022115618450590919 13401067533173427675886379)
              ·
                refine ⟨20101601299760141513829569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13401067533173427675886379 20101601299760141513829569)
                ·
                  refine ⟨15076200974820106135372177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20101601299760141513829569 15076200974820106135372177)
                  ·
                    refine ⟨11307150731115079601529133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15076200974820106135372177 11307150731115079601529133)
                    ·
                      refine ⟨4240181524168154850573425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11307150731115079601529133 4240181524168154850573425)
                      ·
                        rfl

theorem cell23_8257724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_8257724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257724 prefixEnd_8257724 := by exact prefixLift 8257724
  have htrace : WordTrace (prefixWord ++ tailWord_8257724) baseStart_8257724 baseEnd_8257724 := by
    simpa [prefixWord, tailWord_8257724, baseEnd_8257724] using wordTrace_append hprefix tailTrace_8257724
  have hstable : (prefixWord ++ tailWord_8257724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257724).length < 2 ^ (prefixWord ++ tailWord_8257724).sum := by decide
  have hdescent : baseEnd_8257724 < baseStart_8257724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257777 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 3, 2, 2]
def baseStart_8257777 : Nat := 118140960795 + 8257777 * 2 ^ 59
def prefixEnd_8257777 : Nat := 4983230072969 + 3 ^ 40 * 8257777 * 2
def baseEnd_8257777 : Nat := 4240208738642843143210681

theorem tailTrace_8257777 : CollatzResearch.WordTrace tailWord_8257777 prefixEnd_8257777 4240208738642843143210681 := by
  unfold tailWord_8257777
  simp only [CollatzResearch.WordTrace]
  refine ⟨301185870604491719875715585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200790580402994479917143723 301185870604491719875715585)
  ·
    refine ⟨225889402953368789906786689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301185870604491719875715585 225889402953368789906786689)
    ·
      refine ⟨169417052215026592430090017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225889402953368789906786689 169417052215026592430090017)
      ·
        refine ⟨127062789161269944322567513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169417052215026592430090017 127062789161269944322567513)
        ·
          refine ⟨95297091870952458241925635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127062789161269944322567513 95297091870952458241925635)
          ·
            refine ⟨142945637806428687362888453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95297091870952458241925635 142945637806428687362888453)
            ·
              refine ⟨26802307088705378880541585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142945637806428687362888453 26802307088705378880541585)
              ·
                refine ⟨20101730316529034160406189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26802307088705378880541585 20101730316529034160406189)
                ·
                  refine ⟨7538148868698387810152321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20101730316529034160406189 7538148868698387810152321)
                  ·
                    refine ⟨5653611651523790857614241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7538148868698387810152321 5653611651523790857614241)
                    ·
                      refine ⟨4240208738642843143210681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653611651523790857614241 4240208738642843143210681)
                      ·
                        rfl

theorem cell23_8257777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_8257777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257777 prefixEnd_8257777 := by exact prefixLift 8257777
  have htrace : WordTrace (prefixWord ++ tailWord_8257777) baseStart_8257777 baseEnd_8257777 := by
    simpa [prefixWord, tailWord_8257777, baseEnd_8257777] using wordTrace_append hprefix tailTrace_8257777
  have hstable : (prefixWord ++ tailWord_8257777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257777).length < 2 ^ (prefixWord ++ tailWord_8257777).sum := by decide
  have hdescent : baseEnd_8257777 < baseStart_8257777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257790 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_8257790 : Nat := 118140960795 + 8257790 * 2 ^ 59
def prefixEnd_8257790 : Nat := 4983230072969 + 3 ^ 40 * 8257790 * 2
def baseEnd_8257790 : Nat := 4240215413891351592348121

theorem tailTrace_8257790 : CollatzResearch.WordTrace tailWord_8257790 prefixEnd_8257790 4240215413891351592348121 := by
  unfold tailWord_8257790
  simp only [CollatzResearch.WordTrace]
  refine ⟨37648293094180577886992353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200790896502296415397292549 37648293094180577886992353)
  ·
    refine ⟨28236219820635433415244265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37648293094180577886992353 28236219820635433415244265)
    ·
      refine ⟨21177164865476575061433199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28236219820635433415244265 21177164865476575061433199)
      ·
        refine ⟨31765747298214862592149799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21177164865476575061433199 31765747298214862592149799)
        ·
          refine ⟨47648620947322293888224699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31765747298214862592149799 47648620947322293888224699)
          ·
            refine ⟨71472931420983440832337049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47648620947322293888224699 71472931420983440832337049)
            ·
              refine ⟨53604698565737580624252787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71472931420983440832337049 53604698565737580624252787)
              ·
                refine ⟨80407047848606370936379181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53604698565737580624252787 80407047848606370936379181)
                ·
                  refine ⟨30152642943227389101142193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80407047848606370936379181 30152642943227389101142193)
                  ·
                    refine ⟨22614482207420541825856645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30152642943227389101142193 22614482207420541825856645)
                    ·
                      refine ⟨4240215413891351592348121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22614482207420541825856645 4240215413891351592348121)
                      ·
                        rfl

theorem cell23_8257790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_8257790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257790 prefixEnd_8257790 := by exact prefixLift 8257790
  have htrace : WordTrace (prefixWord ++ tailWord_8257790) baseStart_8257790 baseEnd_8257790 := by
    simpa [prefixWord, tailWord_8257790, baseEnd_8257790] using wordTrace_append hprefix tailTrace_8257790
  have hstable : (prefixWord ++ tailWord_8257790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257790).length < 2 ^ (prefixWord ++ tailWord_8257790).sum := by decide
  have hdescent : baseEnd_8257790 < baseStart_8257790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257820 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_8257820 : Nat := 118140960795 + 8257820 * 2 ^ 59
def prefixEnd_8257820 : Nat := 4983230072969 + 3 ^ 40 * 8257820 * 2
def baseEnd_8257820 : Nat := 4240230818310986474972983

theorem tailTrace_8257820 : CollatzResearch.WordTrace tailWord_8257820 prefixEnd_8257820 4240230818310986474972983 := by
  unfold tailWord_8257820
  simp only [CollatzResearch.WordTrace]
  refine ⟨150593719471667969109765457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200791625962223958813020609 150593719471667969109765457)
  ·
    refine ⟨112945289603750976832324093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150593719471667969109765457 112945289603750976832324093)
    ·
      refine ⟨42354483601406616312121535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112945289603750976832324093 42354483601406616312121535)
      ·
        refine ⟨63531725402109924468182303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42354483601406616312121535 63531725402109924468182303)
        ·
          refine ⟨95297588103164886702273455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63531725402109924468182303 95297588103164886702273455)
          ·
            refine ⟨142946382154747330053410183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95297588103164886702273455 142946382154747330053410183)
            ·
              refine ⟨214419573232120995080115275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142946382154747330053410183 214419573232120995080115275)
              ·
                refine ⟨321629359848181492620172913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214419573232120995080115275 321629359848181492620172913)
                ·
                  refine ⟨241222019886136119465129685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321629359848181492620172913 241222019886136119465129685)
                  ·
                    refine ⟨5653641091081315299963977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 241222019886136119465129685 5653641091081315299963977)
                    ·
                      refine ⟨4240230818310986474972983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653641091081315299963977 4240230818310986474972983)
                      ·
                        rfl

theorem cell23_8257820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_8257820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257820 prefixEnd_8257820 := by exact prefixLift 8257820
  have htrace : WordTrace (prefixWord ++ tailWord_8257820) baseStart_8257820 baseEnd_8257820 := by
    simpa [prefixWord, tailWord_8257820, baseEnd_8257820] using wordTrace_append hprefix tailTrace_8257820
  have hstable : (prefixWord ++ tailWord_8257820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257820).length < 2 ^ (prefixWord ++ tailWord_8257820).sum := by decide
  have hdescent : baseEnd_8257820 < baseStart_8257820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257821 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_8257821 : Nat := 118140960795 + 8257821 * 2 ^ 59
def prefixEnd_8257821 : Nat := 4983230072969 + 3 ^ 40 * 8257821 * 2
def baseEnd_8257821 : Nat := 1413410443930546990353493

theorem tailTrace_8257821 : CollatzResearch.WordTrace tailWord_8257821 prefixEnd_8257821 1413410443930546990353493 := by
  unfold tailWord_8257821
  simp only [CollatzResearch.WordTrace]
  refine ⟨301187475416332315390317317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200791650277554876926878211 301187475416332315390317317)
  ·
    refine ⟨56472651640562309135684497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301187475416332315390317317 56472651640562309135684497)
    ·
      refine ⟨42354488730421731851763373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56472651640562309135684497 42354488730421731851763373)
      ·
        refine ⟨15882933273908149444411265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42354488730421731851763373 15882933273908149444411265)
        ·
          refine ⟨11912199955431112083308449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15882933273908149444411265 11912199955431112083308449)
          ·
            refine ⟨8934149966573334062481337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11912199955431112083308449 8934149966573334062481337)
            ·
              refine ⟨6700612474930000546861003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8934149966573334062481337 6700612474930000546861003)
              ·
                refine ⟨10050918712395000820291505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6700612474930000546861003 10050918712395000820291505)
                ·
                  refine ⟨7538189034296250615218629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10050918712395000820291505 7538189034296250615218629)
                  ·
                    refine ⟨1413410443930546990353493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7538189034296250615218629 1413410443930546990353493)
                    ·
                      rfl

theorem cell23_8257821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_8257821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257821 prefixEnd_8257821 := by exact prefixLift 8257821
  have htrace : WordTrace (prefixWord ++ tailWord_8257821) baseStart_8257821 baseEnd_8257821 := by
    simpa [prefixWord, tailWord_8257821, baseEnd_8257821] using wordTrace_append hprefix tailTrace_8257821
  have hstable : (prefixWord ++ tailWord_8257821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257821).length < 2 ^ (prefixWord ++ tailWord_8257821).sum := by decide
  have hdescent : baseEnd_8257821 < baseStart_8257821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257827 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 2, 1, 3]
def baseStart_8257827 : Nat := 118140960795 + 8257827 * 2 ^ 59
def prefixEnd_8257827 : Nat := 4983230072969 + 3 ^ 40 * 8257827 * 2
def baseEnd_8257827 : Nat := 4240234412675567947585451

theorem tailTrace_8257827 : CollatzResearch.WordTrace tailWord_8257827 prefixEnd_8257827 4240234412675567947585451 := by
  unfold tailWord_8257827
  simp only [CollatzResearch.WordTrace]
  refine ⟨301187694254310578415035735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200791796169540385610023823 301187694254310578415035735)
  ·
    refine ⟨451781541381465867622553603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301187694254310578415035735 451781541381465867622553603)
    ·
      refine ⟨677672312072198801433830405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451781541381465867622553603 677672312072198801433830405)
      ·
        refine ⟨127063558513537275268843201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 677672312072198801433830405 127063558513537275268843201)
        ·
          refine ⟨95297668885152956451632401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127063558513537275268843201 95297668885152956451632401)
          ·
            refine ⟨71473251663864717338724301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95297668885152956451632401 71473251663864717338724301)
            ·
              refine ⟨26802469373949269002021613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71473251663864717338724301 26802469373949269002021613)
              ·
                refine ⟨10050926015230975875758105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26802469373949269002021613 10050926015230975875758105)
                ·
                  refine ⟨7538194511423231906818579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10050926015230975875758105 7538194511423231906818579)
                  ·
                    refine ⟨11307291767134847860227869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7538194511423231906818579 11307291767134847860227869)
                    ·
                      refine ⟨4240234412675567947585451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11307291767134847860227869 4240234412675567947585451)
                      ·
                        rfl

theorem cell23_8257827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_8257827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257827 prefixEnd_8257827 := by exact prefixLift 8257827
  have htrace : WordTrace (prefixWord ++ tailWord_8257827) baseStart_8257827 baseEnd_8257827 := by
    simpa [prefixWord, tailWord_8257827, baseEnd_8257827] using wordTrace_append hprefix tailTrace_8257827
  have hstable : (prefixWord ++ tailWord_8257827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257827).length < 2 ^ (prefixWord ++ tailWord_8257827).sum := by decide
  have hdescent : baseEnd_8257827 < baseStart_8257827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257831 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_8257831 : Nat := 118140960795 + 8257831 * 2 ^ 59
def prefixEnd_8257831 : Nat := 4983230072969 + 3 ^ 40 * 8257831 * 2
def baseEnd_8257831 : Nat := 4240236466598185931935433

theorem tailTrace_8257831 : CollatzResearch.WordTrace tailWord_8257831 prefixEnd_8257831 4240236466598185931935433 := by
  unfold tailWord_8257831
  simp only [CollatzResearch.WordTrace]
  refine ⟨301187840146296087098181347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200791893430864058065454231 301187840146296087098181347)
  ·
    refine ⟨451781760219444130647272021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301187840146296087098181347 451781760219444130647272021)
    ·
      refine ⟨5294317502571610906022719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 451781760219444130647272021 5294317502571610906022719)
      ·
        refine ⟨7941476253857416359034079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5294317502571610906022719 7941476253857416359034079)
        ·
          refine ⟨11912214380786124538551119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941476253857416359034079 11912214380786124538551119)
          ·
            refine ⟨17868321571179186807826679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11912214380786124538551119 17868321571179186807826679)
            ·
              refine ⟨26802482356768780211740019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17868321571179186807826679 26802482356768780211740019)
              ·
                refine ⟨40203723535153170317610029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26802482356768780211740019 40203723535153170317610029)
                ·
                  refine ⟨15076396325682438869103761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40203723535153170317610029 15076396325682438869103761)
                  ·
                    refine ⟨11307297244261829151827821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15076396325682438869103761 11307297244261829151827821)
                    ·
                      refine ⟨4240236466598185931935433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11307297244261829151827821 4240236466598185931935433)
                      ·
                        rfl

theorem cell23_8257831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_8257831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257831 prefixEnd_8257831 := by exact prefixLift 8257831
  have htrace : WordTrace (prefixWord ++ tailWord_8257831) baseStart_8257831 baseEnd_8257831 := by
    simpa [prefixWord, tailWord_8257831, baseEnd_8257831] using wordTrace_append hprefix tailTrace_8257831
  have hstable : (prefixWord ++ tailWord_8257831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257831).length < 2 ^ (prefixWord ++ tailWord_8257831).sum := by decide
  have hdescent : baseEnd_8257831 < baseStart_8257831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257890 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 9]
def baseStart_8257890 : Nat := 118140960795 + 8257890 * 2 ^ 59
def prefixEnd_8257890 : Nat := 4983230072969 + 3 ^ 40 * 8257890 * 2
def baseEnd_8257890 : Nat := 471140751328533466788629

theorem tailTrace_8257890 : CollatzResearch.WordTrace tailWord_8257890 prefixEnd_8257890 471140751328533466788629 := by
  unfold tailWord_8257890
  simp only [CollatzResearch.WordTrace]
  refine ⟨75297498013270585043644781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200793328035388226783052749 75297498013270585043644781)
  ·
    refine ⟨28236561754976469391366793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75297498013270585043644781 28236561754976469391366793)
    ·
      refine ⟨21177421316232352043525095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28236561754976469391366793 21177421316232352043525095)
      ·
        refine ⟨31766131974348528065287643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21177421316232352043525095 31766131974348528065287643)
        ·
          refine ⟨47649197961522792097931465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31766131974348528065287643 47649197961522792097931465)
          ·
            refine ⟨35736898471142094073448599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47649197961522792097931465 35736898471142094073448599)
            ·
              refine ⟨53605347706713141110172899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35736898471142094073448599 53605347706713141110172899)
              ·
                refine ⟨80408021560069711665259349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53605347706713141110172899 80408021560069711665259349)
                ·
                  refine ⟨471140751328533466788629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80408021560069711665259349 471140751328533466788629)
                  ·
                    rfl

theorem cell23_8257890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_8257890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257890 prefixEnd_8257890 := by exact prefixLift 8257890
  have htrace : WordTrace (prefixWord ++ tailWord_8257890) baseStart_8257890 baseEnd_8257890 := by
    simpa [prefixWord, tailWord_8257890, baseEnd_8257890] using wordTrace_append hprefix tailTrace_8257890
  have hstable : (prefixWord ++ tailWord_8257890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257890).length < 2 ^ (prefixWord ++ tailWord_8257890).sum := by decide
  have hdescent : baseEnd_8257890 < baseStart_8257890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257977 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 4, 2, 3]
def baseStart_8257977 : Nat := 118140960795 + 8257977 * 2 ^ 59
def prefixEnd_8257977 : Nat := 4983230072969 + 3 ^ 40 * 8257977 * 2
def baseEnd_8257977 : Nat := 4240311434773742360709761

theorem tailTrace_8257977 : CollatzResearch.WordTrace tailWord_8257977 prefixEnd_8257977 4240311434773742360709761 := by
  unfold tailWord_8257977
  simp only [CollatzResearch.WordTrace]
  refine ⟨301193165203767154032996185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200795443469178102688664123 301193165203767154032996185)
  ·
    refine ⟨225894873902825365524747139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301193165203767154032996185 225894873902825365524747139)
    ·
      refine ⟨338842310854238048287120709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225894873902825365524747139 338842310854238048287120709)
      ·
        refine ⟨63532933285169634053835133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338842310854238048287120709 63532933285169634053835133)
        ·
          refine ⟨23824849981938612770188175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63532933285169634053835133 23824849981938612770188175)
          ·
            refine ⟨35737274972907919155282263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23824849981938612770188175 35737274972907919155282263)
            ·
              refine ⟨53605912459361878732923395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35737274972907919155282263 53605912459361878732923395)
              ·
                refine ⟨80408868689042818099385093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53605912459361878732923395 80408868689042818099385093)
                ·
                  refine ⟨15076662879195528393634705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80408868689042818099385093 15076662879195528393634705)
                  ·
                    refine ⟨11307497159396646295226029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15076662879195528393634705 11307497159396646295226029)
                    ·
                      refine ⟨4240311434773742360709761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11307497159396646295226029 4240311434773742360709761)
                      ·
                        rfl

theorem cell23_8257977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_8257977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8257977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8257977 prefixEnd_8257977 := by exact prefixLift 8257977
  have htrace : WordTrace (prefixWord ++ tailWord_8257977) baseStart_8257977 baseEnd_8257977 := by
    simpa [prefixWord, tailWord_8257977, baseEnd_8257977] using wordTrace_append hprefix tailTrace_8257977
  have hstable : (prefixWord ++ tailWord_8257977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257977).length < 2 ^ (prefixWord ++ tailWord_8257977).sum := by decide
  have hdescent : baseEnd_8257977 < baseStart_8257977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258040 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 3, 6]
def baseStart_8258040 : Nat := 118140960795 + 8258040 * 2 ^ 59
def prefixEnd_8258040 : Nat := 4983230072969 + 3 ^ 40 * 8258040 * 2
def baseEnd_8258040 : Nat := 1413447928018325204740657

theorem tailTrace_8258040 : CollatzResearch.WordTrace tailWord_8258040 prefixEnd_8258040 1413447928018325204740657 := by
  unfold tailWord_8258040
  simp only [CollatzResearch.WordTrace]
  refine ⟨150597731501269457896269787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200796975335025943861693049 150597731501269457896269787)
  ·
    refine ⟨225896597251904186844404681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150597731501269457896269787 225896597251904186844404681)
    ·
      refine ⟨169422447938928140133303511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225896597251904186844404681 169422447938928140133303511)
      ·
        refine ⟨254133671908392210199955267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169422447938928140133303511 254133671908392210199955267)
        ·
          refine ⟨381200507862588315299932901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254133671908392210199955267 381200507862588315299932901)
          ·
            refine ⟨71475095224235309118737419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 381200507862588315299932901 71475095224235309118737419)
            ·
              refine ⟨107212642836352963678106129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71475095224235309118737419 107212642836352963678106129)
              ·
                refine ⟨80409482127264722758579597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107212642836352963678106129 80409482127264722758579597)
                ·
                  refine ⟨30153555797724271034467349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80409482127264722758579597 30153555797724271034467349)
                  ·
                    refine ⟨1413447928018325204740657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30153555797724271034467349 1413447928018325204740657)
                    ·
                      rfl

theorem cell23_8258040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_8258040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258040 prefixEnd_8258040 := by exact prefixLift 8258040
  have htrace : WordTrace (prefixWord ++ tailWord_8258040) baseStart_8258040 baseEnd_8258040 := by
    simpa [prefixWord, tailWord_8258040, baseEnd_8258040] using wordTrace_append hprefix tailTrace_8258040
  have hstable : (prefixWord ++ tailWord_8258040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258040).length < 2 ^ (prefixWord ++ tailWord_8258040).sum := by decide
  have hdescent : baseEnd_8258040 < baseStart_8258040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258061 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_8258061 : Nat := 118140960795 + 8258061 * 2 ^ 59
def prefixEnd_8258061 : Nat := 4983230072969 + 3 ^ 40 * 8258061 * 2
def baseEnd_8258061 : Nat := 1413451522382906677353125

theorem tailTrace_8258061 : CollatzResearch.WordTrace tailWord_8258061 prefixEnd_8258061 1413451522382906677353125 := by
  unfold tailWord_8258061
  simp only [CollatzResearch.WordTrace]
  refine ⟨301196228935462836379054037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200797485956975224252702691 301196228935462836379054037)
  ·
    refine ⟨7059286615674910227634079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 301196228935462836379054037 7059286615674910227634079)
    ·
      refine ⟨10588929923512365341451119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7059286615674910227634079 10588929923512365341451119)
      ·
        refine ⟨15883394885268548012176679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10588929923512365341451119 15883394885268548012176679)
        ·
          refine ⟨23825092327902822018265019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15883394885268548012176679 23825092327902822018265019)
          ·
            refine ⟨35737638491854233027397529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23825092327902822018265019 35737638491854233027397529)
            ·
              refine ⟨26803228868890674770548147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35737638491854233027397529 26803228868890674770548147)
              ·
                refine ⟨40204843303336012155822221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26803228868890674770548147 40204843303336012155822221)
                ·
                  refine ⟨15076816238751004558433333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40204843303336012155822221 15076816238751004558433333)
                  ·
                    refine ⟨1413451522382906677353125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15076816238751004558433333 1413451522382906677353125)
                    ·
                      rfl

theorem cell23_8258061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_8258061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258061 prefixEnd_8258061 := by exact prefixLift 8258061
  have htrace : WordTrace (prefixWord ++ tailWord_8258061) baseStart_8258061 baseEnd_8258061 := by
    simpa [prefixWord, tailWord_8258061, baseEnd_8258061] using wordTrace_append hprefix tailTrace_8258061
  have hstable : (prefixWord ++ tailWord_8258061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258061).length < 2 ^ (prefixWord ++ tailWord_8258061).sum := by decide
  have hdescent : baseEnd_8258061 < baseStart_8258061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258067 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 3]
def baseStart_8258067 : Nat := 118140960795 + 8258067 * 2 ^ 59
def prefixEnd_8258067 : Nat := 4983230072969 + 3 ^ 40 * 8258067 * 2
def baseEnd_8258067 : Nat := 4240357648032647008584347

theorem tailTrace_8258067 : CollatzResearch.WordTrace tailWord_8258067 prefixEnd_8258067 4240357648032647008584347 := by
  unfold tailWord_8258067
  simp only [CollatzResearch.WordTrace]
  refine ⟨301196447773441099403772455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200797631848960732935848303 301196447773441099403772455)
  ·
    refine ⟨451794671660161649105658683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301196447773441099403772455 451794671660161649105658683)
    ·
      refine ⟨677692007490242473658488025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451794671660161649105658683 677692007490242473658488025)
      ·
        refine ⟨508269005617681855243866019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677692007490242473658488025 508269005617681855243866019)
        ·
          refine ⟨762403508426522782865799029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508269005617681855243866019 762403508426522782865799029)
          ·
            refine ⟨71475328914986510893668659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 762403508426522782865799029 71475328914986510893668659)
            ·
              refine ⟨107212993372479766340502989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71475328914986510893668659 107212993372479766340502989)
              ·
                refine ⟨40204872514679912377688621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107212993372479766340502989 40204872514679912377688621)
                ·
                  refine ⟨15076827193004967141633233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40204872514679912377688621 15076827193004967141633233)
                  ·
                    refine ⟨11307620394753725356224925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15076827193004967141633233 11307620394753725356224925)
                    ·
                      refine ⟨4240357648032647008584347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11307620394753725356224925 4240357648032647008584347)
                      ·
                        rfl

theorem cell23_8258067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 3].length) (baseStart_8258067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258067 prefixEnd_8258067 := by exact prefixLift 8258067
  have htrace : WordTrace (prefixWord ++ tailWord_8258067) baseStart_8258067 baseEnd_8258067 := by
    simpa [prefixWord, tailWord_8258067, baseEnd_8258067] using wordTrace_append hprefix tailTrace_8258067
  have hstable : (prefixWord ++ tailWord_8258067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258067).length < 2 ^ (prefixWord ++ tailWord_8258067).sum := by decide
  have hdescent : baseEnd_8258067 < baseStart_8258067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258068 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_8258068 : Nat := 118140960795 + 8258068 * 2 ^ 59
def prefixEnd_8258068 : Nat := 4983230072969 + 3 ^ 40 * 8258068 * 2
def baseEnd_8258068 : Nat := 4240358161513301504671843

theorem tailTrace_8258068 : CollatzResearch.WordTrace tailWord_8258068 prefixEnd_8258068 4240358161513301504671843 := by
  unfold tailWord_8258068
  simp only [CollatzResearch.WordTrace]
  refine ⟨150598242123218738287279429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200797656164291651049705905 150598242123218738287279429)
  ·
    refine ⟨28237170398103513428864893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150598242123218738287279429 28237170398103513428864893)
    ·
      refine ⟨10588938899288817535824335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28237170398103513428864893 10588938899288817535824335)
      ·
        refine ⟨15883408348933226303736503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10588938899288817535824335 15883408348933226303736503)
        ·
          refine ⟨23825112523399839455604755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15883408348933226303736503 23825112523399839455604755)
          ·
            refine ⟨35737668785099759183407133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23825112523399839455604755 35737668785099759183407133)
            ·
              refine ⟨13401625794412409693777675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35737668785099759183407133 13401625794412409693777675)
              ·
                refine ⟨20102438691618614540666513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13401625794412409693777675 20102438691618614540666513)
                ·
                  refine ⟨15076829018713960905499885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20102438691618614540666513 15076829018713960905499885)
                  ·
                    refine ⟨5653810882017735339562457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15076829018713960905499885 5653810882017735339562457)
                    ·
                      refine ⟨4240358161513301504671843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653810882017735339562457 4240358161513301504671843)
                      ·
                        rfl

theorem cell23_8258068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_8258068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258068 prefixEnd_8258068 := by exact prefixLift 8258068
  have htrace : WordTrace (prefixWord ++ tailWord_8258068) baseStart_8258068 baseEnd_8258068 := by
    simpa [prefixWord, tailWord_8258068, baseEnd_8258068] using wordTrace_append hprefix tailTrace_8258068
  have hstable : (prefixWord ++ tailWord_8258068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258068).length < 2 ^ (prefixWord ++ tailWord_8258068).sum := by decide
  have hdescent : baseEnd_8258068 < baseStart_8258068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258097 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 3, 3, 3]
def baseStart_8258097 : Nat := 118140960795 + 8258097 * 2 ^ 59
def prefixEnd_8258097 : Nat := 4983230072969 + 3 ^ 40 * 8258097 * 2
def baseEnd_8258097 : Nat := 4240373052452281891209209

theorem tailTrace_8258097 : CollatzResearch.WordTrace tailWord_8258097 prefixEnd_8258097 4240373052452281891209209 := by
  unfold tailWord_8258097
  simp only [CollatzResearch.WordTrace]
  refine ⟨301197541963332414527364545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200798361308888276351576363 301197541963332414527364545)
  ·
    refine ⟨225898156472499310895523409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301197541963332414527364545 225898156472499310895523409)
    ·
      refine ⟨169423617354374483171642557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225898156472499310895523409 169423617354374483171642557)
      ·
        refine ⟨63533856507890431189365959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169423617354374483171642557 63533856507890431189365959)
        ·
          refine ⟨95300784761835646784048939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63533856507890431189365959 95300784761835646784048939)
          ·
            refine ⟨142951177142753470176073409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95300784761835646784048939 142951177142753470176073409)
            ·
              refine ⟨107213382857065102632055057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142951177142753470176073409 107213382857065102632055057)
              ·
                refine ⟨80410037142798826974041293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107213382857065102632055057 80410037142798826974041293)
                ·
                  refine ⟨30153763928549560115265485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80410037142798826974041293 30153763928549560115265485)
                  ·
                    refine ⟨11307661473206085043224557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30153763928549560115265485 11307661473206085043224557)
                    ·
                      refine ⟨4240373052452281891209209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11307661473206085043224557 4240373052452281891209209)
                      ·
                        rfl

theorem cell23_8258097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_8258097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258097 prefixEnd_8258097 := by exact prefixLift 8258097
  have htrace : WordTrace (prefixWord ++ tailWord_8258097) baseStart_8258097 baseEnd_8258097 := by
    simpa [prefixWord, tailWord_8258097, baseEnd_8258097] using wordTrace_append hprefix tailTrace_8258097
  have hstable : (prefixWord ++ tailWord_8258097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258097).length < 2 ^ (prefixWord ++ tailWord_8258097).sum := by decide
  have hdescent : baseEnd_8258097 < baseStart_8258097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258098 : List Nat := [3, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2]
def baseStart_8258098 : Nat := 118140960795 + 8258098 * 2 ^ 59
def prefixEnd_8258098 : Nat := 4983230072969 + 3 ^ 40 * 8258098 * 2
def baseEnd_8258098 : Nat := 4240373565932936387296705

theorem tailTrace_8258098 : CollatzResearch.WordTrace tailWord_8258098 prefixEnd_8258098 4240373565932936387296705 := by
  unfold tailWord_8258098
  simp only [CollatzResearch.WordTrace]
  refine ⟨75299394609082197924537737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200798385624219194465433965 75299394609082197924537737)
  ·
    refine ⟨56474545956811648443403303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75299394609082197924537737 56474545956811648443403303)
    ·
      refine ⟨84711818935217472665104955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56474545956811648443403303 84711818935217472665104955)
      ·
        refine ⟨127067728402826208997657433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84711818935217472665104955 127067728402826208997657433)
        ·
          refine ⟨95300796302119656748243075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127067728402826208997657433 95300796302119656748243075)
          ·
            refine ⟨142951194453179485122364613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95300796302119656748243075 142951194453179485122364613)
            ·
              refine ⟨26803348959971153460443365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142951194453179485122364613 26803348959971153460443365)
              ·
                refine ⟨5025627929994591273833131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26803348959971153460443365 5025627929994591273833131)
                ·
                  refine ⟨7538441894991886910749697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025627929994591273833131 7538441894991886910749697)
                  ·
                    refine ⟨5653831421243915183062273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7538441894991886910749697 5653831421243915183062273)
                    ·
                      refine ⟨4240373565932936387296705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653831421243915183062273 4240373565932936387296705)
                      ·
                        rfl

theorem cell23_8258098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_8258098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258098 prefixEnd_8258098 := by exact prefixLift 8258098
  have htrace : WordTrace (prefixWord ++ tailWord_8258098) baseStart_8258098 baseEnd_8258098 := by
    simpa [prefixWord, tailWord_8258098, baseEnd_8258098] using wordTrace_append hprefix tailTrace_8258098
  have hstable : (prefixWord ++ tailWord_8258098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258098).length < 2 ^ (prefixWord ++ tailWord_8258098).sum := by decide
  have hdescent : baseEnd_8258098 < baseStart_8258098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258118 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_8258118 : Nat := 118140960795 + 8258118 * 2 ^ 59
def prefixEnd_8258118 : Nat := 4983230072969 + 3 ^ 40 * 8258118 * 2
def baseEnd_8258118 : Nat := 4240383835546026309046613

theorem tailTrace_8258118 : CollatzResearch.WordTrace tailWord_8258118 prefixEnd_8258118 4240383835546026309046613 := by
  unfold tailWord_8258118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9412447121758010472308719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 200798871930837556742586005 9412447121758010472308719)
  ·
    refine ⟨14118670682637015708463079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9412447121758010472308719 14118670682637015708463079)
    ·
      refine ⟨21178006023955523562694619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14118670682637015708463079 21178006023955523562694619)
      ·
        refine ⟨31767009035933285344041929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21178006023955523562694619 31767009035933285344041929)
        ·
          refine ⟨23825256776949964008031447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31767009035933285344041929 23825256776949964008031447)
          ·
            refine ⟨35737885165424946012047171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23825256776949964008031447 35737885165424946012047171)
            ·
              refine ⟨53606827748137419018070757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35737885165424946012047171 53606827748137419018070757)
              ·
                refine ⟨10051280202775766065888267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53606827748137419018070757 10051280202775766065888267)
                ·
                  refine ⟨15076920304163649098832401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10051280202775766065888267 15076920304163649098832401)
                  ·
                    refine ⟨11307690228122736824124301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15076920304163649098832401 11307690228122736824124301)
                    ·
                      refine ⟨4240383835546026309046613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11307690228122736824124301 4240383835546026309046613)
                      ·
                        rfl

theorem cell23_8258118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_8258118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258118 prefixEnd_8258118 := by exact prefixLift 8258118
  have htrace : WordTrace (prefixWord ++ tailWord_8258118) baseStart_8258118 baseEnd_8258118 := by
    simpa [prefixWord, tailWord_8258118, baseEnd_8258118] using wordTrace_append hprefix tailTrace_8258118
  have hstable : (prefixWord ++ tailWord_8258118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258118).length < 2 ^ (prefixWord ++ tailWord_8258118).sum := by decide
  have hdescent : baseEnd_8258118 < baseStart_8258118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258167 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_8258167 : Nat := 118140960795 + 8258167 * 2 ^ 59
def prefixEnd_8258167 : Nat := 4983230072969 + 3 ^ 40 * 8258167 * 2
def baseEnd_8258167 : Nat := 4240408996098096617333887

theorem tailTrace_8258167 : CollatzResearch.WordTrace tailWord_8258167 prefixEnd_8258167 4240408996098096617333887 := by
  unfold tailWord_8258167
  simp only [CollatzResearch.WordTrace]
  refine ⟨301200095073078816482412755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200800063382052544321608503 301200095073078816482412755)
  ·
    refine ⟨451800142609618224723619133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301200095073078816482412755 451800142609618224723619133)
    ·
      refine ⟨169425053478606834271357175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451800142609618224723619133 169425053478606834271357175)
      ·
        refine ⟨254137580217910251407035763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169425053478606834271357175 254137580217910251407035763)
        ·
          refine ⟨381206370326865377110553645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254137580217910251407035763 381206370326865377110553645)
          ·
            refine ⟨142952388872574516416457617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381206370326865377110553645 142952388872574516416457617)
            ·
              refine ⟨107214291654430887312343213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142952388872574516416457617 107214291654430887312343213)
              ·
                refine ⟨40205359370411582742128705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107214291654430887312343213 40205359370411582742128705)
                ·
                  refine ⟨30154019527808687056596529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40205359370411582742128705 30154019527808687056596529)
                  ·
                    refine ⟨22615514645856515292447397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30154019527808687056596529 22615514645856515292447397)
                    ·
                      refine ⟨4240408996098096617333887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22615514645856515292447397 4240408996098096617333887)
                      ·
                        rfl

theorem cell23_8258167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_8258167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258167 prefixEnd_8258167 := by exact prefixLift 8258167
  have htrace : WordTrace (prefixWord ++ tailWord_8258167) baseStart_8258167 baseEnd_8258167 := by
    simpa [prefixWord, tailWord_8258167, baseEnd_8258167] using wordTrace_append hprefix tailTrace_8258167
  have hstable : (prefixWord ++ tailWord_8258167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258167).length < 2 ^ (prefixWord ++ tailWord_8258167).sum := by decide
  have hdescent : baseEnd_8258167 < baseStart_8258167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258177 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 9]
def baseStart_8258177 : Nat := 118140960795 + 8258177 * 2 ^ 59
def prefixEnd_8258177 : Nat := 4983230072969 + 3 ^ 40 * 8258177 * 2
def baseEnd_8258177 : Nat := 471157125656071286467649

theorem tailTrace_8258177 : CollatzResearch.WordTrace tailWord_8258177 prefixEnd_8258177 471157125656071286467649 := by
  unfold tailWord_8258177
  simp only [CollatzResearch.WordTrace]
  refine ⟨301200459803042588190276785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200800306535361725460184523 301200459803042588190276785)
  ·
    refine ⟨225900344852281941142707589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301200459803042588190276785 225900344852281941142707589)
    ·
      refine ⟨42356314659802863964257673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225900344852281941142707589 42356314659802863964257673)
      ·
        refine ⟨31767235994852147973193255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42356314659802863964257673 31767235994852147973193255)
        ·
          refine ⟨47650853992278221959789883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31767235994852147973193255 47650853992278221959789883)
          ·
            refine ⟨71476280988417332939684825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47650853992278221959789883 71476280988417332939684825)
            ·
              refine ⟨53607210741312999704763619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71476280988417332939684825 53607210741312999704763619)
              ·
                refine ⟨80410816111969499557145429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53607210741312999704763619 80410816111969499557145429)
                ·
                  refine ⟨471157125656071286467649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80410816111969499557145429 471157125656071286467649)
                  ·
                    rfl

theorem cell23_8258177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 9].length) (baseStart_8258177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258177 prefixEnd_8258177 := by exact prefixLift 8258177
  have htrace : WordTrace (prefixWord ++ tailWord_8258177) baseStart_8258177 baseEnd_8258177 := by
    simpa [prefixWord, tailWord_8258177, baseEnd_8258177] using wordTrace_append hprefix tailTrace_8258177
  have hstable : (prefixWord ++ tailWord_8258177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258177).length < 2 ^ (prefixWord ++ tailWord_8258177).sum := by decide
  have hdescent : baseEnd_8258177 < baseStart_8258177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258187 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 3]
def baseStart_8258187 : Nat := 118140960795 + 8258187 * 2 ^ 59
def prefixEnd_8258187 : Nat := 4983230072969 + 3 ^ 40 * 8258187 * 2
def baseEnd_8258187 : Nat := 4240419265711186539083795

theorem tailTrace_8258187 : CollatzResearch.WordTrace tailWord_8258187 prefixEnd_8258187 4240419265711186539083795 := by
  unfold tailWord_8258187
  simp only [CollatzResearch.WordTrace]
  refine ⟨301200824533006359898140815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200800549688670906598760543 301200824533006359898140815)
  ·
    refine ⟨451801236799509539847211223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301200824533006359898140815 451801236799509539847211223)
    ·
      refine ⟨677701855199264309770816835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451801236799509539847211223 677701855199264309770816835)
      ·
        refine ⟨1016552782798896464656225253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677701855199264309770816835 1016552782798896464656225253)
        ·
          refine ⟨190603646774793087123042235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1016552782798896464656225253 190603646774793087123042235)
          ·
            refine ⟨285905470162189630684563353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190603646774793087123042235 285905470162189630684563353)
            ·
              refine ⟨214429102621642223013422515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285905470162189630684563353 214429102621642223013422515)
              ·
                refine ⟨321643653932463334520133773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214429102621642223013422515 321643653932463334520133773)
                ·
                  refine ⟨120616370224673750445050165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321643653932463334520133773 120616370224673750445050165)
                  ·
                    refine ⟨11307784708563164104223453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120616370224673750445050165 11307784708563164104223453)
                    ·
                      refine ⟨4240419265711186539083795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11307784708563164104223453 4240419265711186539083795)
                      ·
                        rfl

theorem cell23_8258187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 3].length) (baseStart_8258187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258187 prefixEnd_8258187 := by exact prefixLift 8258187
  have htrace : WordTrace (prefixWord ++ tailWord_8258187) baseStart_8258187 baseEnd_8258187 := by
    simpa [prefixWord, tailWord_8258187, baseEnd_8258187] using wordTrace_append hprefix tailTrace_8258187
  have hstable : (prefixWord ++ tailWord_8258187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258187).length < 2 ^ (prefixWord ++ tailWord_8258187).sum := by decide
  have hdescent : baseEnd_8258187 < baseStart_8258187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258218 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_8258218 : Nat := 118140960795 + 8258218 * 2 ^ 59
def prefixEnd_8258218 : Nat := 4983230072969 + 3 ^ 40 * 8258218 * 2
def baseEnd_8258218 : Nat := 4240435183611475917796153

theorem tailTrace_8258218 : CollatzResearch.WordTrace tailWord_8258218 prefixEnd_8258218 4240435183611475917796153 := by
  unfold tailWord_8258218
  simp only [CollatzResearch.WordTrace]
  refine ⟨75300488798973513048129827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200801303463929368128346205 75300488798973513048129827)
  ·
    refine ⟨112950733198460269572194741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75300488798973513048129827 112950733198460269572194741)
    ·
      refine ⟨10589131237355650272393257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112950733198460269572194741 10589131237355650272393257)
      ·
        refine ⟨7941848428016737704294943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10589131237355650272393257 7941848428016737704294943)
        ·
          refine ⟨11912772642025106556442415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941848428016737704294943 11912772642025106556442415)
          ·
            refine ⟨17869158963037659834663623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11912772642025106556442415 17869158963037659834663623)
            ·
              refine ⟨26803738444556489751995435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17869158963037659834663623 26803738444556489751995435)
              ·
                refine ⟨40205607666834734627993153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26803738444556489751995435 40205607666834734627993153)
                ·
                  refine ⟨30154205750126050970994865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40205607666834734627993153 30154205750126050970994865)
                  ·
                    refine ⟨22615654312594538228246149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30154205750126050970994865 22615654312594538228246149)
                    ·
                      refine ⟨4240435183611475917796153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22615654312594538228246149 4240435183611475917796153)
                      ·
                        rfl

theorem cell23_8258218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_8258218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258218 prefixEnd_8258218 := by exact prefixLift 8258218
  have htrace : WordTrace (prefixWord ++ tailWord_8258218) baseStart_8258218 baseEnd_8258218 := by
    simpa [prefixWord, tailWord_8258218, baseEnd_8258218] using wordTrace_append hprefix tailTrace_8258218
  have hstable : (prefixWord ++ tailWord_8258218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258218).length < 2 ^ (prefixWord ++ tailWord_8258218).sum := by decide
  have hdescent : baseEnd_8258218 < baseStart_8258218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258221 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_8258221 : Nat := 118140960795 + 8258221 * 2 ^ 59
def prefixEnd_8258221 : Nat := 4983230072969 + 3 ^ 40 * 8258221 * 2
def baseEnd_8258221 : Nat := 4240436724053439406058639

theorem tailTrace_8258221 : CollatzResearch.WordTrace tailWord_8258221 prefixEnd_8258221 4240436724053439406058639 := by
  unfold tailWord_8258221
  simp only [CollatzResearch.WordTrace]
  refine ⟨301202064614883183704878517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200801376409922122469919011 301202064614883183704878517)
  ·
    refine ⟨28237693557645298472332361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301202064614883183704878517 28237693557645298472332361)
    ·
      refine ⟨21178270168233973854249271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28237693557645298472332361 21178270168233973854249271)
      ·
        refine ⟨31767405252350960781373907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21178270168233973854249271 31767405252350960781373907)
        ·
          refine ⟨47651107878526441172060861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31767405252350960781373907 47651107878526441172060861)
          ·
            refine ⟨17869165454447415439522823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47651107878526441172060861 17869165454447415439522823)
            ·
              refine ⟨26803748181671123159284235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17869165454447415439522823 26803748181671123159284235)
              ·
                refine ⟨40205622272506684738926353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26803748181671123159284235 40205622272506684738926353)
                ·
                  refine ⟨30154216704380013554194765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40205622272506684738926353 30154216704380013554194765)
                  ·
                    refine ⟨11307831264142505082823037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30154216704380013554194765 11307831264142505082823037)
                    ·
                      refine ⟨4240436724053439406058639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11307831264142505082823037 4240436724053439406058639)
                      ·
                        rfl

theorem cell23_8258221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_8258221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258221 prefixEnd_8258221 := by exact prefixLift 8258221
  have htrace : WordTrace (prefixWord ++ tailWord_8258221) baseStart_8258221 baseEnd_8258221 := by
    simpa [prefixWord, tailWord_8258221, baseEnd_8258221] using wordTrace_append hprefix tailTrace_8258221
  have hstable : (prefixWord ++ tailWord_8258221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258221).length < 2 ^ (prefixWord ++ tailWord_8258221).sum := by decide
  have hdescent : baseEnd_8258221 < baseStart_8258221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258247 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_8258247 : Nat := 118140960795 + 8258247 * 2 ^ 59
def prefixEnd_8258247 : Nat := 4983230072969 + 3 ^ 40 * 8258247 * 2
def baseEnd_8258247 : Nat := 4240450074550456304333519

theorem tailTrace_8258247 : CollatzResearch.WordTrace tailWord_8258247 prefixEnd_8258247 4240450074550456304333519 := by
  unfold tailWord_8258247
  simp only [CollatzResearch.WordTrace]
  refine ⟨301203012912788990145324995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200802008608525993430216663 301203012912788990145324995)
  ·
    refine ⟨451804519369183485217987493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301203012912788990145324995 451804519369183485217987493)
    ·
      refine ⟨84713347381721903478372655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451804519369183485217987493 84713347381721903478372655)
      ·
        refine ⟨127070021072582855217558983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84713347381721903478372655 127070021072582855217558983)
        ·
          refine ⟨190605031608874282826338475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127070021072582855217558983 190605031608874282826338475)
          ·
            refine ⟨285907547413311424239507713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190605031608874282826338475 285907547413311424239507713)
            ·
              refine ⟨214430660559983568179630785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285907547413311424239507713 214430660559983568179630785)
              ·
                refine ⟨160822995419987676134723089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214430660559983568179630785 160822995419987676134723089)
                ·
                  refine ⟨120617246564990757101042317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160822995419987676134723089 120617246564990757101042317)
                  ·
                    refine ⟨45231467461871533912890869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120617246564990757101042317 45231467461871533912890869)
                    ·
                      refine ⟨4240450074550456304333519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45231467461871533912890869 4240450074550456304333519)
                      ·
                        rfl

theorem cell23_8258247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_8258247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258247 prefixEnd_8258247 := by exact prefixLift 8258247
  have htrace : WordTrace (prefixWord ++ tailWord_8258247) baseStart_8258247 baseEnd_8258247 := by
    simpa [prefixWord, tailWord_8258247, baseEnd_8258247] using wordTrace_append hprefix tailTrace_8258247
  have hstable : (prefixWord ++ tailWord_8258247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258247).length < 2 ^ (prefixWord ++ tailWord_8258247).sum := by decide
  have hdescent : baseEnd_8258247 < baseStart_8258247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258257 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_8258257 : Nat := 118140960795 + 8258257 * 2 ^ 59
def prefixEnd_8258257 : Nat := 4983230072969 + 3 ^ 40 * 8258257 * 2
def baseEnd_8258257 : Nat := 4240455209357001265208473

theorem tailTrace_8258257 : CollatzResearch.WordTrace tailWord_8258257 prefixEnd_8258257 4240455209357001265208473 := by
  unfold tailWord_8258257
  simp only [CollatzResearch.WordTrace]
  refine ⟨301203377642752761853189025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200802251761835174568792683 301203377642752761853189025)
  ·
    refine ⟨225902533232064571389891769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301203377642752761853189025 225902533232064571389891769)
    ·
      refine ⟨169426899924048428542418827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225902533232064571389891769 169426899924048428542418827)
      ·
        refine ⟨254140349886072642813628241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169426899924048428542418827 254140349886072642813628241)
        ·
          refine ⟨190605262414554482110221181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254140349886072642813628241 190605262414554482110221181)
          ·
            refine ⟨71476973405457930791332943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190605262414554482110221181 71476973405457930791332943)
            ·
              refine ⟨107215460108186896186999415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71476973405457930791332943 107215460108186896186999415)
              ·
                refine ⟨160823190162280344280499123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107215460108186896186999415 160823190162280344280499123)
                ·
                  refine ⟨241234785243420516420748685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160823190162280344280499123 241234785243420516420748685)
                  ·
                    refine ⟨90463044466282693657780757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241234785243420516420748685 90463044466282693657780757)
                    ·
                      refine ⟨4240455209357001265208473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90463044466282693657780757 4240455209357001265208473)
                      ·
                        rfl

theorem cell23_8258257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_8258257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258257 prefixEnd_8258257 := by exact prefixLift 8258257
  have htrace : WordTrace (prefixWord ++ tailWord_8258257) baseStart_8258257 baseEnd_8258257 := by
    simpa [prefixWord, tailWord_8258257, baseEnd_8258257] using wordTrace_append hprefix tailTrace_8258257
  have hstable : (prefixWord ++ tailWord_8258257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258257).length < 2 ^ (prefixWord ++ tailWord_8258257).sum := by decide
  have hdescent : baseEnd_8258257 < baseStart_8258257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258271 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 3, 4]
def baseStart_8258271 : Nat := 118140960795 + 8258271 * 2 ^ 59
def prefixEnd_8258271 : Nat := 4983230072969 + 3 ^ 40 * 8258271 * 2
def baseEnd_8258271 : Nat := 1413487466028721403477803

theorem tailTrace_8258271 : CollatzResearch.WordTrace tailWord_8258271 prefixEnd_8258271 1413487466028721403477803 := by
  unfold tailWord_8258271
  simp only [CollatzResearch.WordTrace]
  refine ⟨301203888264702042244198667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200802592176468028162799111 301203888264702042244198667)
  ·
    refine ⟨451805832397053063366298001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301203888264702042244198667 451805832397053063366298001)
    ·
      refine ⟨338854374297789797524723501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451805832397053063366298001 338854374297789797524723501)
      ·
        refine ⟨127070390361671174071771313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338854374297789797524723501 127070390361671174071771313)
        ·
          refine ⟨95302792771253380553828485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127070390361671174071771313 95302792771253380553828485)
          ·
            refine ⟨17869273644610008853842841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95302792771253380553828485 17869273644610008853842841)
            ·
              refine ⟨13401955233457506640382131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17869273644610008853842841 13401955233457506640382131)
              ·
                refine ⟨20102932850186259960573197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13401955233457506640382131 20102932850186259960573197)
                ·
                  refine ⟨7538599818819847485214949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20102932850186259960573197 7538599818819847485214949)
                  ·
                    refine ⟨1413487466028721403477803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7538599818819847485214949 1413487466028721403477803)
                    ·
                      rfl

theorem cell23_8258271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 4].length) (baseStart_8258271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258271 prefixEnd_8258271 := by exact prefixLift 8258271
  have htrace : WordTrace (prefixWord ++ tailWord_8258271) baseStart_8258271 baseEnd_8258271 := by
    simpa [prefixWord, tailWord_8258271, baseEnd_8258271] using wordTrace_append hprefix tailTrace_8258271
  have hstable : (prefixWord ++ tailWord_8258271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258271).length < 2 ^ (prefixWord ++ tailWord_8258271).sum := by decide
  have hdescent : baseEnd_8258271 < baseStart_8258271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258297 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 2, 9]
def baseStart_8258297 : Nat := 118140960795 + 8258297 * 2 ^ 59
def prefixEnd_8258297 : Nat := 4983230072969 + 3 ^ 40 * 8258297 * 2
def baseEnd_8258297 : Nat := 1413491916194393702902763

theorem tailTrace_8258297 : CollatzResearch.WordTrace tailWord_8258297 prefixEnd_8258297 1413491916194393702902763 := by
  unfold tailWord_8258297
  simp only [CollatzResearch.WordTrace]
  refine ⟨301204836562607848684645145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200803224375071899123096763 301204836562607848684645145)
  ·
    refine ⟨225903627421955886513483859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301204836562607848684645145 225903627421955886513483859)
    ·
      refine ⟨338855441132933829770225789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225903627421955886513483859 338855441132933829770225789)
      ·
        refine ⟨127070790424850186163834671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338855441132933829770225789 127070790424850186163834671)
        ·
          refine ⟨190606185637275279245752007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127070790424850186163834671 190606185637275279245752007)
          ·
            refine ⟨285909278455912918868628011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190606185637275279245752007 285909278455912918868628011)
            ·
              refine ⟨428863917683869378302942017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285909278455912918868628011 428863917683869378302942017)
              ·
                refine ⟨321647938262902033727206513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428863917683869378302942017 321647938262902033727206513)
                ·
                  refine ⟨241235953697176525295404885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321647938262902033727206513 241235953697176525295404885)
                  ·
                    refine ⟨1413491916194393702902763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 241235953697176525295404885 1413491916194393702902763)
                    ·
                      rfl

theorem cell23_8258297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_8258297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258297 prefixEnd_8258297 := by exact prefixLift 8258297
  have htrace : WordTrace (prefixWord ++ tailWord_8258297) baseStart_8258297 baseEnd_8258297 := by
    simpa [prefixWord, tailWord_8258297, baseEnd_8258297] using wordTrace_append hprefix tailTrace_8258297
  have hstable : (prefixWord ++ tailWord_8258297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258297).length < 2 ^ (prefixWord ++ tailWord_8258297).sum := by decide
  have hdescent : baseEnd_8258297 < baseStart_8258297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258321 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 4, 3, 2]
def baseStart_8258321 : Nat := 118140960795 + 8258321 * 2 ^ 59
def prefixEnd_8258321 : Nat := 4983230072969 + 3 ^ 40 * 8258321 * 2
def baseEnd_8258321 : Nat := 4240488072118889014808179

theorem tailTrace_8258321 : CollatzResearch.WordTrace tailWord_8258321 prefixEnd_8258321 4240488072118889014808179 := by
  unfold tailWord_8258321
  simp only [CollatzResearch.WordTrace]
  refine ⟨301205711914520900783518817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200803807943013933855679211 301205711914520900783518817)
  ·
    refine ⟨225904283935890675587639113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301205711914520900783518817 225904283935890675587639113)
    ·
      refine ⟨169428212951918006690729335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225904283935890675587639113 169428212951918006690729335)
      ·
        refine ⟨254142319427877010036094003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169428212951918006690729335 254142319427877010036094003)
        ·
          refine ⟨381213479141815515054141005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254142319427877010036094003 381213479141815515054141005)
          ·
            refine ⟨142955054678180818145302877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381213479141815515054141005 142955054678180818145302877)
            ·
              refine ⟨53608145504317806804488579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142955054678180818145302877 53608145504317806804488579)
              ·
                refine ⟨80412218256476710206732869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53608145504317806804488579 80412218256476710206732869)
                ·
                  refine ⟨15077290923089383163762413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80412218256476710206732869 15077290923089383163762413)
                  ·
                    refine ⟨5653984096158518686410905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15077290923089383163762413 5653984096158518686410905)
                    ·
                      refine ⟨4240488072118889014808179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5653984096158518686410905 4240488072118889014808179)
                      ·
                        rfl

theorem cell23_8258321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 3, 2].length) (baseStart_8258321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258321 prefixEnd_8258321 := by exact prefixLift 8258321
  have htrace : WordTrace (prefixWord ++ tailWord_8258321) baseStart_8258321 baseEnd_8258321 := by
    simpa [prefixWord, tailWord_8258321, baseEnd_8258321] using wordTrace_append hprefix tailTrace_8258321
  have hstable : (prefixWord ++ tailWord_8258321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258321).length < 2 ^ (prefixWord ++ tailWord_8258321).sum := by decide
  have hdescent : baseEnd_8258321 < baseStart_8258321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258322 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_8258322 : Nat := 118140960795 + 8258322 * 2 ^ 59
def prefixEnd_8258322 : Nat := 4983230072969 + 3 ^ 40 * 8258322 * 2
def baseEnd_8258322 : Nat := 1413496195199847836965225

theorem tailTrace_8258322 : CollatzResearch.WordTrace tailWord_8258322 prefixEnd_8258322 1413496195199847836965225 := by
  unfold tailWord_8258322
  simp only [CollatzResearch.WordTrace]
  refine ⟨75301437096879319488576305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200803832258344851969536813 75301437096879319488576305)
  ·
    refine ⟨56476077822659489616432229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75301437096879319488576305 56476077822659489616432229)
    ·
      refine ⟨10589264591748654303081043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56476077822659489616432229 10589264591748654303081043)
      ·
        refine ⟨15883896887622981454621565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10589264591748654303081043 15883896887622981454621565)
        ·
          refine ⟨5956461332858618045483087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15883896887622981454621565 5956461332858618045483087)
          ·
            refine ⟨8934691999287927068224631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956461332858618045483087 8934691999287927068224631)
            ·
              refine ⟨13402037998931890602336947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8934691999287927068224631 13402037998931890602336947)
              ·
                refine ⟨20103056998397835903505421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13402037998931890602336947 20103056998397835903505421)
                ·
                  refine ⟨7538646374399188463814533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20103056998397835903505421 7538646374399188463814533)
                  ·
                    refine ⟨1413496195199847836965225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7538646374399188463814533 1413496195199847836965225)
                    ·
                      rfl

theorem cell23_8258322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_8258322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258322 prefixEnd_8258322 := by exact prefixLift 8258322
  have htrace : WordTrace (prefixWord ++ tailWord_8258322) baseStart_8258322 baseEnd_8258322 := by
    simpa [prefixWord, tailWord_8258322, baseEnd_8258322] using wordTrace_append hprefix tailTrace_8258322
  have hstable : (prefixWord ++ tailWord_8258322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258322).length < 2 ^ (prefixWord ++ tailWord_8258322).sum := by decide
  have hdescent : baseEnd_8258322 < baseStart_8258322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258365 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_8258365 : Nat := 118140960795 + 8258365 * 2 ^ 59
def prefixEnd_8258365 : Nat := 4983230072969 + 3 ^ 40 * 8258365 * 2
def baseEnd_8258365 : Nat := 1413503555089228947552659

theorem tailTrace_8258365 : CollatzResearch.WordTrace tailWord_8258365 prefixEnd_8258365 1413503555089228947552659 := by
  unfold tailWord_8258365
  simp only [CollatzResearch.WordTrace]
  refine ⟨301207316726361496298120549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200804877817574330865413699 301207316726361496298120549)
  ·
    refine ⟨56476371886192780555897603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301207316726361496298120549 56476371886192780555897603)
    ·
      refine ⟨84714557829289170833846405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56476371886192780555897603 84714557829289170833846405)
      ·
        refine ⟨15883979592991719531346201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84714557829289170833846405 15883979592991719531346201)
        ·
          refine ⟨11912984694743789648509651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15883979592991719531346201 11912984694743789648509651)
          ·
            refine ⟨17869477042115684472764477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11912984694743789648509651 17869477042115684472764477)
            ·
              refine ⟨6701053890793381677286679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17869477042115684472764477 6701053890793381677286679)
              ·
                refine ⟨10051580836190072515930019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701053890793381677286679 10051580836190072515930019)
                ·
                  refine ⟨15077371254285108773895029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10051580836190072515930019 15077371254285108773895029)
                  ·
                    refine ⟨1413503555089228947552659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15077371254285108773895029 1413503555089228947552659)
                    ·
                      rfl

theorem cell23_8258365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_8258365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258365 prefixEnd_8258365 := by exact prefixLift 8258365
  have htrace : WordTrace (prefixWord ++ tailWord_8258365) baseStart_8258365 baseEnd_8258365 := by
    simpa [prefixWord, tailWord_8258365, baseEnd_8258365] using wordTrace_append hprefix tailTrace_8258365
  have hstable : (prefixWord ++ tailWord_8258365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258365).length < 2 ^ (prefixWord ++ tailWord_8258365).sum := by decide
  have hdescent : baseEnd_8258365 < baseStart_8258365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258391 : List Nat := [1, 1, 3, 2, 4, 3, 1, 8]
def baseStart_8258391 : Nat := 118140960795 + 8258391 * 2 ^ 59
def prefixEnd_8258391 : Nat := 4983230072969 + 3 ^ 40 * 8258391 * 2
def baseEnd_8258391 : Nat := 157056445028322360775291

theorem tailTrace_8258391 : CollatzResearch.WordTrace tailWord_8258391 prefixEnd_8258391 157056445028322360775291 := by
  unfold tailWord_8258391
  simp only [CollatzResearch.WordTrace]
  refine ⟨301208265024267302738567027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200805510016178201825711351 301208265024267302738567027)
  ·
    refine ⟨451812397536400954107850541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301208265024267302738567027 451812397536400954107850541)
    ·
      refine ⟨169429649076150357790443953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451812397536400954107850541 169429649076150357790443953)
      ·
        refine ⟨127072236807112768342832965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169429649076150357790443953 127072236807112768342832965)
        ·
          refine ⟨23826044401333644064281181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127072236807112768342832965 23826044401333644064281181)
          ·
            refine ⟨8934766650500116524105443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23826044401333644064281181 8934766650500116524105443)
            ·
              refine ⟨13402149975750174786158165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8934766650500116524105443 13402149975750174786158165)
              ·
                refine ⟨157056445028322360775291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13402149975750174786158165 157056445028322360775291)
                ·
                  rfl

theorem cell23_8258391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 8].length) (baseStart_8258391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258391 prefixEnd_8258391 := by exact prefixLift 8258391
  have htrace : WordTrace (prefixWord ++ tailWord_8258391) baseStart_8258391 baseEnd_8258391 := by
    simpa [prefixWord, tailWord_8258391, baseEnd_8258391] using wordTrace_append hprefix tailTrace_8258391
  have hstable : (prefixWord ++ tailWord_8258391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258391).length < 2 ^ (prefixWord ++ tailWord_8258391).sum := by decide
  have hdescent : baseEnd_8258391 < baseStart_8258391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258402 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_8258402 : Nat := 118140960795 + 8258402 * 2 ^ 59
def prefixEnd_8258402 : Nat := 4983230072969 + 3 ^ 40 * 8258402 * 2
def baseEnd_8258402 : Nat := 4240529664051903197895307

theorem tailTrace_8258402 : CollatzResearch.WordTrace tailWord_8258402 prefixEnd_8258402 4240529664051903197895307 := by
  unfold tailWord_8258402
  simp only [CollatzResearch.WordTrace]
  refine ⟨75302166556806862904304365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200805777484818301078144973 75302166556806862904304365)
  ·
    refine ⟨28238312458802573589114137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75302166556806862904304365 28238312458802573589114137)
    ·
      refine ⟨21178734344101930191835603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28238312458802573589114137 21178734344101930191835603)
      ·
        refine ⟨31768101516152895287753405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21178734344101930191835603 31768101516152895287753405)
        ·
          refine ⟨11913038068557335732907527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31768101516152895287753405 11913038068557335732907527)
          ·
            refine ⟨17869557102836003599361291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11913038068557335732907527 17869557102836003599361291)
            ·
              refine ⟨26804335654254005399041937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17869557102836003599361291 26804335654254005399041937)
              ·
                refine ⟨20103251740690504049281453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26804335654254005399041937 20103251740690504049281453)
                ·
                  refine ⟨7538719402758939018480545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20103251740690504049281453 7538719402758939018480545)
                  ·
                    refine ⟨5654039552069204263860409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7538719402758939018480545 5654039552069204263860409)
                    ·
                      refine ⟨4240529664051903197895307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5654039552069204263860409 4240529664051903197895307)
                      ·
                        rfl

theorem cell23_8258402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_8258402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258402 prefixEnd_8258402 := by exact prefixLift 8258402
  have htrace : WordTrace (prefixWord ++ tailWord_8258402) baseStart_8258402 baseEnd_8258402 := by
    simpa [prefixWord, tailWord_8258402, baseEnd_8258402] using wordTrace_append hprefix tailTrace_8258402
  have hstable : (prefixWord ++ tailWord_8258402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258402).length < 2 ^ (prefixWord ++ tailWord_8258402).sum := by decide
  have hdescent : baseEnd_8258402 < baseStart_8258402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258422 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_8258422 : Nat := 118140960795 + 8258422 * 2 ^ 59
def prefixEnd_8258422 : Nat := 4983230072969 + 3 ^ 40 * 8258422 * 2
def baseEnd_8258422 : Nat := 4240539933664993119645215

theorem tailTrace_8258422 : CollatzResearch.WordTrace tailWord_8258422 prefixEnd_8258422 4240539933664993119645215 := by
  unfold tailWord_8258422
  simp only [CollatzResearch.WordTrace]
  refine ⟨18825587230447187189559095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200806263791436663355297013 18825587230447187189559095)
  ·
    refine ⟨28238380845670780784338643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18825587230447187189559095 28238380845670780784338643)
    ·
      refine ⟨42357571268506171176507965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28238380845670780784338643 42357571268506171176507965)
      ·
        refine ⟨15884089225689814191190487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42357571268506171176507965 15884089225689814191190487)
        ·
          refine ⟨23826133838534721286785731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15884089225689814191190487 23826133838534721286785731)
          ·
            refine ⟨35739200757802081930178597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23826133838534721286785731 35739200757802081930178597)
            ·
              refine ⟨6701100142087890361908487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35739200757802081930178597 6701100142087890361908487)
              ·
                refine ⟨10051650213131835542862731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701100142087890361908487 10051650213131835542862731)
                ·
                  refine ⟨15077475319697753314294097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10051650213131835542862731 15077475319697753314294097)
                  ·
                    refine ⟨11308106489773314985720573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15077475319697753314294097 11308106489773314985720573)
                    ·
                      refine ⟨4240539933664993119645215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11308106489773314985720573 4240539933664993119645215)
                      ·
                        rfl

theorem cell23_8258422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_8258422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258422 prefixEnd_8258422 := by exact prefixLift 8258422
  have htrace : WordTrace (prefixWord ++ tailWord_8258422) baseStart_8258422 baseEnd_8258422 := by
    simpa [prefixWord, tailWord_8258422, baseEnd_8258422] using wordTrace_append hprefix tailTrace_8258422
  have hstable : (prefixWord ++ tailWord_8258422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258422).length < 2 ^ (prefixWord ++ tailWord_8258422).sum := by decide
  have hdescent : baseEnd_8258422 < baseStart_8258422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258424 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_8258424 : Nat := 118140960795 + 8258424 * 2 ^ 59
def prefixEnd_8258424 : Nat := 4983230072969 + 3 ^ 40 * 8258424 * 2
def baseEnd_8258424 : Nat := 4240540960626302111820205

theorem tailTrace_8258424 : CollatzResearch.WordTrace tailWord_8258424 prefixEnd_8258424 4240540960626302111820205 := by
  unfold tailWord_8258424
  simp only [CollatzResearch.WordTrace]
  refine ⟨150604734316573874687259163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200806312422098499583012217 150604734316573874687259163)
  ·
    refine ⟨225907101474860812030888745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150604734316573874687259163 225907101474860812030888745)
    ·
      refine ⟨169430326106145609023166559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225907101474860812030888745 169430326106145609023166559)
      ·
        refine ⟨254145489159218413534749839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169430326106145609023166559 254145489159218413534749839)
        ·
          refine ⟨381218233738827620302124759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254145489159218413534749839 381218233738827620302124759)
          ·
            refine ⟨571827350608241430453187139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381218233738827620302124759 571827350608241430453187139)
            ·
              refine ⟨857741025912362145679780709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571827350608241430453187139 857741025912362145679780709)
              ·
                refine ⟨160826442358567902314958883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 857741025912362145679780709 160826442358567902314958883)
                ·
                  refine ⟨241239663537851853472438325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160826442358567902314958883 241239663537851853472438325)
                  ·
                    refine ⟨22616218456673611263041093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 241239663537851853472438325 22616218456673611263041093)
                    ·
                      refine ⟨4240540960626302111820205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22616218456673611263041093 4240540960626302111820205)
                      ·
                        rfl

theorem cell23_8258424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_8258424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258424 prefixEnd_8258424 := by exact prefixLift 8258424
  have htrace : WordTrace (prefixWord ++ tailWord_8258424) baseStart_8258424 baseEnd_8258424 := by
    simpa [prefixWord, tailWord_8258424, baseEnd_8258424] using wordTrace_append hprefix tailTrace_8258424
  have hstable : (prefixWord ++ tailWord_8258424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258424).length < 2 ^ (prefixWord ++ tailWord_8258424).sum := by decide
  have hdescent : baseEnd_8258424 < baseStart_8258424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258452 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_8258452 : Nat := 118140960795 + 8258452 * 2 ^ 59
def prefixEnd_8258452 : Nat := 4983230072969 + 3 ^ 40 * 8258452 * 2
def baseEnd_8258452 : Nat := 4240555338084628002270077

theorem tailTrace_8258452 : CollatzResearch.WordTrace tailWord_8258452 prefixEnd_8258452 4240555338084628002270077 := by
  unfold tailWord_8258452
  simp only [CollatzResearch.WordTrace]
  refine ⟨150605244938523155078268805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200806993251364206771025073 150605244938523155078268805)
  ·
    refine ⟨28238483425973091577175401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150605244938523155078268805 28238483425973091577175401)
    ·
      refine ⟨21178862569479818682881551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28238483425973091577175401 21178862569479818682881551)
      ·
        refine ⟨31768293854219728024322327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21178862569479818682881551 31768293854219728024322327)
        ·
          refine ⟨47652440781329592036483491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31768293854219728024322327 47652440781329592036483491)
          ·
            refine ⟨71478661171994388054725237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47652440781329592036483491 71478661171994388054725237)
            ·
              refine ⟨6701124484874473880130491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71478661171994388054725237 6701124484874473880130491)
              ·
                refine ⟨10051686727311710820195737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701124484874473880130491 10051686727311710820195737)
                ·
                  refine ⟨7538765045483783115146803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10051686727311710820195737 7538765045483783115146803)
                  ·
                    refine ⟨11308147568225674672720205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7538765045483783115146803 11308147568225674672720205)
                    ·
                      refine ⟨4240555338084628002270077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11308147568225674672720205 4240555338084628002270077)
                      ·
                        rfl

theorem cell23_8258452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_8258452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258452 prefixEnd_8258452 := by exact prefixLift 8258452
  have htrace : WordTrace (prefixWord ++ tailWord_8258452) baseStart_8258452 baseEnd_8258452 := by
    simpa [prefixWord, tailWord_8258452, baseEnd_8258452] using wordTrace_append hprefix tailTrace_8258452
  have hstable : (prefixWord ++ tailWord_8258452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258452).length < 2 ^ (prefixWord ++ tailWord_8258452).sum := by decide
  have hdescent : baseEnd_8258452 < baseStart_8258452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258461 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_8258461 : Nat := 118140960795 + 8258461 * 2 ^ 59
def prefixEnd_8258461 : Nat := 4983230072969 + 3 ^ 40 * 8258461 * 2
def baseEnd_8258461 : Nat := 4240559959410518467057535

theorem tailTrace_8258461 : CollatzResearch.WordTrace tailWord_8258461 prefixEnd_8258461 4240559959410518467057535 := by
  unfold tailWord_8258461
  simp only [CollatzResearch.WordTrace]
  refine ⟨301210818134013704693615237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200807212089342469795743491 301210818134013704693615237)
  ·
    refine ⟨56477028400127569630052857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301210818134013704693615237 56477028400127569630052857)
    ·
      refine ⟨42357771300095677222539643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56477028400127569630052857 42357771300095677222539643)
      ·
        refine ⟨63536656950143515833809465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42357771300095677222539643 63536656950143515833809465)
        ·
          refine ⟨47652492712607636875357099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63536656950143515833809465 47652492712607636875357099)
          ·
            refine ⟨71478739068911455313035649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47652492712607636875357099 71478739068911455313035649)
            ·
              refine ⟨53609054301683591484776737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71478739068911455313035649 53609054301683591484776737)
              ·
                refine ⟨40206790726262693613582553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53609054301683591484776737 40206790726262693613582553)
                ·
                  refine ⟨30155093044697020210186915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40206790726262693613582553 30155093044697020210186915)
                  ·
                    refine ⟨45232639567045530315280373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30155093044697020210186915 45232639567045530315280373)
                    ·
                      refine ⟨4240559959410518467057535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45232639567045530315280373 4240559959410518467057535)
                      ·
                        rfl

theorem cell23_8258461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_8258461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258461 prefixEnd_8258461 := by exact prefixLift 8258461
  have htrace : WordTrace (prefixWord ++ tailWord_8258461) baseStart_8258461 baseEnd_8258461 := by
    simpa [prefixWord, tailWord_8258461, baseEnd_8258461] using wordTrace_append hprefix tailTrace_8258461
  have hstable : (prefixWord ++ tailWord_8258461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258461).length < 2 ^ (prefixWord ++ tailWord_8258461).sum := by decide
  have hdescent : baseEnd_8258461 < baseStart_8258461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258622 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_8258622 : Nat := 118140960795 + 8258622 * 2 ^ 59
def prefixEnd_8258622 : Nat := 4983230072969 + 3 ^ 40 * 8258622 * 2
def baseEnd_8258622 : Nat := 471182514421765815238255

theorem tailTrace_8258622 : CollatzResearch.WordTrace tailWord_8258622 prefixEnd_8258622 471182514421765815238255 := by
  unfold tailWord_8258622
  simp only [CollatzResearch.WordTrace]
  refine ⟨37652086285803803648778265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200811126857620286126817413 37652086285803803648778265)
  ·
    refine ⟨28239064714352852736583699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37652086285803803648778265 28239064714352852736583699)
    ·
      refine ⟨42358597071529279104875549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28239064714352852736583699 42358597071529279104875549)
      ·
        refine ⟨15884473901823479664328331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42358597071529279104875549 15884473901823479664328331)
        ·
          refine ⟨23826710852735219496492497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15884473901823479664328331 23826710852735219496492497)
          ·
            refine ⟨17870033139551414622369373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23826710852735219496492497 17870033139551414622369373)
            ·
              refine ⟨6701262427331780483388515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17870033139551414622369373 6701262427331780483388515)
              ·
                refine ⟨10051893640997670725082773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701262427331780483388515 10051893640997670725082773)
                ·
                  refine ⟨471182514421765815238255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10051893640997670725082773 471182514421765815238255)
                  ·
                    rfl

theorem cell23_8258622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_8258622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258622 prefixEnd_8258622 := by exact prefixLift 8258622
  have htrace : WordTrace (prefixWord ++ tailWord_8258622) baseStart_8258622 baseEnd_8258622 := by
    simpa [prefixWord, tailWord_8258622, baseEnd_8258622] using wordTrace_append hprefix tailTrace_8258622
  have hstable : (prefixWord ++ tailWord_8258622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258622).length < 2 ^ (prefixWord ++ tailWord_8258622).sum := by decide
  have hdescent : baseEnd_8258622 < baseStart_8258622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258648 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 6, 4]
def baseStart_8258648 : Nat := 118140960795 + 8258648 * 2 ^ 59
def prefixEnd_8258648 : Nat := 4983230072969 + 3 ^ 40 * 8258648 * 2
def baseEnd_8258648 : Nat := 1413551993430969745139725

theorem tailTrace_8258648 : CollatzResearch.WordTrace tailWord_8258648 prefixEnd_8258648 1413551993430969745139725 := by
  unfold tailWord_8258648
  simp only [CollatzResearch.WordTrace]
  refine ⟨150608819292168117815336299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200811759056224157087115065 150608819292168117815336299)
  ·
    refine ⟨225913228938252176723004449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150608819292168117815336299 225913228938252176723004449)
    ·
      refine ⟨169434921703689132542253337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225913228938252176723004449 169434921703689132542253337)
      ·
        refine ⟨127076191277766849406690003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169434921703689132542253337 127076191277766849406690003)
        ·
          refine ⟨190614286916650274110035005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127076191277766849406690003 190614286916650274110035005)
          ·
            refine ⟨71480357593743852791263127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190614286916650274110035005 71480357593743852791263127)
            ·
              refine ⟨107220536390615779186894691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71480357593743852791263127 107220536390615779186894691)
              ·
                refine ⟨160830804585923668780342037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107220536390615779186894691 160830804585923668780342037)
                ·
                  refine ⟨7538943964965171974078533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160830804585923668780342037 7538943964965171974078533)
                  ·
                    refine ⟨1413551993430969745139725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7538943964965171974078533 1413551993430969745139725)
                    ·
                      rfl

theorem cell23_8258648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_8258648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258648 prefixEnd_8258648 := by exact prefixLift 8258648
  have htrace : WordTrace (prefixWord ++ tailWord_8258648) baseStart_8258648 baseEnd_8258648 := by
    simpa [prefixWord, tailWord_8258648, baseEnd_8258648] using wordTrace_append hprefix tailTrace_8258648
  have hstable : (prefixWord ++ tailWord_8258648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258648).length < 2 ^ (prefixWord ++ tailWord_8258648).sum := by decide
  have hdescent : baseEnd_8258648 < baseStart_8258648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258666 : List Nat := [3, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_8258666 : Nat := 118140960795 + 8258666 * 2 ^ 59
def prefixEnd_8258666 : Nat := 4983230072969 + 3 ^ 40 * 8258666 * 2
def baseEnd_8258666 : Nat := 4240665222944690164994093

theorem tailTrace_8258666 : CollatzResearch.WordTrace tailWord_8258666 prefixEnd_8258666 4240665222944690164994093 := by
  unfold tailWord_8258666
  simp only [CollatzResearch.WordTrace]
  refine ⟨75304573774567756176206963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200812196732180683136551901 75304573774567756176206963)
  ·
    refine ⟨112956860661851634264310445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75304573774567756176206963 112956860661851634264310445)
    ·
      refine ⟨42358822748194362849116417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112956860661851634264310445 42358822748194362849116417)
      ·
        refine ⟨31769117061145772136837313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42358822748194362849116417 31769117061145772136837313)
        ·
          refine ⟨23826837795859329102627985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31769117061145772136837313 23826837795859329102627985)
          ·
            refine ⟨17870128346894496826970989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23826837795859329102627985 17870128346894496826970989)
            ·
              refine ⟨6701298130085436310114121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17870128346894496826970989 6701298130085436310114121)
              ·
                refine ⟨5025973597564077232585591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6701298130085436310114121 5025973597564077232585591)
                ·
                  refine ⟨7538960396346115848878387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5025973597564077232585591 7538960396346115848878387)
                  ·
                    refine ⟨11308440594519173773317581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7538960396346115848878387 11308440594519173773317581)
                    ·
                      refine ⟨4240665222944690164994093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11308440594519173773317581 4240665222944690164994093)
                      ·
                        rfl

theorem cell23_8258666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_8258666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258666 prefixEnd_8258666 := by exact prefixLift 8258666
  have htrace : WordTrace (prefixWord ++ tailWord_8258666) baseStart_8258666 baseEnd_8258666 := by
    simpa [prefixWord, tailWord_8258666, baseEnd_8258666] using wordTrace_append hprefix tailTrace_8258666
  have hstable : (prefixWord ++ tailWord_8258666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258666).length < 2 ^ (prefixWord ++ tailWord_8258666).sum := by decide
  have hdescent : baseEnd_8258666 < baseStart_8258666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258692 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_8258692 : Nat := 118140960795 + 8258692 * 2 ^ 59
def prefixEnd_8258692 : Nat := 4983230072969 + 3 ^ 40 * 8258692 * 2
def baseEnd_8258692 : Nat := 4240678573441707063268973

theorem tailTrace_8258692 : CollatzResearch.WordTrace tailWord_8258692 prefixEnd_8258692 4240678573441707063268973 := by
  unfold tailWord_8258692
  simp only [CollatzResearch.WordTrace]
  refine ⟨150609621698088415572637165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200812828930784554096849553 150609621698088415572637165)
  ·
    refine ⟨56478608136783155839738937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150609621698088415572637165 56478608136783155839738937)
    ·
      refine ⟨42358956102587366879804203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56478608136783155839738937 42358956102587366879804203)
      ·
        refine ⟨63538434153881050319706305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42358956102587366879804203 63538434153881050319706305)
        ·
          refine ⟨47653825615410787739779729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63538434153881050319706305 47653825615410787739779729)
          ·
            refine ⟨35740369211558090804834797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47653825615410787739779729 35740369211558090804834797)
            ·
              refine ⟨13402638454334284051813049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35740369211558090804834797 13402638454334284051813049)
              ·
                refine ⟨10051978840750713038859787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13402638454334284051813049 10051978840750713038859787)
                ·
                  refine ⟨15077968261126069558289681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10051978840750713038859787 15077968261126069558289681)
                  ·
                    refine ⟨11308476195844552168717261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15077968261126069558289681 11308476195844552168717261)
                    ·
                      refine ⟨4240678573441707063268973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11308476195844552168717261 4240678573441707063268973)
                      ·
                        rfl

theorem cell23_8258692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_8258692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258692 prefixEnd_8258692 := by exact prefixLift 8258692
  have htrace : WordTrace (prefixWord ++ tailWord_8258692) baseStart_8258692 baseEnd_8258692 := by
    simpa [prefixWord, tailWord_8258692, baseEnd_8258692] using wordTrace_append hprefix tailTrace_8258692
  have hstable : (prefixWord ++ tailWord_8258692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258692).length < 2 ^ (prefixWord ++ tailWord_8258692).sum := by decide
  have hdescent : baseEnd_8258692 < baseStart_8258692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258738 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_8258738 : Nat := 118140960795 + 8258738 * 2 ^ 59
def prefixEnd_8258738 : Nat := 4983230072969 + 3 ^ 40 * 8258738 * 2
def baseEnd_8258738 : Nat := 1413567397850604627764587

theorem tailTrace_8258738 : CollatzResearch.WordTrace tailWord_8258738 prefixEnd_8258738 1413567397850604627764587 := by
  unfold tailWord_8258738
  simp only [CollatzResearch.WordTrace]
  refine ⟨75305230288502545250362217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200813947436006787334299245 75305230288502545250362217)
  ·
    refine ⟨56478922716376908937771663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75305230288502545250362217 56478922716376908937771663)
    ·
      refine ⟨84718384074565363406657495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56478922716376908937771663 84718384074565363406657495)
      ·
        refine ⟨127077576111848045109986243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84718384074565363406657495 127077576111848045109986243)
        ·
          refine ⟨190616364167772067664979365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127077576111848045109986243 190616364167772067664979365)
          ·
            refine ⟨35740568281457262687183631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190616364167772067664979365 35740568281457262687183631)
            ·
              refine ⟨53610852422185894030775447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35740568281457262687183631 53610852422185894030775447)
              ·
                refine ⟨80416278633278841046163171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53610852422185894030775447 80416278633278841046163171)
                ·
                  refine ⟨120624417949918261569244757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80416278633278841046163171 120624417949918261569244757)
                  ·
                    refine ⟨1413567397850604627764587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120624417949918261569244757 1413567397850604627764587)
                    ·
                      rfl

theorem cell23_8258738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_8258738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258738 prefixEnd_8258738 := by exact prefixLift 8258738
  have htrace : WordTrace (prefixWord ++ tailWord_8258738) baseStart_8258738 baseEnd_8258738 := by
    simpa [prefixWord, tailWord_8258738, baseEnd_8258738] using wordTrace_append hprefix tailTrace_8258738
  have hstable : (prefixWord ++ tailWord_8258738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258738).length < 2 ^ (prefixWord ++ tailWord_8258738).sum := by decide
  have hdescent : baseEnd_8258738 < baseStart_8258738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258762 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2]
def baseStart_8258762 : Nat := 118140960795 + 8258762 * 2 ^ 59
def prefixEnd_8258762 : Nat := 4983230072969 + 3 ^ 40 * 8258762 * 2
def baseEnd_8258762 : Nat := 4240714517087521789393651

theorem tailTrace_8258762 : CollatzResearch.WordTrace tailWord_8258762 prefixEnd_8258762 4240714517087521789393651 := by
  unfold tailWord_8258762
  simp only [CollatzResearch.WordTrace]
  refine ⟨75305449126480808275080635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200814531003948822066881693 75305449126480808275080635)
  ·
    refine ⟨112958173689721212412620953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75305449126480808275080635 112958173689721212412620953)
    ·
      refine ⟨84718630267290909309465715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112958173689721212412620953 84718630267290909309465715)
      ·
        refine ⟨127077945400936363964198573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84718630267290909309465715 127077945400936363964198573)
        ·
          refine ⟨47654229525351136486574465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127077945400936363964198573 47654229525351136486574465)
          ·
            refine ⟨35740672144013352364930849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47654229525351136486574465 35740672144013352364930849)
            ·
              refine ⟨26805504108010014273698137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35740672144013352364930849 26805504108010014273698137)
              ·
                refine ⟨20104128081007510705273603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26805504108010014273698137 20104128081007510705273603)
                ·
                  refine ⟨30156192121511266057910405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20104128081007510705273603 30156192121511266057910405)
                  ·
                    refine ⟨5654286022783362385858201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30156192121511266057910405 5654286022783362385858201)
                    ·
                      refine ⟨4240714517087521789393651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5654286022783362385858201 4240714517087521789393651)
                      ·
                        rfl

theorem cell23_8258762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_8258762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258762 prefixEnd_8258762 := by exact prefixLift 8258762
  have htrace : WordTrace (prefixWord ++ tailWord_8258762) baseStart_8258762 baseEnd_8258762 := by
    simpa [prefixWord, tailWord_8258762, baseEnd_8258762] using wordTrace_append hprefix tailTrace_8258762
  have hstable : (prefixWord ++ tailWord_8258762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258762).length < 2 ^ (prefixWord ++ tailWord_8258762).sum := by decide
  have hdescent : baseEnd_8258762 < baseStart_8258762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258785 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 7]
def baseStart_8258785 : Nat := 118140960795 + 8258785 * 2 ^ 59
def prefixEnd_8258785 : Nat := 4983230072969 + 3 ^ 40 * 8258785 * 2
def baseEnd_8258785 : Nat := 471191814126952799934005

theorem tailTrace_8258785 : CollatzResearch.WordTrace tailWord_8258785 prefixEnd_8258785 471191814126952799934005 := by
  unfold tailWord_8258785
  simp only [CollatzResearch.WordTrace]
  refine ⟨301222635384839908028409809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200815090256559938685606539 301222635384839908028409809)
  ·
    refine ⟨225916976538629931021307357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301222635384839908028409809 225916976538629931021307357)
    ·
      refine ⟨84718866201986224132990259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225916976538629931021307357 84718866201986224132990259)
      ·
        refine ⟨127078299302979336199485389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84718866201986224132990259 127078299302979336199485389)
        ·
          refine ⟨47654362238617251074807021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127078299302979336199485389 47654362238617251074807021)
          ·
            refine ⟨17870385839481469153052633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47654362238617251074807021 17870385839481469153052633)
            ·
              refine ⟨13402789379611101864789475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17870385839481469153052633 13402789379611101864789475)
              ·
                refine ⟨20104184069416652797184213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13402789379611101864789475 20104184069416652797184213)
                ·
                  refine ⟨471191814126952799934005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20104184069416652797184213 471191814126952799934005)
                  ·
                    rfl

theorem cell23_8258785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 7].length) (baseStart_8258785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258785 prefixEnd_8258785 := by exact prefixLift 8258785
  have htrace : WordTrace (prefixWord ++ tailWord_8258785) baseStart_8258785 baseEnd_8258785 := by
    simpa [prefixWord, tailWord_8258785, baseEnd_8258785] using wordTrace_append hprefix tailTrace_8258785
  have hstable : (prefixWord ++ tailWord_8258785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258785).length < 2 ^ (prefixWord ++ tailWord_8258785).sum := by decide
  have hdescent : baseEnd_8258785 < baseStart_8258785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258795 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 3]
def baseStart_8258795 : Nat := 118140960795 + 8258795 * 2 ^ 59
def prefixEnd_8258795 : Nat := 4983230072969 + 3 ^ 40 * 8258795 * 2
def baseEnd_8258795 : Nat := 4240731461949120160280999

theorem tailTrace_8258795 : CollatzResearch.WordTrace tailWord_8258795 prefixEnd_8258795 4240731461949120160280999 := by
  unfold tailWord_8258795
  simp only [CollatzResearch.WordTrace]
  refine ⟨301223000114803679736273839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200815333409869119824182559 301223000114803679736273839)
  ·
    refine ⟨451834500172205519604410759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301223000114803679736273839 451834500172205519604410759)
    ·
      refine ⟨677751750258308279406616139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451834500172205519604410759 677751750258308279406616139)
      ·
        refine ⟨1016627625387462419109924209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677751750258308279406616139 1016627625387462419109924209)
        ·
          refine ⟨762470719040596814332443157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1016627625387462419109924209 762470719040596814332443157)
          ·
            refine ⟨35740814955027975671833273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 762470719040596814332443157 35740814955027975671833273)
            ·
              refine ⟨26805611216270981753874955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35740814955027975671833273 26805611216270981753874955)
              ·
                refine ⟨40208416824406472630812433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26805611216270981753874955 40208416824406472630812433)
                ·
                  refine ⟨30156312618304854473109325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40208416824406472630812433 30156312618304854473109325)
                  ·
                    refine ⟨11308617231864320427415997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30156312618304854473109325 11308617231864320427415997)
                    ·
                      refine ⟨4240731461949120160280999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11308617231864320427415997 4240731461949120160280999)
                      ·
                        rfl

theorem cell23_8258795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 3].length) (baseStart_8258795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258795 prefixEnd_8258795 := by exact prefixLift 8258795
  have htrace : WordTrace (prefixWord ++ tailWord_8258795) baseStart_8258795 baseEnd_8258795 := by
    simpa [prefixWord, tailWord_8258795, baseEnd_8258795] using wordTrace_append hprefix tailTrace_8258795
  have hstable : (prefixWord ++ tailWord_8258795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258795).length < 2 ^ (prefixWord ++ tailWord_8258795).sum := by decide
  have hdescent : baseEnd_8258795 < baseStart_8258795 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258796 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 2, 2, 2]
def baseStart_8258796 : Nat := 118140960795 + 8258796 * 2 ^ 59
def prefixEnd_8258796 : Nat := 4983230072969 + 3 ^ 40 * 8258796 * 2
def baseEnd_8258796 : Nat := 4240731975429774656368495

theorem tailTrace_8258796 : CollatzResearch.WordTrace tailWord_8258796 prefixEnd_8258796 4240731975429774656368495 := by
  unfold tailWord_8258796
  simp only [CollatzResearch.WordTrace]
  refine ⟨150611518293900028453530121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200815357725200037938040161 150611518293900028453530121)
  ·
    refine ⟨112958638720425021340147591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150611518293900028453530121 112958638720425021340147591)
    ·
      refine ⟨169437958080637532010221387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112958638720425021340147591 169437958080637532010221387)
      ·
        refine ⟨254156937120956298015332081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169437958080637532010221387 254156937120956298015332081)
        ·
          refine ⟨190617702840717223511499061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254156937120956298015332081 190617702840717223511499061)
          ·
            refine ⟨17870409641317239704203037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190617702840717223511499061 17870409641317239704203037)
            ·
              refine ⟨6701403615493964889076139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17870409641317239704203037 6701403615493964889076139)
              ·
                refine ⟨10052105423240947333614209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701403615493964889076139 10052105423240947333614209)
                ·
                  refine ⟨7539079067430710500210657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10052105423240947333614209 7539079067430710500210657)
                  ·
                    refine ⟨5654309300573032875157993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7539079067430710500210657 5654309300573032875157993)
                    ·
                      refine ⟨4240731975429774656368495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5654309300573032875157993 4240731975429774656368495)
                      ·
                        rfl

theorem cell23_8258796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 2, 2].length) (baseStart_8258796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258796 prefixEnd_8258796 := by exact prefixLift 8258796
  have htrace : WordTrace (prefixWord ++ tailWord_8258796) baseStart_8258796 baseEnd_8258796 := by
    simpa [prefixWord, tailWord_8258796, baseEnd_8258796] using wordTrace_append hprefix tailTrace_8258796
  have hstable : (prefixWord ++ tailWord_8258796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258796).length < 2 ^ (prefixWord ++ tailWord_8258796).sum := by decide
  have hdescent : baseEnd_8258796 < baseStart_8258796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258808 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_8258808 : Nat := 118140960795 + 8258808 * 2 ^ 59
def prefixEnd_8258808 : Nat := 4983230072969 + 3 ^ 40 * 8258808 * 2
def baseEnd_8258808 : Nat := 4240738137197628609418439

theorem tailTrace_8258808 : CollatzResearch.WordTrace tailWord_8258808 prefixEnd_8258808 4240738137197628609418439 := by
  unfold tailWord_8258808
  simp only [CollatzResearch.WordTrace]
  refine ⟨150611737131878291478248539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200815649509171055304331385 150611737131878291478248539)
  ·
    refine ⟨225917605697817437217372809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150611737131878291478248539 225917605697817437217372809)
    ·
      refine ⟨169438204273363077913029607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225917605697817437217372809 169438204273363077913029607)
      ·
        refine ⟨254157306410044616869544411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169438204273363077913029607 254157306410044616869544411)
        ·
          refine ⟨381235959615066925304316617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254157306410044616869544411 381235959615066925304316617)
          ·
            refine ⟨285926969711300193978237463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381235959615066925304316617 285926969711300193978237463)
            ·
              refine ⟨428890454566950290967356195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285926969711300193978237463 428890454566950290967356195)
              ·
                refine ⟨643335681850425436451034293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428890454566950290967356195 643335681850425436451034293)
                ·
                  refine ⟨60312720173477384667284465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 643335681850425436451034293 60312720173477384667284465)
                  ·
                    refine ⟨45234540130108038500463349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60312720173477384667284465 45234540130108038500463349)
                    ·
                      refine ⟨4240738137197628609418439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45234540130108038500463349 4240738137197628609418439)
                      ·
                        rfl

theorem cell23_8258808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_8258808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258808 prefixEnd_8258808 := by exact prefixLift 8258808
  have htrace : WordTrace (prefixWord ++ tailWord_8258808) baseStart_8258808 baseEnd_8258808 := by
    simpa [prefixWord, tailWord_8258808, baseEnd_8258808] using wordTrace_append hprefix tailTrace_8258808
  have hstable : (prefixWord ++ tailWord_8258808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258808).length < 2 ^ (prefixWord ++ tailWord_8258808).sum := by decide
  have hdescent : baseEnd_8258808 < baseStart_8258808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258852 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 1, 6, 2]
def baseStart_8258852 : Nat := 118140960795 + 8258852 * 2 ^ 59
def prefixEnd_8258852 : Nat := 4983230072969 + 3 ^ 40 * 8258852 * 2
def baseEnd_8258852 : Nat := 4240760730346426437268237

theorem tailTrace_8258852 : CollatzResearch.WordTrace tailWord_8258852 prefixEnd_8258852 4240760730346426437268237 := by
  unfold tailWord_8258852
  simp only [CollatzResearch.WordTrace]
  refine ⟨150612539537798589235549405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200816719383731452314065873 150612539537798589235549405)
  ·
    refine ⟨56479702326674470963331027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150612539537798589235549405 56479702326674470963331027)
    ·
      refine ⟨84719553490011706444996541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56479702326674470963331027 84719553490011706444996541)
      ·
        refine ⟨31769832558754389916873703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84719553490011706444996541 31769832558754389916873703)
        ·
          refine ⟨47654748838131584875310555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31769832558754389916873703 47654748838131584875310555)
          ·
            refine ⟨71482123257197377312965833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47654748838131584875310555 71482123257197377312965833)
            ·
              refine ⟨53611592442898032984724375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71482123257197377312965833 53611592442898032984724375)
              ·
                refine ⟨80417388664347049477086563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53611592442898032984724375 80417388664347049477086563)
                ·
                  refine ⟨120626082996520574215629845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80417388664347049477086563 120626082996520574215629845)
                  ·
                    refine ⟨5654347640461901916357649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120626082996520574215629845 5654347640461901916357649)
                    ·
                      refine ⟨4240760730346426437268237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5654347640461901916357649 4240760730346426437268237)
                      ·
                        rfl

theorem cell23_8258852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_8258852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258852 prefixEnd_8258852 := by exact prefixLift 8258852
  have htrace : WordTrace (prefixWord ++ tailWord_8258852) baseStart_8258852 baseEnd_8258852 := by
    simpa [prefixWord, tailWord_8258852, baseEnd_8258852] using wordTrace_append hprefix tailTrace_8258852
  have hstable : (prefixWord ++ tailWord_8258852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258852).length < 2 ^ (prefixWord ++ tailWord_8258852).sum := by decide
  have hdescent : baseEnd_8258852 < baseStart_8258852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258892 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 6]
def baseStart_8258892 : Nat := 118140960795 + 8258892 * 2 ^ 59
def prefixEnd_8258892 : Nat := 4983230072969 + 3 ^ 40 * 8258892 * 2
def baseEnd_8258892 : Nat := 471197918841400697863117

theorem tailTrace_8258892 : CollatzResearch.WordTrace tailWord_8258892 prefixEnd_8258892 471197918841400697863117 := by
  unfold tailWord_8258892
  simp only [CollatzResearch.WordTrace]
  refine ⟨150613268997726132651277465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200817691996968176868369953 150613268997726132651277465)
  ·
    refine ⟨112959951748294599488458099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150613268997726132651277465 112959951748294599488458099)
    ·
      refine ⟨169439927622441899232687149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112959951748294599488458099 169439927622441899232687149)
      ·
        refine ⟨63539972858415712212257681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169439927622441899232687149 63539972858415712212257681)
        ·
          refine ⟨47654979643811784159193261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63539972858415712212257681 47654979643811784159193261)
          ·
            refine ⟨17870617366429419059697473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47654979643811784159193261 17870617366429419059697473)
            ·
              refine ⟨13402963024822064294773105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17870617366429419059697473 13402963024822064294773105)
              ·
                refine ⟨10052222268616548221079829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13402963024822064294773105 10052222268616548221079829)
                ·
                  refine ⟨471197918841400697863117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10052222268616548221079829 471197918841400697863117)
                  ·
                    rfl

theorem cell23_8258892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_8258892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258892 prefixEnd_8258892 := by exact prefixLift 8258892
  have htrace : WordTrace (prefixWord ++ tailWord_8258892) baseStart_8258892 baseEnd_8258892 := by
    simpa [prefixWord, tailWord_8258892, baseEnd_8258892] using wordTrace_append hprefix tailTrace_8258892
  have hstable : (prefixWord ++ tailWord_8258892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258892).length < 2 ^ (prefixWord ++ tailWord_8258892).sum := by decide
  have hdescent : baseEnd_8258892 < baseStart_8258892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258905 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 3, 5]
def baseStart_8258905 : Nat := 118140960795 + 8258905 * 2 ^ 59
def prefixEnd_8258905 : Nat := 4983230072969 + 3 ^ 40 * 8258905 * 2
def baseEnd_8258905 : Nat := 1413595981607038243301831

theorem tailTrace_8258905 : CollatzResearch.WordTrace tailWord_8258905 prefixEnd_8258905 1413595981607038243301831 := by
  unfold tailWord_8258905
  simp only [CollatzResearch.WordTrace]
  refine ⟨301227012144405168522778169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200818008096270112348518779 301227012144405168522778169)
  ·
    refine ⟨225920259108303876392083627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301227012144405168522778169 225920259108303876392083627)
    ·
      refine ⟨338880388662455814588125441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225920259108303876392083627 338880388662455814588125441)
      ·
        refine ⟨254160291496841860941094081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338880388662455814588125441 254160291496841860941094081)
        ·
          refine ⟨190620218622631395705820561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254160291496841860941094081 190620218622631395705820561)
          ·
            refine ⟨142965163966973546779365421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190620218622631395705820561 142965163966973546779365421)
            ·
              refine ⟨53611936487615080042262033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142965163966973546779365421 53611936487615080042262033)
              ·
                refine ⟨40208952365711310031696525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53611936487615080042262033 40208952365711310031696525)
                ·
                  refine ⟨15078357137141741261886197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40208952365711310031696525 15078357137141741261886197)
                  ·
                    refine ⟨1413595981607038243301831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15078357137141741261886197 1413595981607038243301831)
                    ·
                      rfl

theorem cell23_8258905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_8258905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258905 prefixEnd_8258905 := by exact prefixLift 8258905
  have htrace : WordTrace (prefixWord ++ tailWord_8258905) baseStart_8258905 baseEnd_8258905 := by
    simpa [prefixWord, tailWord_8258905, baseEnd_8258905] using wordTrace_append hprefix tailTrace_8258905
  have hstable : (prefixWord ++ tailWord_8258905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258905).length < 2 ^ (prefixWord ++ tailWord_8258905).sum := by decide
  have hdescent : baseEnd_8258905 < baseStart_8258905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258929 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 2, 3, 2]
def baseStart_8258929 : Nat := 118140960795 + 8258929 * 2 ^ 59
def prefixEnd_8258929 : Nat := 4983230072969 + 3 ^ 40 * 8258929 * 2
def baseEnd_8258929 : Nat := 4240800268356822636005383

theorem tailTrace_8258929 : CollatzResearch.WordTrace tailWord_8258929 prefixEnd_8258929 4240800268356822636005383 := by
  unfold tailWord_8258929
  simp only [CollatzResearch.WordTrace]
  refine ⟨301227887496318220621651841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200818591664212147081101227 301227887496318220621651841)
  ·
    refine ⟨225920915622238665466238881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301227887496318220621651841 225920915622238665466238881)
    ·
      refine ⟨169440686716678999099679161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225920915622238665466238881 169440686716678999099679161)
      ·
        refine ⟨127080515037509249324759371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169440686716678999099679161 127080515037509249324759371)
        ·
          refine ⟨190620772556263873987139057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127080515037509249324759371 190620772556263873987139057)
          ·
            refine ⟨142965579417197905490354293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190620772556263873987139057 142965579417197905490354293)
            ·
              refine ⟨13403023070362303639720715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142965579417197905490354293 13403023070362303639720715)
              ·
                refine ⟨20104534605543455459581073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13403023070362303639720715 20104534605543455459581073)
                ·
                  refine ⟨15078400954157591594685805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20104534605543455459581073 15078400954157591594685805)
                  ·
                    refine ⟨5654400357809096848007177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15078400954157591594685805 5654400357809096848007177)
                    ·
                      refine ⟨4240800268356822636005383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5654400357809096848007177 4240800268356822636005383)
                      ·
                        rfl

theorem cell23_8258929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_8258929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258929 prefixEnd_8258929 := by exact prefixLift 8258929
  have htrace : WordTrace (prefixWord ++ tailWord_8258929) baseStart_8258929 baseEnd_8258929 := by
    simpa [prefixWord, tailWord_8258929, baseEnd_8258929] using wordTrace_append hprefix tailTrace_8258929
  have hstable : (prefixWord ++ tailWord_8258929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258929).length < 2 ^ (prefixWord ++ tailWord_8258929).sum := by decide
  have hdescent : baseEnd_8258929 < baseStart_8258929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258935 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 1, 6]
def baseStart_8258935 : Nat := 118140960795 + 8258935 * 2 ^ 59
def prefixEnd_8258935 : Nat := 4983230072969 + 3 ^ 40 * 8258935 * 2
def baseEnd_8258935 : Nat := 1413601116413583204176785

theorem tailTrace_8258935 : CollatzResearch.WordTrace tailWord_8258935 prefixEnd_8258935 1413601116413583204176785 := by
  unfold tailWord_8258935
  simp only [CollatzResearch.WordTrace]
  refine ⟨301228106334296483646370259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200818737556197655764246839 301228106334296483646370259)
  ·
    refine ⟨451842159501444725469555389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301228106334296483646370259 451842159501444725469555389)
    ·
      refine ⟨169440809813041772051083271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451842159501444725469555389 169440809813041772051083271)
      ·
        refine ⟨254161214719562658076624907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169440809813041772051083271 254161214719562658076624907)
        ·
          refine ⟨381241822079343987114937361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254161214719562658076624907 381241822079343987114937361)
          ·
            refine ⟨285931366559507990336203021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381241822079343987114937361 285931366559507990336203021)
            ·
              refine ⟨107224262459815496376076133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285931366559507990336203021 107224262459815496376076133)
              ·
                refine ⟨20104549211215405570514275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107224262459815496376076133 20104549211215405570514275)
                ·
                  refine ⟨30156823816823108355771413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20104549211215405570514275 30156823816823108355771413)
                  ·
                    refine ⟨1413601116413583204176785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30156823816823108355771413 1413601116413583204176785)
                    ·
                      rfl

theorem cell23_8258935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_8258935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258935 prefixEnd_8258935 := by exact prefixLift 8258935
  have htrace : WordTrace (prefixWord ++ tailWord_8258935) baseStart_8258935 baseEnd_8258935 := by
    simpa [prefixWord, tailWord_8258935, baseEnd_8258935] using wordTrace_append hprefix tailTrace_8258935
  have hstable : (prefixWord ++ tailWord_8258935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258935).length < 2 ^ (prefixWord ++ tailWord_8258935).sum := by decide
  have hdescent : baseEnd_8258935 < baseStart_8258935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258955 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 6]
def baseStart_8258955 : Nat := 118140960795 + 8258955 * 2 ^ 59
def prefixEnd_8258955 : Nat := 4983230072969 + 3 ^ 40 * 8258955 * 2
def baseEnd_8258955 : Nat := 4240813618853839534280263

theorem tailTrace_8258955 : CollatzResearch.WordTrace tailWord_8258955 prefixEnd_8258955 4240813618853839534280263 := by
  unfold tailWord_8258955
  simp only [CollatzResearch.WordTrace]
  refine ⟨301228835794224027062098319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200819223862816018041398879 301228835794224027062098319)
  ·
    refine ⟨451843253691336040593147479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301228835794224027062098319 451843253691336040593147479)
    ·
      refine ⟨677764880537004060889721219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451843253691336040593147479 677764880537004060889721219)
      ·
        refine ⟨1016647320805506091334581829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677764880537004060889721219 1016647320805506091334581829)
        ·
          refine ⟨190621372651032392125234093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1016647320805506091334581829 190621372651032392125234093)
          ·
            refine ⟨71483014744137147046962785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190621372651032392125234093 71483014744137147046962785)
            ·
              refine ⟨53612261058102860285222089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71483014744137147046962785 53612261058102860285222089)
              ·
                refine ⟨40209195793577145213916567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53612261058102860285222089 40209195793577145213916567)
                ·
                  refine ⟨60313793690365717820874851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40209195793577145213916567 60313793690365717820874851)
                  ·
                    refine ⟨90470690535548576731312277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60313793690365717820874851 90470690535548576731312277)
                    ·
                      refine ⟨4240813618853839534280263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90470690535548576731312277 4240813618853839534280263)
                      ·
                        rfl

theorem cell23_8258955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 6].length) (baseStart_8258955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258955 prefixEnd_8258955 := by exact prefixLift 8258955
  have htrace : WordTrace (prefixWord ++ tailWord_8258955) baseStart_8258955 baseEnd_8258955 := by
    simpa [prefixWord, tailWord_8258955, baseEnd_8258955] using wordTrace_append hprefix tailTrace_8258955
  have hstable : (prefixWord ++ tailWord_8258955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258955).length < 2 ^ (prefixWord ++ tailWord_8258955).sum := by decide
  have hdescent : baseEnd_8258955 < baseStart_8258955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8258979 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 1, 2, 3]
def baseStart_8258979 : Nat := 118140960795 + 8258979 * 2 ^ 59
def prefixEnd_8258979 : Nat := 4983230072969 + 3 ^ 40 * 8258979 * 2
def baseEnd_8258979 : Nat := 4240825942389547440380153

theorem tailTrace_8258979 : CollatzResearch.WordTrace tailWord_8258979 prefixEnd_8258979 4240825942389547440380153 := by
  unfold tailWord_8258979
  simp only [CollatzResearch.WordTrace]
  refine ⟨301229711146137079160971991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200819807430758052773981327 301229711146137079160971991)
  ·
    refine ⟨451844566719205618741457987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301229711146137079160971991 451844566719205618741457987)
    ·
      refine ⟨677766850078808428112186981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451844566719205618741457987 677766850078808428112186981)
      ·
        refine ⟨127081284389776580271035059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 677766850078808428112186981 127081284389776580271035059)
        ·
          refine ⟨190621926584664870406552589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127081284389776580271035059 190621926584664870406552589)
          ·
            refine ⟨71483222469249326402457221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190621926584664870406552589 71483222469249326402457221)
            ·
              refine ⟨13403104212984248700460729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71483222469249326402457221 13403104212984248700460729)
              ·
                refine ⟨10052328159738186525345547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13403104212984248700460729 10052328159738186525345547)
                ·
                  refine ⟨15078492239607279788018321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10052328159738186525345547 15078492239607279788018321)
                  ·
                    refine ⟨11308869179705459841013741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15078492239607279788018321 11308869179705459841013741)
                    ·
                      refine ⟨4240825942389547440380153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11308869179705459841013741 4240825942389547440380153)
                      ·
                        rfl

theorem cell23_8258979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_8258979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8258979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8258979 prefixEnd_8258979 := by exact prefixLift 8258979
  have htrace : WordTrace (prefixWord ++ tailWord_8258979) baseStart_8258979 baseEnd_8258979 := by
    simpa [prefixWord, tailWord_8258979, baseEnd_8258979] using wordTrace_append hprefix tailTrace_8258979
  have hstable : (prefixWord ++ tailWord_8258979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8258979).length < 2 ^ (prefixWord ++ tailWord_8258979).sum := by decide
  have hdescent : baseEnd_8258979 < baseStart_8258979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8258979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259079 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_8259079 : Nat := 118140960795 + 8259079 * 2 ^ 59
def prefixEnd_8259079 : Nat := 4983230072969 + 3 ^ 40 * 8259079 * 2
def baseEnd_8259079 : Nat := 4240877290454997049129693

theorem tailTrace_8259079 : CollatzResearch.WordTrace tailWord_8259079 prefixEnd_8259079 4240877290454997049129693 := by
  unfold tailWord_8259079
  simp only [CollatzResearch.WordTrace]
  refine ⟨301233358445774796239612291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200822238963849864159741527 301233358445774796239612291)
  ·
    refine ⟨451850037668662194359418437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301233358445774796239612291 451850037668662194359418437)
    ·
      refine ⟨84721882062874161442390957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451850037668662194359418437 84721882062874161442390957)
      ·
        refine ⟨31770705773577810540896609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84721882062874161442390957 31770705773577810540896609)
        ·
          refine ⟨23828029330183357905672457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31770705773577810540896609 23828029330183357905672457)
          ·
            refine ⟨17871021997637518429254343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23828029330183357905672457 17871021997637518429254343)
            ·
              refine ⟨26806532996456277643881515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17871021997637518429254343 26806532996456277643881515)
              ·
                refine ⟨40209799494684416465822273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26806532996456277643881515 40209799494684416465822273)
                ·
                  refine ⟨30157349621013312349366705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40209799494684416465822273 30157349621013312349366705)
                  ·
                    refine ⟨22618012215759984262025029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30157349621013312349366705 22618012215759984262025029)
                    ·
                      refine ⟨4240877290454997049129693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22618012215759984262025029 4240877290454997049129693)
                      ·
                        rfl

theorem cell23_8259079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_8259079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259079 prefixEnd_8259079 := by exact prefixLift 8259079
  have htrace : WordTrace (prefixWord ++ tailWord_8259079) baseStart_8259079 baseEnd_8259079 := by
    simpa [prefixWord, tailWord_8259079, baseEnd_8259079] using wordTrace_append hprefix tailTrace_8259079
  have hstable : (prefixWord ++ tailWord_8259079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259079).length < 2 ^ (prefixWord ++ tailWord_8259079).sum := by decide
  have hdescent : baseEnd_8259079 < baseStart_8259079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259152 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 4]
def baseStart_8259152 : Nat := 118140960795 + 8259152 * 2 ^ 59
def prefixEnd_8259152 : Nat := 4983230072969 + 3 ^ 40 * 8259152 * 2
def baseEnd_8259152 : Nat := 4240914774542775263516857

theorem tailTrace_8259152 : CollatzResearch.WordTrace tailWord_8259152 prefixEnd_8259152 4240914774542775263516857 := by
  unfold tailWord_8259152
  simp only [CollatzResearch.WordTrace]
  refine ⟨150618010487255164853509855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200824013983006886471346473 150618010487255164853509855)
  ·
    refine ⟨225927015730882747280264783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150618010487255164853509855 225927015730882747280264783)
    ·
      refine ⟨338890523596324120920397175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225927015730882747280264783 338890523596324120920397175)
      ·
        refine ⟨508335785394486181380595763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338890523596324120920397175 508335785394486181380595763)
        ·
          refine ⟨762503678091729272070893645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508335785394486181380595763 762503678091729272070893645)
          ·
            refine ⟨285938879284398477026585117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 762503678091729272070893645 285938879284398477026585117)
            ·
              refine ⟨107227079731649428884969419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285938879284398477026585117 107227079731649428884969419)
              ·
                refine ⟨160840619597474143327454129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107227079731649428884969419 160840619597474143327454129)
                ·
                  refine ⟨120630464698105607495590597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160840619597474143327454129 120630464698105607495590597)
                  ·
                    refine ⟨22618212130894801405423237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120630464698105607495590597 22618212130894801405423237)
                    ·
                      refine ⟨4240914774542775263516857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22618212130894801405423237 4240914774542775263516857)
                      ·
                        rfl

theorem cell23_8259152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_8259152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259152 prefixEnd_8259152 := by exact prefixLift 8259152
  have htrace : WordTrace (prefixWord ++ tailWord_8259152) baseStart_8259152 baseEnd_8259152 := by
    simpa [prefixWord, tailWord_8259152, baseEnd_8259152] using wordTrace_append hprefix tailTrace_8259152
  have hstable : (prefixWord ++ tailWord_8259152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259152).length < 2 ^ (prefixWord ++ tailWord_8259152).sum := by decide
  have hdescent : baseEnd_8259152 < baseStart_8259152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259159 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 3]
def baseStart_8259159 : Nat := 118140960795 + 8259159 * 2 ^ 59
def prefixEnd_8259159 : Nat := 4983230072969 + 3 ^ 40 * 8259159 * 2
def baseEnd_8259159 : Nat := 4240918368907356736129325

theorem tailTrace_8259159 : CollatzResearch.WordTrace tailWord_8259159 prefixEnd_8259159 4240918368907356736129325 := by
  unfold tailWord_8259159
  simp only [CollatzResearch.WordTrace]
  refine ⟨301236276285484969902524531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200824184190323313268349687 301236276285484969902524531)
  ·
    refine ⟨451854414428227454853786797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301236276285484969902524531 451854414428227454853786797)
    ·
      refine ⟨169445405410585295570170049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451854414428227454853786797 169445405410585295570170049)
      ·
        refine ⟨127084054057938971677627537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169445405410585295570170049 127084054057938971677627537)
        ·
          refine ⟨95313040543454228758220653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127084054057938971677627537 95313040543454228758220653)
          ·
            refine ⟨35742390203795335784332745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95313040543454228758220653 35742390203795335784332745)
            ·
              refine ⟨26806792652846501838249559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35742390203795335784332745 26806792652846501838249559)
              ·
                refine ⟨40210188979269752757374339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26806792652846501838249559 40210188979269752757374339)
                ·
                  refine ⟨60315283468904629136061509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40210188979269752757374339 60315283468904629136061509)
                  ·
                    refine ⟨11309115650419617963011533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60315283468904629136061509 11309115650419617963011533)
                    ·
                      refine ⟨4240918368907356736129325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11309115650419617963011533 4240918368907356736129325)
                      ·
                        rfl

theorem cell23_8259159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_8259159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259159 prefixEnd_8259159 := by exact prefixLift 8259159
  have htrace : WordTrace (prefixWord ++ tailWord_8259159) baseStart_8259159 baseEnd_8259159 := by
    simpa [prefixWord, tailWord_8259159, baseEnd_8259159] using wordTrace_append hprefix tailTrace_8259159
  have hstable : (prefixWord ++ tailWord_8259159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259159).length < 2 ^ (prefixWord ++ tailWord_8259159).sum := by decide
  have hdescent : baseEnd_8259159 < baseStart_8259159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259176 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_8259176 : Nat := 118140960795 + 8259176 * 2 ^ 59
def prefixEnd_8259176 : Nat := 4983230072969 + 3 ^ 40 * 8259176 * 2
def baseEnd_8259176 : Nat := 4240927098078483169616747

theorem tailTrace_8259176 : CollatzResearch.WordTrace tailWord_8259176 prefixEnd_8259176 4240927098078483169616747 := by
  unfold tailWord_8259176
  simp only [CollatzResearch.WordTrace]
  refine ⟨150618448163211690902946691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200824597550948921203928921 150618448163211690902946691)
  ·
    refine ⟨225927672244817536354420037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150618448163211690902946691 225927672244817536354420037)
    ·
      refine ⟨42361438545903288066453757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225927672244817536354420037 42361438545903288066453757)
      ·
        refine ⟨15885539454713733024920159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42361438545903288066453757 15885539454713733024920159)
        ·
          refine ⟨23828309182070599537380239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15885539454713733024920159 23828309182070599537380239)
          ·
            refine ⟨35742463773105899306070359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23828309182070599537380239 35742463773105899306070359)
            ·
              refine ⟨53613695659658848959105539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35742463773105899306070359 53613695659658848959105539)
              ·
                refine ⟨80420543489488273438658309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53613695659658848959105539 80420543489488273438658309)
                ·
                  refine ⟨15078851904279051269748433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80420543489488273438658309 15078851904279051269748433)
                  ·
                    refine ⟨11309138928209288452311325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15078851904279051269748433 11309138928209288452311325)
                    ·
                      refine ⟨4240927098078483169616747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11309138928209288452311325 4240927098078483169616747)
                      ·
                        rfl

theorem cell23_8259176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_8259176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259176 prefixEnd_8259176 := by exact prefixLift 8259176
  have htrace : WordTrace (prefixWord ++ tailWord_8259176) baseStart_8259176 baseEnd_8259176 := by
    simpa [prefixWord, tailWord_8259176, baseEnd_8259176] using wordTrace_append hprefix tailTrace_8259176
  have hstable : (prefixWord ++ tailWord_8259176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259176).length < 2 ^ (prefixWord ++ tailWord_8259176).sum := by decide
  have hdescent : baseEnd_8259176 < baseStart_8259176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259233 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 2, 3, 2]
def baseStart_8259233 : Nat := 118140960795 + 8259233 * 2 ^ 59
def prefixEnd_8259233 : Nat := 4983230072969 + 3 ^ 40 * 8259233 * 2
def baseEnd_8259233 : Nat := 4240956366475789446603985

theorem tailTrace_8259233 : CollatzResearch.WordTrace tailWord_8259233 prefixEnd_8259233 4240956366475789446603985 := by
  unfold tailWord_8259233
  simp only [CollatzResearch.WordTrace]
  refine ⟨301238975287216880540718353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200825983524811253693812235 301238975287216880540718353)
  ·
    refine ⟨225929231465412660405538765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301238975287216880540718353 225929231465412660405538765)
    ·
      refine ⟨84723461799529747652077037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225929231465412660405538765 84723461799529747652077037)
      ·
        refine ⟨31771298174823655369528889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84723461799529747652077037 31771298174823655369528889)
        ·
          refine ⟨23828473631117741527146667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31771298174823655369528889 23828473631117741527146667)
          ·
            refine ⟨35742710446676612290720001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23828473631117741527146667 35742710446676612290720001)
            ·
              refine ⟨26807032835007459218040001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35742710446676612290720001 26807032835007459218040001)
              ·
                refine ⟨20105274626255594413530001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26807032835007459218040001 20105274626255594413530001)
                ·
                  refine ⟨15078955969691695810147501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20105274626255594413530001 15078955969691695810147501)
                  ·
                    refine ⟨5654608488634385928805313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15078955969691695810147501 5654608488634385928805313)
                    ·
                      refine ⟨4240956366475789446603985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5654608488634385928805313 4240956366475789446603985)
                      ·
                        rfl

theorem cell23_8259233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_8259233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259233 prefixEnd_8259233 := by exact prefixLift 8259233
  have htrace : WordTrace (prefixWord ++ tailWord_8259233) baseStart_8259233 baseEnd_8259233 := by
    simpa [prefixWord, tailWord_8259233, baseEnd_8259233] using wordTrace_append hprefix tailTrace_8259233
  have hstable : (prefixWord ++ tailWord_8259233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259233).length < 2 ^ (prefixWord ++ tailWord_8259233).sum := by decide
  have hdescent : baseEnd_8259233 < baseStart_8259233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259234 : List Nat := [3, 3, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_8259234 : Nat := 118140960795 + 8259234 * 2 ^ 59
def prefixEnd_8259234 : Nat := 4983230072969 + 3 ^ 40 * 8259234 * 2
def baseEnd_8259234 : Nat := 1413652293318814647563827

theorem tailTrace_8259234 : CollatzResearch.WordTrace tailWord_8259234 prefixEnd_8259234 1413652293318814647563827 := by
  unfold tailWord_8259234
  simp only [CollatzResearch.WordTrace]
  refine ⟨75309752940053314427876189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200826007840142171807669837 75309752940053314427876189)
  ·
    refine ⟨28241157352519992910453571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75309752940053314427876189 28241157352519992910453571)
    ·
      refine ⟨42361736028779989365680357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28241157352519992910453571 42361736028779989365680357)
      ·
        refine ⟨7942825505396248006065067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42361736028779989365680357 7942825505396248006065067)
        ·
          refine ⟨11914238258094372009097601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7942825505396248006065067 11914238258094372009097601)
          ·
            refine ⟨8935678693570779006823201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11914238258094372009097601 8935678693570779006823201)
            ·
              refine ⟨6701759020178084255117401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8935678693570779006823201 6701759020178084255117401)
              ·
                refine ⟨5026319265133563191338051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6701759020178084255117401 5026319265133563191338051)
                ·
                  refine ⟨7539478897700344787007077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5026319265133563191338051 7539478897700344787007077)
                  ·
                    refine ⟨1413652293318814647563827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7539478897700344787007077 1413652293318814647563827)
                    ·
                      rfl

theorem cell23_8259234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_8259234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259234 prefixEnd_8259234 := by exact prefixLift 8259234
  have htrace : WordTrace (prefixWord ++ tailWord_8259234) baseStart_8259234 baseEnd_8259234 := by
    simpa [prefixWord, tailWord_8259234, baseEnd_8259234] using wordTrace_append hprefix tailTrace_8259234
  have hstable : (prefixWord ++ tailWord_8259234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259234).length < 2 ^ (prefixWord ++ tailWord_8259234).sum := by decide
  have hdescent : baseEnd_8259234 < baseStart_8259234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259263 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 3, 2, 2]
def baseStart_8259263 : Nat := 118140960795 + 8259263 * 2 ^ 59
def prefixEnd_8259263 : Nat := 4983230072969 + 3 ^ 40 * 8259263 * 2
def baseEnd_8259263 : Nat := 4240971770895424329228847

theorem tailTrace_8259263 : CollatzResearch.WordTrace tailWord_8259263 prefixEnd_8259263 4240971770895424329228847 := by
  unfold tailWord_8259263
  simp only [CollatzResearch.WordTrace]
  refine ⟨301240069477108195664310443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200826712984738797109540295 301240069477108195664310443)
  ·
    refine ⟨451860104215662293496465665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301240069477108195664310443 451860104215662293496465665)
    ·
      refine ⟨338895078161746720122349249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451860104215662293496465665 338895078161746720122349249)
      ·
        refine ⟨254171308621310040091761937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338895078161746720122349249 254171308621310040091761937)
        ·
          refine ⟨190628481465982530068821453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254171308621310040091761937 190628481465982530068821453)
          ·
            refine ⟨71485680549743448775808045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190628481465982530068821453 71485680549743448775808045)
            ·
              refine ⟨26807130206153793290928017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71485680549743448775808045 26807130206153793290928017)
              ·
                refine ⟨20105347654615344968196013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26807130206153793290928017 20105347654615344968196013)
                ·
                  refine ⟨7539505370480754363073505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20105347654615344968196013 7539505370480754363073505)
                  ·
                    refine ⟨5654629027860565772305129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7539505370480754363073505 5654629027860565772305129)
                    ·
                      refine ⟨4240971770895424329228847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5654629027860565772305129 4240971770895424329228847)
                      ·
                        rfl

theorem cell23_8259263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 2, 2].length) (baseStart_8259263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259263 prefixEnd_8259263 := by exact prefixLift 8259263
  have htrace : WordTrace (prefixWord ++ tailWord_8259263) baseStart_8259263 baseEnd_8259263 := by
    simpa [prefixWord, tailWord_8259263, baseEnd_8259263] using wordTrace_append hprefix tailTrace_8259263
  have hstable : (prefixWord ++ tailWord_8259263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259263).length < 2 ^ (prefixWord ++ tailWord_8259263).sum := by decide
  have hdescent : baseEnd_8259263 < baseStart_8259263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259277 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_8259277 : Nat := 118140960795 + 8259277 * 2 ^ 59
def prefixEnd_8259277 : Nat := 4983230072969 + 3 ^ 40 * 8259277 * 2
def baseEnd_8259277 : Nat := 1413659653208195758151261

theorem tailTrace_8259277 : CollatzResearch.WordTrace tailWord_8259277 prefixEnd_8259277 1413659653208195758151261 := by
  unfold tailWord_8259277
  simp only [CollatzResearch.WordTrace]
  refine ⟨301240580099057476055320085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200827053399371650703546723 301240580099057476055320085)
  ·
    refine ⟨14120652192143319190093129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 301240580099057476055320085 14120652192143319190093129)
    ·
      refine ⟨10590489144107489392569847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14120652192143319190093129 10590489144107489392569847)
      ·
        refine ⟨15885733716161234088854771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10590489144107489392569847 15885733716161234088854771)
        ·
          refine ⟨23828600574241851133282157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15885733716161234088854771 23828600574241851133282157)
          ·
            refine ⟨8935725215340694174980809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23828600574241851133282157 8935725215340694174980809)
            ·
              refine ⟨6701793911505520631235607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8935725215340694174980809 6701793911505520631235607)
              ·
                refine ⟨10052690867258280946853411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701793911505520631235607 10052690867258280946853411)
                ·
                  refine ⟨15079036300887421420280117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10052690867258280946853411 15079036300887421420280117)
                  ·
                    refine ⟨1413659653208195758151261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15079036300887421420280117 1413659653208195758151261)
                    ·
                      rfl

theorem cell23_8259277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_8259277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259277 prefixEnd_8259277 := by exact prefixLift 8259277
  have htrace : WordTrace (prefixWord ++ tailWord_8259277) baseStart_8259277 baseEnd_8259277 := by
    simpa [prefixWord, tailWord_8259277, baseEnd_8259277] using wordTrace_append hprefix tailTrace_8259277
  have hstable : (prefixWord ++ tailWord_8259277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259277).length < 2 ^ (prefixWord ++ tailWord_8259277).sum := by decide
  have hdescent : baseEnd_8259277 < baseStart_8259277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259313 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 1, 3, 3]
def baseStart_8259313 : Nat := 118140960795 + 8259313 * 2 ^ 59
def prefixEnd_8259313 : Nat := 4983230072969 + 3 ^ 40 * 8259313 * 2
def baseEnd_8259313 : Nat := 4240997444928149133603617

theorem tailTrace_8259313 : CollatzResearch.WordTrace tailWord_8259313 prefixEnd_8259313 4240997444928149133603617 := by
  unfold tailWord_8259313
  simp only [CollatzResearch.WordTrace]
  refine ⟨301241893126927054203630593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200827928751284702802420395 301241893126927054203630593)
  ·
    refine ⟨225931419845195290652722945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301241893126927054203630593 225931419845195290652722945)
    ·
      refine ⟨169448564883896467989542209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225931419845195290652722945 169448564883896467989542209)
      ·
        refine ⟨127086423662922350992156657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169448564883896467989542209 127086423662922350992156657)
        ·
          refine ⟨95314817747191763244117493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127086423662922350992156657 95314817747191763244117493)
          ·
            refine ⟨8935764163799227804136015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95314817747191763244117493 8935764163799227804136015)
            ·
              refine ⟨13403646245698841706204023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935764163799227804136015 13403646245698841706204023)
              ·
                refine ⟨20105469368548262559306035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13403646245698841706204023 20105469368548262559306035)
                ·
                  refine ⟨30158204052822393838959053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20105469368548262559306035 30158204052822393838959053)
                  ·
                    refine ⟨11309326519808397689609645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30158204052822393838959053 11309326519808397689609645)
                    ·
                      refine ⟨4240997444928149133603617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11309326519808397689609645 4240997444928149133603617)
                      ·
                        rfl

theorem cell23_8259313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_8259313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259313 prefixEnd_8259313 := by exact prefixLift 8259313
  have htrace : WordTrace (prefixWord ++ tailWord_8259313) baseStart_8259313 baseEnd_8259313 := by
    simpa [prefixWord, tailWord_8259313, baseEnd_8259313] using wordTrace_append hprefix tailTrace_8259313
  have hstable : (prefixWord ++ tailWord_8259313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259313).length < 2 ^ (prefixWord ++ tailWord_8259313).sum := by decide
  have hdescent : baseEnd_8259313 < baseStart_8259313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259319 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_8259319 : Nat := 118140960795 + 8259319 * 2 ^ 59
def prefixEnd_8259319 : Nat := 4983230072969 + 3 ^ 40 * 8259319 * 2
def baseEnd_8259319 : Nat := 4241000525812076110128589

theorem tailTrace_8259319 : CollatzResearch.WordTrace tailWord_8259319 prefixEnd_8259319 4241000525812076110128589 := by
  unfold tailWord_8259319
  simp only [CollatzResearch.WordTrace]
  refine ⟨301242111964905317228349011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200828074643270211485566007 301242111964905317228349011)
  ·
    refine ⟨451863167947357975842523517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301242111964905317228349011 451863167947357975842523517)
    ·
      refine ⟨169448687980259240940946319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451863167947357975842523517 169448687980259240940946319)
      ·
        refine ⟨254173031970388861411419479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169448687980259240940946319 254173031970388861411419479)
        ·
          refine ⟨381259547955583292117129219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254173031970388861411419479 381259547955583292117129219)
          ·
            refine ⟨571889321933374938175693829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381259547955583292117129219 571889321933374938175693829)
            ·
              refine ⟨107229247862507800907942593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 571889321933374938175693829 107229247862507800907942593)
              ·
                refine ⟨80421935896880850680956945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107229247862507800907942593 80421935896880850680956945)
                ·
                  refine ⟨60316451922660638010717709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80421935896880850680956945 60316451922660638010717709)
                  ·
                    refine ⟨22618669470997739254019141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60316451922660638010717709 22618669470997739254019141)
                    ·
                      refine ⟨4241000525812076110128589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22618669470997739254019141 4241000525812076110128589)
                      ·
                        rfl

theorem cell23_8259319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_8259319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259319 prefixEnd_8259319 := by exact prefixLift 8259319
  have htrace : WordTrace (prefixWord ++ tailWord_8259319) baseStart_8259319 baseEnd_8259319 := by
    simpa [prefixWord, tailWord_8259319, baseEnd_8259319] using wordTrace_append hprefix tailTrace_8259319
  have hstable : (prefixWord ++ tailWord_8259319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259319).length < 2 ^ (prefixWord ++ tailWord_8259319).sum := by decide
  have hdescent : baseEnd_8259319 < baseStart_8259319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259329 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 1, 8]
def baseStart_8259329 : Nat := 118140960795 + 8259329 * 2 ^ 59
def prefixEnd_8259329 : Nat := 4983230072969 + 3 ^ 40 * 8259329 * 2
def baseEnd_8259329 : Nat := 1413668553539540357001181

theorem tailTrace_8259329 : CollatzResearch.WordTrace tailWord_8259329 prefixEnd_8259329 1413668553539540357001181 := by
  unfold tailWord_8259329
  simp only [CollatzResearch.WordTrace]
  refine ⟨301242476694869088936213041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200828317796579392624142027 301242476694869088936213041)
  ·
    refine ⟨225931857521151816702159781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301242476694869088936213041 225931857521151816702159781)
    ·
      refine ⟨42362223285215965631654959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225931857521151816702159781 42362223285215965631654959)
      ·
        refine ⟨63543334927823948447482439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42362223285215965631654959 63543334927823948447482439)
        ·
          refine ⟨95315002391735922671223659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63543334927823948447482439 95315002391735922671223659)
          ·
            refine ⟨142972503587603884006835489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95315002391735922671223659 142972503587603884006835489)
            ·
              refine ⟨107229377690702913005126617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142972503587603884006835489 107229377690702913005126617)
              ·
                refine ⟨80422033268027184753844963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107229377690702913005126617 80422033268027184753844963)
                ·
                  refine ⟨120633049902040777130767445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80422033268027184753844963 120633049902040777130767445)
                  ·
                    refine ⟨1413668553539540357001181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120633049902040777130767445 1413668553539540357001181)
                    ·
                      rfl

theorem cell23_8259329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_8259329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259329 prefixEnd_8259329 := by exact prefixLift 8259329
  have htrace : WordTrace (prefixWord ++ tailWord_8259329) baseStart_8259329 baseEnd_8259329 := by
    simpa [prefixWord, tailWord_8259329, baseEnd_8259329] using wordTrace_append hprefix tailTrace_8259329
  have hstable : (prefixWord ++ tailWord_8259329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259329).length < 2 ^ (prefixWord ++ tailWord_8259329).sum := by decide
  have hdescent : baseEnd_8259329 < baseStart_8259329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259339 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 5]
def baseStart_8259339 : Nat := 118140960795 + 8259339 * 2 ^ 59
def prefixEnd_8259339 : Nat := 4983230072969 + 3 ^ 40 * 8259339 * 2
def baseEnd_8259339 : Nat := 4241010795425166031878497

theorem tailTrace_8259339 : CollatzResearch.WordTrace tailWord_8259339 prefixEnd_8259339 4241010795425166031878497 := by
  unfold tailWord_8259339
  simp only [CollatzResearch.WordTrace]
  refine ⟨301242841424832860644077071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200828560949888573762718047 301242841424832860644077071)
  ·
    refine ⟨451864262137249290966115607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301242841424832860644077071 451864262137249290966115607)
    ·
      refine ⟨677796393205873936449173411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451864262137249290966115607 677796393205873936449173411)
      ·
        refine ⟨1016694589808810904673760117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677796393205873936449173411 1016694589808810904673760117)
        ·
          refine ⟨95315117794576022313165011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1016694589808810904673760117 95315117794576022313165011)
          ·
            refine ⟨142972676691864033469747517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95315117794576022313165011 142972676691864033469747517)
            ·
              refine ⟨53614753759449012551155319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142972676691864033469747517 53614753759449012551155319)
              ·
                refine ⟨80422130639173518826732979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53614753759449012551155319 80422130639173518826732979)
                ·
                  refine ⟨120633195958760278240099469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80422130639173518826732979 120633195958760278240099469)
                  ·
                    refine ⟨45237448484535104340037301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120633195958760278240099469 45237448484535104340037301)
                    ·
                      refine ⟨4241010795425166031878497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45237448484535104340037301 4241010795425166031878497)
                      ·
                        rfl

theorem cell23_8259339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_8259339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259339 prefixEnd_8259339 := by exact prefixLift 8259339
  have htrace : WordTrace (prefixWord ++ tailWord_8259339) baseStart_8259339 baseEnd_8259339 := by
    simpa [prefixWord, tailWord_8259339, baseEnd_8259339] using wordTrace_append hprefix tailTrace_8259339
  have hstable : (prefixWord ++ tailWord_8259339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259339).length < 2 ^ (prefixWord ++ tailWord_8259339).sum := by decide
  have hdescent : baseEnd_8259339 < baseStart_8259339 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259348 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_8259348 : Nat := 118140960795 + 8259348 * 2 ^ 59
def prefixEnd_8259348 : Nat := 4983230072969 + 3 ^ 40 * 8259348 * 2
def baseEnd_8259348 : Nat := 4241015416751056496665957

theorem tailTrace_8259348 : CollatzResearch.WordTrace tailWord_8259348 prefixEnd_8259348 4241015416751056496665957 := by
  unfold tailWord_8259348
  simp only [CollatzResearch.WordTrace]
  refine ⟨150621584840900127590577349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200828779787866836787436465 150621584840900127590577349)
  ·
    refine ⟨28241547157668773923233253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150621584840900127590577349 28241547157668773923233253)
    ·
      refine ⟨5295290092062895110606235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28241547157668773923233253 5295290092062895110606235)
      ·
        refine ⟨7942935138094342665909353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295290092062895110606235 7942935138094342665909353)
        ·
          refine ⟨5957201353570756999432015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7942935138094342665909353 5957201353570756999432015)
          ·
            refine ⟨8935802030356135499148023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957201353570756999432015 8935802030356135499148023)
            ·
              refine ⟨13403703045534203248722035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935802030356135499148023 13403703045534203248722035)
              ·
                refine ⟨20105554568301304873083053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13403703045534203248722035 20105554568301304873083053)
                ·
                  refine ⟨7539582963112989327406145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20105554568301304873083053 7539582963112989327406145)
                  ·
                    refine ⟨5654687222334741995554609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7539582963112989327406145 5654687222334741995554609)
                    ·
                      refine ⟨4241015416751056496665957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5654687222334741995554609 4241015416751056496665957)
                      ·
                        rfl

theorem cell23_8259348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_8259348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259348 prefixEnd_8259348 := by exact prefixLift 8259348
  have htrace : WordTrace (prefixWord ++ tailWord_8259348) baseStart_8259348 baseEnd_8259348 := by
    simpa [prefixWord, tailWord_8259348, baseEnd_8259348] using wordTrace_append hprefix tailTrace_8259348
  have hstable : (prefixWord ++ tailWord_8259348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259348).length < 2 ^ (prefixWord ++ tailWord_8259348).sum := by decide
  have hdescent : baseEnd_8259348 < baseStart_8259348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259356 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_8259356 : Nat := 118140960795 + 8259356 * 2 ^ 59
def prefixEnd_8259356 : Nat := 4983230072969 + 3 ^ 40 * 8259356 * 2
def baseEnd_8259356 : Nat := 4241019524596292465365919

theorem tailTrace_8259356 : CollatzResearch.WordTrace tailWord_8259356 prefixEnd_8259356 4241019524596292465365919 := by
  unfold tailWord_8259356
  simp only [CollatzResearch.WordTrace]
  refine ⟨150621730732885636273722961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200828974310514181698297281 150621730732885636273722961)
  ·
    refine ⟨112966298049664227205292221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150621730732885636273722961 112966298049664227205292221)
    ·
      refine ⟨42362361768624085201984583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112966298049664227205292221 42362361768624085201984583)
      ·
        refine ⟨63543542652936127802976875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42362361768624085201984583 63543542652936127802976875)
        ·
          refine ⟨95315313979404191704465313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63543542652936127802976875 95315313979404191704465313)
          ·
            refine ⟨71486485484553143778348985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95315313979404191704465313 71486485484553143778348985)
            ·
              refine ⟨53614864113414857833761739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71486485484553143778348985 53614864113414857833761739)
              ·
                refine ⟨80422296170122286750642609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53614864113414857833761739 80422296170122286750642609)
                ·
                  refine ⟨60316722127591715062981957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80422296170122286750642609 60316722127591715062981957)
                  ·
                    refine ⟨11309385398923446574309117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60316722127591715062981957 11309385398923446574309117)
                    ·
                      refine ⟨4241019524596292465365919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11309385398923446574309117 4241019524596292465365919)
                      ·
                        rfl

theorem cell23_8259356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_8259356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259356 prefixEnd_8259356 := by exact prefixLift 8259356
  have htrace : WordTrace (prefixWord ++ tailWord_8259356) baseStart_8259356 baseEnd_8259356 := by
    simpa [prefixWord, tailWord_8259356, baseEnd_8259356] using wordTrace_append hprefix tailTrace_8259356
  have hstable : (prefixWord ++ tailWord_8259356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259356).length < 2 ^ (prefixWord ++ tailWord_8259356).sum := by decide
  have hdescent : baseEnd_8259356 < baseStart_8259356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259374 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_8259374 : Nat := 118140960795 + 8259374 * 2 ^ 59
def prefixEnd_8259374 : Nat := 4983230072969 + 3 ^ 40 * 8259374 * 2
def baseEnd_8259374 : Nat := 4241028767248073394940837

theorem tailTrace_8259374 : CollatzResearch.WordTrace tailWord_8259374 prefixEnd_8259374 4241028767248073394940837 := by
  unfold tailWord_8259374
  simp only [CollatzResearch.WordTrace]
  refine ⟨37655514747463257702700147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200829411986470707747734117 37655514747463257702700147)
  ·
    refine ⟨56483272121194886554050221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37655514747463257702700147 56483272121194886554050221)
    ·
      refine ⟨21181227045448082457768833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56483272121194886554050221 21181227045448082457768833)
      ·
        refine ⟨15885920284086061843326625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21181227045448082457768833 15885920284086061843326625)
        ·
          refine ⟨11914440213064546382494969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15885920284086061843326625 11914440213064546382494969)
          ·
            refine ⟨8935830159798409786871227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11914440213064546382494969 8935830159798409786871227)
            ·
              refine ⟨13403745239697614680306841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935830159798409786871227 13403745239697614680306841)
              ·
                refine ⟨10052808929773211010230131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13403745239697614680306841 10052808929773211010230131)
                ·
                  refine ⟨15079213394659816515345197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10052808929773211010230131 15079213394659816515345197)
                  ·
                    refine ⟨5654705022997431193254449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15079213394659816515345197 5654705022997431193254449)
                    ·
                      refine ⟨4241028767248073394940837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5654705022997431193254449 4241028767248073394940837)
                      ·
                        rfl

theorem cell23_8259374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_8259374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259374 prefixEnd_8259374 := by exact prefixLift 8259374
  have htrace : WordTrace (prefixWord ++ tailWord_8259374) baseStart_8259374 baseEnd_8259374 := by
    simpa [prefixWord, tailWord_8259374, baseEnd_8259374] using wordTrace_append hprefix tailTrace_8259374
  have hstable : (prefixWord ++ tailWord_8259374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259374).length < 2 ^ (prefixWord ++ tailWord_8259374).sum := by decide
  have hdescent : baseEnd_8259374 < baseStart_8259374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259410 : List Nat := [3, 2, 2, 1, 1, 3, 4, 2, 5]
def baseStart_8259410 : Nat := 118140960795 + 8259410 * 2 ^ 59
def prefixEnd_8259410 : Nat := 4983230072969 + 3 ^ 40 * 8259410 * 2
def baseEnd_8259410 : Nat := 471227472505737250454519

theorem tailTrace_8259410 : CollatzResearch.WordTrace tailWord_8259410 prefixEnd_8259410 471227472505737250454519 := by
  unfold tailWord_8259410
  simp only [CollatzResearch.WordTrace]
  refine ⟨75311357751893909942477921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200830287338383759846607789 75311357751893909942477921)
  ·
    refine ⟨56483518313920432456858441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75311357751893909942477921 56483518313920432456858441)
    ·
      refine ⟨42362638735440324342643831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56483518313920432456858441 42362638735440324342643831)
      ·
        refine ⟨63543958103160486513965747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42362638735440324342643831 63543958103160486513965747)
        ·
          refine ⟨95315937154740729770948621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63543958103160486513965747 95315937154740729770948621)
          ·
            refine ⟨35743476433027773664105733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95315937154740729770948621 35743476433027773664105733)
            ·
              refine ⟨6701901831192707562019825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35743476433027773664105733 6701901831192707562019825)
              ·
                refine ⟨5026426373394530671514869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6701901831192707562019825 5026426373394530671514869)
                ·
                  refine ⟨471227472505737250454519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5026426373394530671514869 471227472505737250454519)
                  ·
                    rfl

theorem cell23_8259410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_8259410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259410 prefixEnd_8259410 := by exact prefixLift 8259410
  have htrace : WordTrace (prefixWord ++ tailWord_8259410) baseStart_8259410 baseEnd_8259410 := by
    simpa [prefixWord, tailWord_8259410, baseEnd_8259410] using wordTrace_append hprefix tailTrace_8259410
  have hstable : (prefixWord ++ tailWord_8259410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259410).length < 2 ^ (prefixWord ++ tailWord_8259410).sum := by decide
  have hdescent : baseEnd_8259410 < baseStart_8259410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259413 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 2, 5, 2]
def baseStart_8259413 : Nat := 118140960795 + 8259413 * 2 ^ 59
def prefixEnd_8259413 : Nat := 4983230072969 + 3 ^ 40 * 8259413 * 2
def baseEnd_8259413 : Nat := 4241048792993598742353157

theorem tailTrace_8259413 : CollatzResearch.WordTrace tailWord_8259413 prefixEnd_8259413 4241048792993598742353157 := by
  unfold tailWord_8259413
  simp only [CollatzResearch.WordTrace]
  refine ⟨301245540426564771282270893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200830360284376514188180595 301245540426564771282270893)
  ·
    refine ⟨112967077659961789230851585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301245540426564771282270893 112967077659961789230851585)
    ·
      refine ⟨84725308244971341923138689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112967077659961789230851585 84725308244971341923138689)
      ·
        refine ⟨63543981183728506442354017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84725308244971341923138689 63543981183728506442354017)
        ·
          refine ⟨47657985887796379831765513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63543981183728506442354017 47657985887796379831765513)
          ·
            refine ⟨35743489415847284873824135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47657985887796379831765513 35743489415847284873824135)
            ·
              refine ⟨53615234123770927310736203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35743489415847284873824135 53615234123770927310736203)
              ·
                refine ⟨80422851185656390966104305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53615234123770927310736203 80422851185656390966104305)
                ·
                  refine ⟨60317138389242293224578229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80422851185656390966104305 60317138389242293224578229)
                  ·
                    refine ⟨5654731723991464989804209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60317138389242293224578229 5654731723991464989804209)
                    ·
                      refine ⟨4241048792993598742353157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5654731723991464989804209 4241048792993598742353157)
                      ·
                        rfl

theorem cell23_8259413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_8259413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259413 prefixEnd_8259413 := by exact prefixLift 8259413
  have htrace : WordTrace (prefixWord ++ tailWord_8259413) baseStart_8259413 baseEnd_8259413 := by
    simpa [prefixWord, tailWord_8259413, baseEnd_8259413] using wordTrace_append hprefix tailTrace_8259413
  have hstable : (prefixWord ++ tailWord_8259413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259413).length < 2 ^ (prefixWord ++ tailWord_8259413).sum := by decide
  have hdescent : baseEnd_8259413 < baseStart_8259413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259420 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_8259420 : Nat := 118140960795 + 8259420 * 2 ^ 59
def prefixEnd_8259420 : Nat := 4983230072969 + 3 ^ 40 * 8259420 * 2
def baseEnd_8259420 : Nat := 4241052387358180214965625

theorem tailTrace_8259420 : CollatzResearch.WordTrace tailWord_8259420 prefixEnd_8259420 4241052387358180214965625 := by
  unfold tailWord_8259420
  simp only [CollatzResearch.WordTrace]
  refine ⟨150622897868769705738887857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200830530491692940985183809 150622897868769705738887857)
  ·
    refine ⟨112967173401577279304165893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150622897868769705738887857 112967173401577279304165893)
    ·
      refine ⟨21181345012795739869531105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112967173401577279304165893 21181345012795739869531105)
      ·
        refine ⟨15886008759596804902148329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21181345012795739869531105 15886008759596804902148329)
        ·
          refine ⟨11914506569697603676611247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15886008759596804902148329 11914506569697603676611247)
          ·
            refine ⟨17871759854546405514916871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11914506569697603676611247 17871759854546405514916871)
            ·
              refine ⟨26807639781819608272375307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17871759854546405514916871 26807639781819608272375307)
              ·
                refine ⟨40211459672729412408562961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26807639781819608272375307 40211459672729412408562961)
                ·
                  refine ⟨30158594754547059306422221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40211459672729412408562961 30158594754547059306422221)
                  ·
                    refine ⟨11309473032955147239908333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30158594754547059306422221 11309473032955147239908333)
                    ·
                      refine ⟨4241052387358180214965625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11309473032955147239908333 4241052387358180214965625)
                      ·
                        rfl

theorem cell23_8259420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_8259420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259420 prefixEnd_8259420 := by exact prefixLift 8259420
  have htrace : WordTrace (prefixWord ++ tailWord_8259420) baseStart_8259420 baseEnd_8259420 := by
    simpa [prefixWord, tailWord_8259420, baseEnd_8259420] using wordTrace_append hprefix tailTrace_8259420
  have hstable : (prefixWord ++ tailWord_8259420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259420).length < 2 ^ (prefixWord ++ tailWord_8259420).sum := by decide
  have hdescent : baseEnd_8259420 < baseStart_8259420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259503 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 1, 5, 2]
def baseStart_8259503 : Nat := 118140960795 + 8259503 * 2 ^ 59
def prefixEnd_8259503 : Nat := 4983230072969 + 3 ^ 40 * 8259503 * 2
def baseEnd_8259503 : Nat := 4241095006252503390227743

theorem tailTrace_8259503 : CollatzResearch.WordTrace tailWord_8259503 prefixEnd_8259503 4241095006252503390227743 := by
  unfold tailWord_8259503
  simp only [CollatzResearch.WordTrace]
  refine ⟨301248822996238716653047163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200832548664159144435364775 301248822996238716653047163)
  ·
    refine ⟨451873234494358074979570745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301248822996238716653047163 451873234494358074979570745)
    ·
      refine ⟨338904925870768556234678059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451873234494358074979570745 338904925870768556234678059)
      ·
        refine ⟨508357388806152834352017089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338904925870768556234678059 508357388806152834352017089)
        ·
          refine ⟨381268041604614625764012817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508357388806152834352017089 381268041604614625764012817)
          ·
            refine ⟨285951031203460969323009613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381268041604614625764012817 285951031203460969323009613)
            ·
              refine ⟨107231636701297863496128605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285951031203460969323009613 107231636701297863496128605)
              ·
                refine ⟨40211863762986698811048227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107231636701297863496128605 40211863762986698811048227)
                ·
                  refine ⟨60317795644480048216572341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40211863762986698811048227 60317795644480048216572341)
                  ·
                    refine ⟨5654793341670004520303657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60317795644480048216572341 5654793341670004520303657)
                    ·
                      refine ⟨4241095006252503390227743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5654793341670004520303657 4241095006252503390227743)
                      ·
                        rfl

theorem cell23_8259503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 5, 2].length) (baseStart_8259503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259503 prefixEnd_8259503 := by exact prefixLift 8259503
  have htrace : WordTrace (prefixWord ++ tailWord_8259503) baseStart_8259503 baseEnd_8259503 := by
    simpa [prefixWord, tailWord_8259503, baseEnd_8259503] using wordTrace_append hprefix tailTrace_8259503
  have hstable : (prefixWord ++ tailWord_8259503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259503).length < 2 ^ (prefixWord ++ tailWord_8259503).sum := by decide
  have hdescent : baseEnd_8259503 < baseStart_8259503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259513 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 1, 5]
def baseStart_8259513 : Nat := 118140960795 + 8259513 * 2 ^ 59
def prefixEnd_8259513 : Nat := 4983230072969 + 3 ^ 40 * 8259513 * 2
def baseEnd_8259513 : Nat := 1413700047019682783700899

theorem tailTrace_8259513 : CollatzResearch.WordTrace tailWord_8259513 prefixEnd_8259513 1413700047019682783700899 := by
  unfold tailWord_8259513
  simp only [CollatzResearch.WordTrace]
  refine ⟨301249187726202488360911193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200832791817468325573940795 301249187726202488360911193)
  ·
    refine ⟨225936890794651866270683395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301249187726202488360911193 225936890794651866270683395)
    ·
      refine ⟨338905336191977799406025093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225936890794651866270683395 338905336191977799406025093)
      ·
        refine ⟨63544750535995837388629705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338905336191977799406025093 63544750535995837388629705)
        ·
          refine ⟨47658562901996878041472279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63544750535995837388629705 47658562901996878041472279)
          ·
            refine ⟨71487844352995317062208419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47658562901996878041472279 71487844352995317062208419)
            ·
              refine ⟨107231766529492975593312629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71487844352995317062208419 107231766529492975593312629)
              ·
                refine ⟨10052978112139966461873059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107231766529492975593312629 10052978112139966461873059)
                ·
                  refine ⟨15079467168209949692809589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10052978112139966461873059 15079467168209949692809589)
                  ·
                    refine ⟨1413700047019682783700899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15079467168209949692809589 1413700047019682783700899)
                    ·
                      rfl

theorem cell23_8259513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 5].length) (baseStart_8259513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259513 prefixEnd_8259513 := by exact prefixLift 8259513
  have htrace : WordTrace (prefixWord ++ tailWord_8259513) baseStart_8259513 baseEnd_8259513 := by
    simpa [prefixWord, tailWord_8259513, baseEnd_8259513] using wordTrace_append hprefix tailTrace_8259513
  have hstable : (prefixWord ++ tailWord_8259513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259513).length < 2 ^ (prefixWord ++ tailWord_8259513).sum := by decide
  have hdescent : baseEnd_8259513 < baseStart_8259513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259520 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 2, 3, 2]
def baseStart_8259520 : Nat := 118140960795 + 8259520 * 2 ^ 59
def prefixEnd_8259520 : Nat := 4983230072969 + 3 ^ 40 * 8259520 * 2
def baseEnd_8259520 : Nat := 4241103735423629823715165

theorem tailTrace_8259520 : CollatzResearch.WordTrace tailWord_8259520 prefixEnd_8259520 4241103735423629823715165 := by
  unfold tailWord_8259520
  simp only [CollatzResearch.WordTrace]
  refine ⟨150624721518588564278208007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200832962024784752370944009 150624721518588564278208007)
  ·
    refine ⟨225937082277882846417312011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150624721518588564278208007 225937082277882846417312011)
    ·
      refine ⟨338905623416824269625968017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225937082277882846417312011 338905623416824269625968017)
      ·
        refine ⟨254179217562618202219476013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338905623416824269625968017 254179217562618202219476013)
        ·
          refine ⟨95317206585981825832303505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254179217562618202219476013 95317206585981825832303505)
          ·
            refine ⟨71487904939486369374227629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95317206585981825832303505 71487904939486369374227629)
            ·
              refine ⟨26807964352307388515335361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71487904939486369374227629 26807964352307388515335361)
              ·
                refine ⟨20105973264230541386501521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26807964352307388515335361 20105973264230541386501521)
                ·
                  refine ⟨15079479948172906039876141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20105973264230541386501521 15079479948172906039876141)
                  ·
                    refine ⟨5654804980564839764953553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15079479948172906039876141 5654804980564839764953553)
                    ·
                      refine ⟨4241103735423629823715165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5654804980564839764953553 4241103735423629823715165)
                      ·
                        rfl

theorem cell23_8259520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 3, 2].length) (baseStart_8259520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259520 prefixEnd_8259520 := by exact prefixLift 8259520
  have htrace : WordTrace (prefixWord ++ tailWord_8259520) baseStart_8259520 baseEnd_8259520 := by
    simpa [prefixWord, tailWord_8259520, baseEnd_8259520] using wordTrace_append hprefix tailTrace_8259520
  have hstable : (prefixWord ++ tailWord_8259520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259520).length < 2 ^ (prefixWord ++ tailWord_8259520).sum := by decide
  have hdescent : baseEnd_8259520 < baseStart_8259520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259556 : List Nat := [2, 3, 1, 1, 1, 1, 3, 11]
def baseStart_8259556 : Nat := 118140960795 + 8259556 * 2 ^ 59
def prefixEnd_8259556 : Nat := 4983230072969 + 3 ^ 40 * 8259556 * 2
def baseEnd_8259556 : Nat := 157078600767673766032037

theorem tailTrace_8259556 : CollatzResearch.WordTrace tailWord_8259556 prefixEnd_8259556 157078600767673766032037 := by
  unfold tailWord_8259556
  simp only [CollatzResearch.WordTrace]
  refine ⟨150625378032523353352363261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200833837376697804469817681 150625378032523353352363261)
  ·
    refine ⟨56484516762196257507136223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150625378032523353352363261 56484516762196257507136223)
    ·
      refine ⟨84726775143294386260704335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56484516762196257507136223 84726775143294386260704335)
      ·
        refine ⟨127090162714941579391056503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84726775143294386260704335 127090162714941579391056503)
        ·
          refine ⟨190635244072412369086584755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127090162714941579391056503 190635244072412369086584755)
          ·
            refine ⟨285952866108618553629877133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190635244072412369086584755 285952866108618553629877133)
            ·
              refine ⟨107232324790731957611203925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285952866108618553629877133 107232324790731957611203925)
              ·
                refine ⟨157078600767673766032037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 107232324790731957611203925 157078600767673766032037)
                ·
                  rfl

theorem cell23_8259556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 11].length) (baseStart_8259556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259556 prefixEnd_8259556 := by exact prefixLift 8259556
  have htrace : WordTrace (prefixWord ++ tailWord_8259556) baseStart_8259556 baseEnd_8259556 := by
    simpa [prefixWord, tailWord_8259556, baseEnd_8259556] using wordTrace_append hprefix tailTrace_8259556
  have hstable : (prefixWord ++ tailWord_8259556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259556).length < 2 ^ (prefixWord ++ tailWord_8259556).sum := by decide
  have hdescent : baseEnd_8259556 < baseStart_8259556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259633 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 2, 6]
def baseStart_8259633 : Nat := 118140960795 + 8259633 * 2 ^ 59
def prefixEnd_8259633 : Nat := 4983230072969 + 3 ^ 40 * 8259633 * 2
def baseEnd_8259633 : Nat := 1413720586245862627200715

theorem tailTrace_8259633 : CollatzResearch.WordTrace tailWord_8259633 prefixEnd_8259633 1413720586245862627200715 := by
  unfold tailWord_8259633
  simp only [CollatzResearch.WordTrace]
  refine ⟨301253564485767748855279553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200835709657178499236853035 301253564485767748855279553)
  ·
    refine ⟨225940173364325811641459665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301253564485767748855279553 225940173364325811641459665)
    ·
      refine ⟨169455130023244358731094749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225940173364325811641459665 169455130023244358731094749)
      ·
        refine ⟨63545673758716634524160531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169455130023244358731094749 63545673758716634524160531)
        ·
          refine ⟨95318510638074951786240797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63545673758716634524160531 95318510638074951786240797)
          ·
            refine ⟨35744441489278106919840299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95318510638074951786240797 35744441489278106919840299)
            ·
              refine ⟨53616662233917160379760449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35744441489278106919840299 53616662233917160379760449)
              ·
                refine ⟨40212496675437870284820337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53616662233917160379760449 40212496675437870284820337)
                ·
                  refine ⟨30159372506578402713615253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40212496675437870284820337 30159372506578402713615253)
                  ·
                    refine ⟨1413720586245862627200715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30159372506578402713615253 1413720586245862627200715)
                    ·
                      rfl

theorem cell23_8259633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_8259633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259633 prefixEnd_8259633 := by exact prefixLift 8259633
  have htrace : WordTrace (prefixWord ++ tailWord_8259633) baseStart_8259633 baseEnd_8259633 := by
    simpa [prefixWord, tailWord_8259633, baseEnd_8259633] using wordTrace_append hprefix tailTrace_8259633
  have hstable : (prefixWord ++ tailWord_8259633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259633).length < 2 ^ (prefixWord ++ tailWord_8259633).sum := by decide
  have hdescent : baseEnd_8259633 < baseStart_8259633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259634 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_8259634 : Nat := 118140960795 + 8259634 * 2 ^ 59
def prefixEnd_8259634 : Nat := 4983230072969 + 3 ^ 40 * 8259634 * 2
def baseEnd_8259634 : Nat := 4241162272218242377689641

theorem tailTrace_8259634 : CollatzResearch.WordTrace tailWord_8259634 prefixEnd_8259634 4241162272218242377689641 := by
  unfold tailWord_8259634
  simp only [CollatzResearch.WordTrace]
  refine ⟨75313400239691031506516489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200835733972509417350710637 75313400239691031506516489)
  ·
    refine ⟨56485050179768273629887367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75313400239691031506516489 56485050179768273629887367)
    ·
      refine ⟨84727575269652410444831051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56485050179768273629887367 84727575269652410444831051)
      ·
        refine ⟨127091362904478615667246577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84727575269652410444831051 127091362904478615667246577)
        ·
          refine ⟨95318522178358961750434933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127091362904478615667246577 95318522178358961750434933)
          ·
            refine ⟨8936111454221152664103275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95318522178358961750434933 8936111454221152664103275)
            ·
              refine ⟨13404167181331728996154913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8936111454221152664103275 13404167181331728996154913)
              ·
                refine ⟨10053125385998796747116185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13404167181331728996154913 10053125385998796747116185)
                ·
                  refine ⟨7539844039499097560337139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10053125385998796747116185 7539844039499097560337139)
                  ·
                    refine ⟨11309766059248646340505709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7539844039499097560337139 11309766059248646340505709)
                    ·
                      refine ⟨4241162272218242377689641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11309766059248646340505709 4241162272218242377689641)
                      ·
                        rfl

theorem cell23_8259634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_8259634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259634 prefixEnd_8259634 := by exact prefixLift 8259634
  have htrace : WordTrace (prefixWord ++ tailWord_8259634) baseStart_8259634 baseEnd_8259634 := by
    simpa [prefixWord, tailWord_8259634, baseEnd_8259634] using wordTrace_append hprefix tailTrace_8259634
  have hstable : (prefixWord ++ tailWord_8259634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259634).length < 2 ^ (prefixWord ++ tailWord_8259634).sum := by decide
  have hdescent : baseEnd_8259634 < baseStart_8259634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259677 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_8259677 : Nat := 118140960795 + 8259677 * 2 ^ 59
def prefixEnd_8259677 : Nat := 4983230072969 + 3 ^ 40 * 8259677 * 2
def baseEnd_8259677 : Nat := 4241184351886385709451943

theorem tailTrace_8259677 : CollatzResearch.WordTrace tailWord_8259677 prefixEnd_8259677 4241184351886385709451943 := by
  unfold tailWord_8259677
  simp only [CollatzResearch.WordTrace]
  refine ⟨301255169297608344369881285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200836779531738896246587523 301255169297608344369881285)
  ·
    refine ⟨56485344243301564569352741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301255169297608344369881285 56485344243301564569352741)
    ·
      refine ⟨10591002045619043356753639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56485344243301564569352741 10591002045619043356753639)
      ·
        refine ⟨15886503068428565035130459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10591002045619043356753639 15886503068428565035130459)
        ·
          refine ⟨23829754602642847552695689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15886503068428565035130459 23829754602642847552695689)
          ·
            refine ⟨17872315951982135664521767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23829754602642847552695689 17872315951982135664521767)
            ·
              refine ⟨26808473927973203496782651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17872315951982135664521767 26808473927973203496782651)
              ·
                refine ⟨40212710891959805245173977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26808473927973203496782651 40212710891959805245173977)
                ·
                  refine ⟨30159533168969853933880483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40212710891959805245173977 30159533168969853933880483)
                  ·
                    refine ⟨45239299753454780900820725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30159533168969853933880483 45239299753454780900820725)
                    ·
                      refine ⟨4241184351886385709451943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45239299753454780900820725 4241184351886385709451943)
                      ·
                        rfl

theorem cell23_8259677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_8259677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259677 prefixEnd_8259677 := by exact prefixLift 8259677
  have htrace : WordTrace (prefixWord ++ tailWord_8259677) baseStart_8259677 baseEnd_8259677 := by
    simpa [prefixWord, tailWord_8259677, baseEnd_8259677] using wordTrace_append hprefix tailTrace_8259677
  have hstable : (prefixWord ++ tailWord_8259677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259677).length < 2 ^ (prefixWord ++ tailWord_8259677).sum := by decide
  have hdescent : baseEnd_8259677 < baseStart_8259677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259697 : List Nat := [1, 2, 2, 2, 1, 1, 7, 2, 5]
def baseStart_8259697 : Nat := 118140960795 + 8259697 * 2 ^ 59
def prefixEnd_8259697 : Nat := 4983230072969 + 3 ^ 40 * 8259697 * 2
def baseEnd_8259697 : Nat := 471243846833275070133539

theorem tailTrace_8259697 : CollatzResearch.WordTrace tailWord_8259697 prefixEnd_8259697 471243846833275070133539 := by
  unfold tailWord_8259697
  simp only [CollatzResearch.WordTrace]
  refine ⟨301255898757535887785609345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200837265838357258523739563 301255898757535887785609345)
  ·
    refine ⟨225941924068151915839207009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301255898757535887785609345 225941924068151915839207009)
    ·
      refine ⟨169456443051113936879405257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225941924068151915839207009 169456443051113936879405257)
      ·
        refine ⟨127092332288335452659553943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169456443051113936879405257 127092332288335452659553943)
        ·
          refine ⟨190638498432503178989330915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127092332288335452659553943 190638498432503178989330915)
          ·
            refine ⟨285957747648754768483996373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190638498432503178989330915 285957747648754768483996373)
            ·
              refine ⟨6702134710517689886343665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 285957747648754768483996373 6702134710517689886343665)
              ·
                refine ⟨5026601032888267414757749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6702134710517689886343665 5026601032888267414757749)
                ·
                  refine ⟨471243846833275070133539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5026601032888267414757749 471243846833275070133539)
                  ·
                    rfl

theorem cell23_8259697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 5].length) (baseStart_8259697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259697 prefixEnd_8259697 := by exact prefixLift 8259697
  have htrace : WordTrace (prefixWord ++ tailWord_8259697) baseStart_8259697 baseEnd_8259697 := by
    simpa [prefixWord, tailWord_8259697, baseEnd_8259697] using wordTrace_append hprefix tailTrace_8259697
  have hstable : (prefixWord ++ tailWord_8259697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259697).length < 2 ^ (prefixWord ++ tailWord_8259697).sum := by decide
  have hdescent : baseEnd_8259697 < baseStart_8259697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259703 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_8259703 : Nat := 118140960795 + 8259703 * 2 ^ 59
def prefixEnd_8259703 : Nat := 4983230072969 + 3 ^ 40 * 8259703 * 2
def baseEnd_8259703 : Nat := 4241197702383402607726823

theorem tailTrace_8259703 : CollatzResearch.WordTrace tailWord_8259703 prefixEnd_8259703 4241197702383402607726823 := by
  unfold tailWord_8259703
  simp only [CollatzResearch.WordTrace]
  refine ⟨301256117595514150810327763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200837411730342767206885175 301256117595514150810327763)
  ·
    refine ⟨451884176393271226215491645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301256117595514150810327763 451884176393271226215491645)
    ·
      refine ⟨169456566147476709830809367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451884176393271226215491645 169456566147476709830809367)
      ·
        refine ⟨254184849221215064746214051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169456566147476709830809367 254184849221215064746214051)
        ·
          refine ⟨381277273831822597119321077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254184849221215064746214051 381277273831822597119321077)
          ·
            refine ⟨35744744421733368479936351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 381277273831822597119321077 35744744421733368479936351)
            ·
              refine ⟨53617116632600052719904527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35744744421733368479936351 53617116632600052719904527)
              ·
                refine ⟨80425674948900079079856791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53617116632600052719904527 80425674948900079079856791)
                ·
                  refine ⟨120638512423350118619785187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80425674948900079079856791 120638512423350118619785187)
                  ·
                    refine ⟨180957768635025177929677781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120638512423350118619785187 180957768635025177929677781)
                    ·
                      refine ⟨4241197702383402607726823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180957768635025177929677781 4241197702383402607726823)
                      ·
                        rfl

theorem cell23_8259703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_8259703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259703 prefixEnd_8259703 := by exact prefixLift 8259703
  have htrace : WordTrace (prefixWord ++ tailWord_8259703) baseStart_8259703 baseEnd_8259703 := by
    simpa [prefixWord, tailWord_8259703, baseEnd_8259703] using wordTrace_append hprefix tailTrace_8259703
  have hstable : (prefixWord ++ tailWord_8259703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259703).length < 2 ^ (prefixWord ++ tailWord_8259703).sum := by decide
  have hdescent : baseEnd_8259703 < baseStart_8259703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259770 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 6]
def baseStart_8259770 : Nat := 118140960795 + 8259770 * 2 ^ 59
def prefixEnd_8259770 : Nat := 4983230072969 + 3 ^ 40 * 8259770 * 2
def baseEnd_8259770 : Nat := 471248011731917093954335

theorem tailTrace_8259770 : CollatzResearch.WordTrace tailWord_8259770 prefixEnd_8259770 471248011731917093954335 := by
  unfold tailWord_8259770
  simp only [CollatzResearch.WordTrace]
  refine ⟨75314640321567855313254191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200839040857514280835344509 75314640321567855313254191)
  ·
    refine ⟨112971960482351782969881287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75314640321567855313254191 112971960482351782969881287)
    ·
      refine ⟨169457940723527674454821931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112971960482351782969881287 169457940723527674454821931)
      ·
        refine ⟨254186911085291511682232897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169457940723527674454821931 254186911085291511682232897)
        ·
          refine ⟨190640183313968633761674673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254186911085291511682232897 190640183313968633761674673)
          ·
            refine ⟨142980137485476475321256005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190640183313968633761674673 142980137485476475321256005)
            ·
              refine ⟨26808775778526839122735501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142980137485476475321256005 26808775778526839122735501)
              ·
                refine ⟨10053290916947564671025813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26808775778526839122735501 10053290916947564671025813)
                ·
                  refine ⟨471248011731917093954335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10053290916947564671025813 471248011731917093954335)
                  ·
                    rfl

theorem cell23_8259770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_8259770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259770 prefixEnd_8259770 := by exact prefixLift 8259770
  have htrace : WordTrace (prefixWord ++ tailWord_8259770) baseStart_8259770 baseEnd_8259770 := by
    simpa [prefixWord, tailWord_8259770, baseEnd_8259770] using wordTrace_append hprefix tailTrace_8259770
  have hstable : (prefixWord ++ tailWord_8259770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259770).length < 2 ^ (prefixWord ++ tailWord_8259770).sum := by decide
  have hdescent : baseEnd_8259770 < baseStart_8259770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259774 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_8259774 : Nat := 118140960795 + 8259774 * 2 ^ 59
def prefixEnd_8259774 : Nat := 4983230072969 + 3 ^ 40 * 8259774 * 2
def baseEnd_8259774 : Nat := 1413744719836623943312999

theorem tailTrace_8259774 : CollatzResearch.WordTrace tailWord_8259774 prefixEnd_8259774 1413744719836623943312999 := by
  unfold tailWord_8259774
  simp only [CollatzResearch.WordTrace]
  refine ⟨37657338397282116242020297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200839138118837953290774917 37657338397282116242020297)
  ·
    refine ⟨28243003797961587181515223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37657338397282116242020297 28243003797961587181515223)
    ·
      refine ⟨42364505696942380772272835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28243003797961587181515223 42364505696942380772272835)
      ·
        refine ⟨63546758545413571158409253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42364505696942380772272835 63546758545413571158409253)
        ·
          refine ⟨11915017227265044592201735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63546758545413571158409253 11915017227265044592201735)
          ·
            refine ⟨17872525840897566888302603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915017227265044592201735 17872525840897566888302603)
            ·
              refine ⟨26808788761346350332453905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17872525840897566888302603 26808788761346350332453905)
              ·
                refine ⟨20106591571009762749340429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26808788761346350332453905 20106591571009762749340429)
                ·
                  refine ⟨7539971839128661031002661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20106591571009762749340429 7539971839128661031002661)
                  ·
                    refine ⟨1413744719836623943312999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7539971839128661031002661 1413744719836623943312999)
                    ·
                      rfl

theorem cell23_8259774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_8259774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259774 prefixEnd_8259774 := by exact prefixLift 8259774
  have htrace : WordTrace (prefixWord ++ tailWord_8259774) baseStart_8259774 baseEnd_8259774 := by
    simpa [prefixWord, tailWord_8259774, baseEnd_8259774] using wordTrace_append hprefix tailTrace_8259774
  have hstable : (prefixWord ++ tailWord_8259774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259774).length < 2 ^ (prefixWord ++ tailWord_8259774).sum := by decide
  have hdescent : baseEnd_8259774 < baseStart_8259774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259804 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 8]
def baseStart_8259804 : Nat := 118140960795 + 8259804 * 2 ^ 59
def prefixEnd_8259804 : Nat := 4983230072969 + 3 ^ 40 * 8259804 * 2
def baseEnd_8259804 : Nat := 471249951547722968062651

theorem tailTrace_8259804 : CollatzResearch.WordTrace tailWord_8259804 prefixEnd_8259804 471249951547722968062651 := by
  unfold tailWord_8259804
  simp only [CollatzResearch.WordTrace]
  refine ⟨150629900684074122529877233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200839867578765496706502977 150629900684074122529877233)
  ·
    refine ⟨112972425513055591897407925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150629900684074122529877233 112972425513055591897407925)
    ·
      refine ⟨10591164891848961740381993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112972425513055591897407925 10591164891848961740381993)
      ·
        refine ⟨7943373668886721305286495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10591164891848961740381993 7943373668886721305286495)
        ·
          refine ⟨11915060503330081957929743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7943373668886721305286495 11915060503330081957929743)
          ·
            refine ⟨17872590754995122936894615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915060503330081957929743 17872590754995122936894615)
            ·
              refine ⟨26808886132492684405341923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17872590754995122936894615 26808886132492684405341923)
              ·
                refine ⟨40213329198739026608012885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26808886132492684405341923 40213329198739026608012885)
                ·
                  refine ⟨471249951547722968062651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40213329198739026608012885 471249951547722968062651)
                  ·
                    rfl

theorem cell23_8259804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_8259804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259804 prefixEnd_8259804 := by exact prefixLift 8259804
  have htrace : WordTrace (prefixWord ++ tailWord_8259804) baseStart_8259804 baseEnd_8259804 := by
    simpa [prefixWord, tailWord_8259804, baseEnd_8259804] using wordTrace_append hprefix tailTrace_8259804
  have hstable : (prefixWord ++ tailWord_8259804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259804).length < 2 ^ (prefixWord ++ tailWord_8259804).sum := by decide
  have hdescent : baseEnd_8259804 < baseStart_8259804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259807 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 4, 3, 2]
def baseStart_8259807 : Nat := 118140960795 + 8259807 * 2 ^ 59
def prefixEnd_8259807 : Nat := 4983230072969 + 3 ^ 40 * 8259807 * 2
def baseEnd_8259807 : Nat := 4241251104371470200826345

theorem tailTrace_8259807 : CollatzResearch.WordTrace tailWord_8259807 prefixEnd_8259807 4241251104371470200826345 := by
  unfold tailWord_8259807
  simp only [CollatzResearch.WordTrace]
  refine ⟨301259910787137376572113675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200839940524758251048075783 301259910787137376572113675)
  ·
    refine ⟨451889866180706064858170513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301259910787137376572113675 451889866180706064858170513)
    ·
      refine ⟨338917399635529548643627885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451889866180706064858170513 338917399635529548643627885)
      ·
        refine ⟨127094024863323580741360457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338917399635529548643627885 127094024863323580741360457)
        ·
          refine ⟨95320518647492685556020343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127094024863323580741360457 95320518647492685556020343)
          ·
            refine ⟨142980777971239028334030515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95320518647492685556020343 142980777971239028334030515)
            ·
              refine ⟨214471166956858542501045773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142980777971239028334030515 214471166956858542501045773)
              ·
                refine ⟨80426687608821953437892165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214471166956858542501045773 80426687608821953437892165)
                ·
                  refine ⟨15080003926654116269604781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80426687608821953437892165 15080003926654116269604781)
                  ·
                    refine ⟨5655001472495293601101793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15080003926654116269604781 5655001472495293601101793)
                    ·
                      refine ⟨4241251104371470200826345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655001472495293601101793 4241251104371470200826345)
                      ·
                        rfl

theorem cell23_8259807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_8259807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259807 prefixEnd_8259807 := by exact prefixLift 8259807
  have htrace : WordTrace (prefixWord ++ tailWord_8259807) baseStart_8259807 baseEnd_8259807 := by
    simpa [prefixWord, tailWord_8259807, baseEnd_8259807] using wordTrace_append hprefix tailTrace_8259807
  have hstable : (prefixWord ++ tailWord_8259807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259807).length < 2 ^ (prefixWord ++ tailWord_8259807).sum := by decide
  have hdescent : baseEnd_8259807 < baseStart_8259807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259848 : List Nat := [2, 1, 3, 2, 3, 3, 1, 3, 1, 1, 3]
def baseStart_8259848 : Nat := 118140960795 + 8259848 * 2 ^ 59
def prefixEnd_8259848 : Nat := 4983230072969 + 3 ^ 40 * 8259848 * 2
def baseEnd_8259848 : Nat := 4241272157078304540413657

theorem tailTrace_8259848 : CollatzResearch.WordTrace tailWord_8259848 prefixEnd_8259848 4241272157078304540413657 := by
  unfold tailWord_8259848
  simp only [CollatzResearch.WordTrace]
  refine ⟨150630703089994420287178099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200840937453325893716237465 150630703089994420287178099)
  ·
    refine ⟨225946054634991630430767149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150630703089994420287178099 225946054634991630430767149)
    ·
      refine ⟨84729770488121861411537681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225946054634991630430767149 84729770488121861411537681)
      ·
        refine ⟨63547327866091396058653261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84729770488121861411537681 63547327866091396058653261)
        ·
          refine ⟨23830247949784273521994973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63547327866091396058653261 23830247949784273521994973)
          ·
            refine ⟨8936342981169102570748115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23830247949784273521994973 8936342981169102570748115)
            ·
              refine ⟨13404514471753653856122173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8936342981169102570748115 13404514471753653856122173)
              ·
                refine ⟨5026692926907620196045815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13404514471753653856122173 5026692926907620196045815)
                ·
                  refine ⟨7540039390361430294068723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5026692926907620196045815 7540039390361430294068723)
                  ·
                    refine ⟨11310059085542145441103085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7540039390361430294068723 11310059085542145441103085)
                    ·
                      refine ⟨4241272157078304540413657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11310059085542145441103085 4241272157078304540413657)
                      ·
                        rfl

theorem cell23_8259848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_8259848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259848 prefixEnd_8259848 := by exact prefixLift 8259848
  have htrace : WordTrace (prefixWord ++ tailWord_8259848) baseStart_8259848 baseEnd_8259848 := by
    simpa [prefixWord, tailWord_8259848, baseEnd_8259848] using wordTrace_append hprefix tailTrace_8259848
  have hstable : (prefixWord ++ tailWord_8259848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259848).length < 2 ^ (prefixWord ++ tailWord_8259848).sum := by decide
  have hdescent : baseEnd_8259848 < baseStart_8259848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259857 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 5]
def baseStart_8259857 : Nat := 118140960795 + 8259857 * 2 ^ 59
def prefixEnd_8259857 : Nat := 4983230072969 + 3 ^ 40 * 8259857 * 2
def baseEnd_8259857 : Nat := 4241276778404195005201115

theorem tailTrace_8259857 : CollatzResearch.WordTrace tailWord_8259857 prefixEnd_8259857 4241276778404195005201115 := by
  unfold tailWord_8259857
  simp only [CollatzResearch.WordTrace]
  refine ⟨301261734436956235111433825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200841156291304156740955883 301261734436956235111433825)
  ·
    refine ⟨225946300827717176333575369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301261734436956235111433825 225946300827717176333575369)
    ·
      refine ⟨169459725620787882250181527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225946300827717176333575369 169459725620787882250181527)
      ·
        refine ⟨254189588431181823375272291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169459725620787882250181527 254189588431181823375272291)
        ·
          refine ⟨381284382646772735062908437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254189588431181823375272291 381284382646772735062908437)
          ·
            refine ⟨17872705436567471956073833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 381284382646772735062908437 17872705436567471956073833)
            ·
              refine ⟨13404529077425603967055375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17872705436567471956073833 13404529077425603967055375)
              ·
                refine ⟨20106793616138405950583063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13404529077425603967055375 20106793616138405950583063)
                ·
                  refine ⟨30160190424207608925874595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20106793616138405950583063 30160190424207608925874595)
                  ·
                    refine ⟨45240285636311413388811893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30160190424207608925874595 45240285636311413388811893)
                    ·
                      refine ⟨4241276778404195005201115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45240285636311413388811893 4241276778404195005201115)
                      ·
                        rfl

theorem cell23_8259857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_8259857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259857 prefixEnd_8259857 := by exact prefixLift 8259857
  have htrace : WordTrace (prefixWord ++ tailWord_8259857) baseStart_8259857 baseEnd_8259857 := by
    simpa [prefixWord, tailWord_8259857, baseEnd_8259857] using wordTrace_append hprefix tailTrace_8259857
  have hstable : (prefixWord ++ tailWord_8259857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259857).length < 2 ^ (prefixWord ++ tailWord_8259857).sum := by decide
  have hdescent : baseEnd_8259857 < baseStart_8259857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259871 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 3, 2, 2]
def baseStart_8259871 : Nat := 118140960795 + 8259871 * 2 ^ 59
def prefixEnd_8259871 : Nat := 4983230072969 + 3 ^ 40 * 8259871 * 2
def baseEnd_8259871 : Nat := 4241283967133357950426051

theorem tailTrace_8259871 : CollatzResearch.WordTrace tailWord_8259871 prefixEnd_8259871 4241283967133357950426051 := by
  unfold tailWord_8259871
  simp only [CollatzResearch.WordTrace]
  refine ⟨301262245058905515502443467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200841496705937010334962311 301262245058905515502443467)
  ·
    refine ⟨451893367588358273253665201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301262245058905515502443467 451893367588358273253665201)
    ·
      refine ⟨338920025691268704940248901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451893367588358273253665201 338920025691268704940248901)
      ·
        refine ⟨63547504817112882176296669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338920025691268704940248901 63547504817112882176296669)
        ·
          refine ⟨23830314306417330816111251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63547504817112882176296669 23830314306417330816111251)
          ·
            refine ⟨35745471459625996224166877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23830314306417330816111251 35745471459625996224166877)
            ·
              refine ⟨13404551797359748584062579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35745471459625996224166877 13404551797359748584062579)
              ·
                refine ⟨20106827696039622876093869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13404551797359748584062579 20106827696039622876093869)
                ·
                  refine ⟨7540060386014858578535201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20106827696039622876093869 7540060386014858578535201)
                  ·
                    refine ⟨5655045289511143933901401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7540060386014858578535201 5655045289511143933901401)
                    ·
                      refine ⟨4241283967133357950426051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655045289511143933901401 4241283967133357950426051)
                      ·
                        rfl

theorem cell23_8259871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_8259871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259871 prefixEnd_8259871 := by exact prefixLift 8259871
  have htrace : WordTrace (prefixWord ++ tailWord_8259871) baseStart_8259871 baseEnd_8259871 := by
    simpa [prefixWord, tailWord_8259871, baseEnd_8259871] using wordTrace_append hprefix tailTrace_8259871
  have hstable : (prefixWord ++ tailWord_8259871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259871).length < 2 ^ (prefixWord ++ tailWord_8259871).sum := by decide
  have hdescent : baseEnd_8259871 < baseStart_8259871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259877 : List Nat := [1, 3, 1, 2, 5, 1, 2, 8]
def baseStart_8259877 : Nat := 118140960795 + 8259877 * 2 ^ 59
def prefixEnd_8259877 : Nat := 4983230072969 + 3 ^ 40 * 8259877 * 2
def baseEnd_8259877 : Nat := 157084705482121663961149

theorem tailTrace_8259877 : CollatzResearch.WordTrace tailWord_8259877 prefixEnd_8259877 157084705482121663961149 := by
  unfold tailWord_8259877
  simp only [CollatzResearch.WordTrace]
  refine ⟨301262463896883778527161885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200841642597922519018107923 301262463896883778527161885)
  ·
    refine ⟨112973423961331416947685707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301262463896883778527161885 112973423961331416947685707)
    ·
      refine ⟨169460135941997125421528561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112973423961331416947685707 169460135941997125421528561)
      ·
        refine ⟨127095101956497844066146421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169460135941997125421528561 127095101956497844066146421)
        ·
          refine ⟨11915165808421672881201227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127095101956497844066146421 11915165808421672881201227)
          ·
            refine ⟨17872748712632509321801841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915165808421672881201227 17872748712632509321801841)
            ·
              refine ⟨13404561534474381991351381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17872748712632509321801841 13404561534474381991351381)
              ·
                refine ⟨157084705482121663961149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13404561534474381991351381 157084705482121663961149)
                ·
                  rfl

theorem cell23_8259877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 8].length) (baseStart_8259877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259877 prefixEnd_8259877 := by exact prefixLift 8259877
  have htrace : WordTrace (prefixWord ++ tailWord_8259877) baseStart_8259877 baseEnd_8259877 := by
    simpa [prefixWord, tailWord_8259877, baseEnd_8259877] using wordTrace_append hprefix tailTrace_8259877
  have hstable : (prefixWord ++ tailWord_8259877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259877).length < 2 ^ (prefixWord ++ tailWord_8259877).sum := by decide
  have hdescent : baseEnd_8259877 < baseStart_8259877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259908 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_8259908 : Nat := 118140960795 + 8259908 * 2 ^ 59
def prefixEnd_8259908 : Nat := 4983230072969 + 3 ^ 40 * 8259908 * 2
def baseEnd_8259908 : Nat := 4241302965917574305663381

theorem tailTrace_8259908 : CollatzResearch.WordTrace tailWord_8259908 prefixEnd_8259908 4241302965917574305663381 := by
  unfold tailWord_8259908
  simp only [CollatzResearch.WordTrace]
  refine ⟨150631797279885735410770189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200842396373180980547693585 150631797279885735410770189)
  ·
    refine ⟨56486923979957150779038821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150631797279885735410770189 56486923979957150779038821)
    ·
      refine ⟨10591298246241965771069779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56486923979957150779038821 10591298246241965771069779)
      ·
        refine ⟨15886947369362948656604669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10591298246241965771069779 15886947369362948656604669)
        ·
          refine ⟨5957605263511105746226751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15886947369362948656604669 5957605263511105746226751)
          ·
            refine ⟨8936407895266658619340127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957605263511105746226751 8936407895266658619340127)
            ·
              refine ⟨13404611842899987929010191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8936407895266658619340127 13404611842899987929010191)
              ·
                refine ⟨20106917764349981893515287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13404611842899987929010191 20106917764349981893515287)
                ·
                  refine ⟨30160376646524972840272931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20106917764349981893515287 30160376646524972840272931)
                  ·
                    refine ⟨45240564969787459260409397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30160376646524972840272931 45240564969787459260409397)
                    ·
                      refine ⟨4241302965917574305663381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45240564969787459260409397 4241302965917574305663381)
                      ·
                        rfl

theorem cell23_8259908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_8259908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259908 prefixEnd_8259908 := by exact prefixLift 8259908
  have htrace : WordTrace (prefixWord ++ tailWord_8259908) baseStart_8259908 baseEnd_8259908 := by
    simpa [prefixWord, tailWord_8259908, baseEnd_8259908] using wordTrace_append hprefix tailTrace_8259908
  have hstable : (prefixWord ++ tailWord_8259908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259908).length < 2 ^ (prefixWord ++ tailWord_8259908).sum := by decide
  have hdescent : baseEnd_8259908 < baseStart_8259908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259921 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 2, 1, 3]
def baseStart_8259921 : Nat := 118140960795 + 8259921 * 2 ^ 59
def prefixEnd_8259921 : Nat := 4983230072969 + 3 ^ 40 * 8259921 * 2
def baseEnd_8259921 : Nat := 4241309641166082754800821

theorem tailTrace_8259921 : CollatzResearch.WordTrace tailWord_8259921 prefixEnd_8259921 4241309641166082754800821 := by
  unfold tailWord_8259921
  simp only [CollatzResearch.WordTrace]
  refine ⟨301264068708724374041763617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200842712472482916027842411 301264068708724374041763617)
  ·
    refine ⟨225948051531543280531322713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301264068708724374041763617 225948051531543280531322713)
    ·
      refine ⟨169461038648657460398492035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225948051531543280531322713 169461038648657460398492035)
      ·
        refine ⟨254191557972986190597738053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169461038648657460398492035 254191557972986190597738053)
        ·
          refine ⟨47660917119934910737075885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254191557972986190597738053 47660917119934910737075885)
          ·
            refine ⟨17872843919975591526403457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47660917119934910737075885 17872843919975591526403457)
            ·
              refine ⟨13404632939981693644802593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17872843919975591526403457 13404632939981693644802593)
              ·
                refine ⟨10053474704986270233601945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13404632939981693644802593 10053474704986270233601945)
                ·
                  refine ⟨7540106028739702675201459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10053474704986270233601945 7540106028739702675201459)
                  ·
                    refine ⟨11310159043109554012802189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7540106028739702675201459 11310159043109554012802189)
                    ·
                      refine ⟨4241309641166082754800821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11310159043109554012802189 4241309641166082754800821)
                      ·
                        rfl

theorem cell23_8259921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_8259921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259921 prefixEnd_8259921 := by exact prefixLift 8259921
  have htrace : WordTrace (prefixWord ++ tailWord_8259921) baseStart_8259921 baseEnd_8259921 := by
    simpa [prefixWord, tailWord_8259921, baseEnd_8259921] using wordTrace_append hprefix tailTrace_8259921
  have hstable : (prefixWord ++ tailWord_8259921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259921).length < 2 ^ (prefixWord ++ tailWord_8259921).sum := by decide
  have hdescent : baseEnd_8259921 < baseStart_8259921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8259994 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3]
def baseStart_8259994 : Nat := 118140960795 + 8259994 * 2 ^ 59
def prefixEnd_8259994 : Nat := 4983230072969 + 3 ^ 40 * 8259994 * 2
def baseEnd_8259994 : Nat := 4241347125253860969187985

theorem tailTrace_8259994 : CollatzResearch.WordTrace tailWord_8259994 prefixEnd_8259994 4241347125253860969187985 := by
  unfold tailWord_8259994
  simp only [CollatzResearch.WordTrace]
  refine ⟨75316682809364976877292759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200844487491639938339447357 75316682809364976877292759)
  ·
    refine ⟨112975024214047465315939139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75316682809364976877292759 112975024214047465315939139)
    ·
      refine ⟨169462536321071197973908709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112975024214047465315939139 169462536321071197973908709)
      ·
        refine ⟨31774225560200849620107883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169462536321071197973908709 31774225560200849620107883)
        ·
          refine ⟨47661338340301274430161825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31774225560200849620107883 47661338340301274430161825)
          ·
            refine ⟨35746003755225955822621369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47661338340301274430161825 35746003755225955822621369)
            ·
              refine ⟨26809502816419466866966027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35746003755225955822621369 26809502816419466866966027)
              ·
                refine ⟨40214254224629200300449041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26809502816419466866966027 40214254224629200300449041)
                ·
                  refine ⟨30160690668471900225336781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40214254224629200300449041 30160690668471900225336781)
                  ·
                    refine ⟨11310259000676962584501293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30160690668471900225336781 11310259000676962584501293)
                    ·
                      refine ⟨4241347125253860969187985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11310259000676962584501293 4241347125253860969187985)
                      ·
                        rfl

theorem cell23_8259994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_8259994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8259994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8259994 prefixEnd_8259994 := by exact prefixLift 8259994
  have htrace : WordTrace (prefixWord ++ tailWord_8259994) baseStart_8259994 baseEnd_8259994 := by
    simpa [prefixWord, tailWord_8259994, baseEnd_8259994] using wordTrace_append hprefix tailTrace_8259994
  have hstable : (prefixWord ++ tailWord_8259994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8259994).length < 2 ^ (prefixWord ++ tailWord_8259994).sum := by decide
  have hdescent : baseEnd_8259994 < baseStart_8259994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8259994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260004 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 2, 5, 2]
def baseStart_8260004 : Nat := 118140960795 + 8260004 * 2 ^ 59
def prefixEnd_8260004 : Nat := 4983230072969 + 3 ^ 40 * 8260004 * 2
def baseEnd_8260004 : Nat := 4241352260060405930062939

theorem tailTrace_8260004 : CollatzResearch.WordTrace tailWord_8260004 prefixEnd_8260004 4241352260060405930062939 := by
  unfold tailWord_8260004
  simp only [CollatzResearch.WordTrace]
  refine ⟨150633547983711839608517533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200844730644949119478023377 150633547983711839608517533)
  ·
    refine ⟨56487580493891939853194075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150633547983711839608517533 56487580493891939853194075)
    ·
      refine ⟨84731370740837909779791113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56487580493891939853194075 84731370740837909779791113)
      ·
        refine ⟨63548528055628432334843335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84731370740837909779791113 63548528055628432334843335)
        ·
          refine ⟨95322792083442648502265003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63548528055628432334843335 95322792083442648502265003)
          ·
            refine ⟨142984188125163972753397505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95322792083442648502265003 142984188125163972753397505)
            ·
              refine ⟨107238141093872979565048129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142984188125163972753397505 107238141093872979565048129)
              ·
                refine ⟨80428605820404734673786097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107238141093872979565048129 80428605820404734673786097)
                ·
                  refine ⟨60321454365303551005339573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80428605820404734673786097 60321454365303551005339573)
                  ·
                    refine ⟨5655136346747207906750585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60321454365303551005339573 5655136346747207906750585)
                    ·
                      refine ⟨4241352260060405930062939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655136346747207906750585 4241352260060405930062939)
                      ·
                        rfl

theorem cell23_8260004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_8260004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260004 prefixEnd_8260004 := by exact prefixLift 8260004
  have htrace : WordTrace (prefixWord ++ tailWord_8260004) baseStart_8260004 baseEnd_8260004 := by
    simpa [prefixWord, tailWord_8260004, baseEnd_8260004] using wordTrace_append hprefix tailTrace_8260004
  have hstable : (prefixWord ++ tailWord_8260004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260004).length < 2 ^ (prefixWord ++ tailWord_8260004).sum := by decide
  have hdescent : baseEnd_8260004 < baseStart_8260004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260037 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 2, 8, 3]
def baseStart_8260037 : Nat := 118140960795 + 8260037 * 2 ^ 59
def prefixEnd_8260037 : Nat := 4983230072969 + 3 ^ 40 * 8260037 * 2
def baseEnd_8260037 : Nat := 4241369204922004300950287

theorem tailTrace_8260037 : CollatzResearch.WordTrace tailWord_8260037 prefixEnd_8260037 4241369204922004300950287 := by
  unfold tailWord_8260037
  simp only [CollatzResearch.WordTrace]
  refine ⟨301268299576304125852986365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200845533050869417235324243 301268299576304125852986365)
  ·
    refine ⟨112975612341114047194869887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301268299576304125852986365 112975612341114047194869887)
    ·
      refine ⟨169463418511671070792304831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112975612341114047194869887 169463418511671070792304831)
      ·
        refine ⟨254195127767506606188457247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169463418511671070792304831 254195127767506606188457247)
        ·
          refine ⟨381292691651259909282685871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254195127767506606188457247 381292691651259909282685871)
          ·
            refine ⟨571939037476889863924028807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381292691651259909282685871 571939037476889863924028807)
            ·
              refine ⟨857908556215334795886043211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571939037476889863924028807 857908556215334795886043211)
              ·
                refine ⟨1286862834323002193829064817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857908556215334795886043211 1286862834323002193829064817)
                ·
                  refine ⟨965147125742251645371798613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286862834323002193829064817 965147125742251645371798613)
                  ·
                    refine ⟨11310317879792011469200765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 965147125742251645371798613 11310317879792011469200765)
                    ·
                      refine ⟨4241369204922004300950287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11310317879792011469200765 4241369204922004300950287)
                      ·
                        rfl

theorem cell23_8260037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_8260037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260037 prefixEnd_8260037 := by exact prefixLift 8260037
  have htrace : WordTrace (prefixWord ++ tailWord_8260037) baseStart_8260037 baseEnd_8260037 := by
    simpa [prefixWord, tailWord_8260037, baseEnd_8260037] using wordTrace_append hprefix tailTrace_8260037
  have hstable : (prefixWord ++ tailWord_8260037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260037).length < 2 ^ (prefixWord ++ tailWord_8260037).sum := by decide
  have hdescent : baseEnd_8260037 < baseStart_8260037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260071 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_8260071 : Nat := 118140960795 + 8260071 * 2 ^ 59
def prefixEnd_8260071 : Nat := 4983230072969 + 3 ^ 40 * 8260071 * 2
def baseEnd_8260071 : Nat := 4241386663264257167925131

theorem tailTrace_8260071 : CollatzResearch.WordTrace tailWord_8260071 prefixEnd_8260071 4241386663264257167925131 := by
  unfold tailWord_8260071
  simp only [CollatzResearch.WordTrace]
  refine ⟨301269539658180949659724067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200846359772120633106482711 301269539658180949659724067)
  ·
    refine ⟨451904309487271424489586101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301269539658180949659724067 451904309487271424489586101)
    ·
      refine ⟨42366029014431696045898697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 451904309487271424489586101 42366029014431696045898697)
      ·
        refine ⟨31774521760823772034424023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42366029014431696045898697 31774521760823772034424023)
        ·
          refine ⟨47661782641235658051636035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31774521760823772034424023 47661782641235658051636035)
          ·
            refine ⟨71492673961853487077454053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47661782641235658051636035 71492673961853487077454053)
            ·
              refine ⟨13404876367847528827022635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71492673961853487077454053 13404876367847528827022635)
              ·
                refine ⟨20107314551771293240533953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13404876367847528827022635 20107314551771293240533953)
                ·
                  refine ⟨15080485913828469930400465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20107314551771293240533953 15080485913828469930400465)
                  ·
                    refine ⟨11310364435371352447800349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15080485913828469930400465 11310364435371352447800349)
                    ·
                      refine ⟨4241386663264257167925131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11310364435371352447800349 4241386663264257167925131)
                      ·
                        rfl

theorem cell23_8260071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_8260071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260071 prefixEnd_8260071 := by exact prefixLift 8260071
  have htrace : WordTrace (prefixWord ++ tailWord_8260071) baseStart_8260071 baseEnd_8260071 := by
    simpa [prefixWord, tailWord_8260071, baseEnd_8260071] using wordTrace_append hprefix tailTrace_8260071
  have hstable : (prefixWord ++ tailWord_8260071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260071).length < 2 ^ (prefixWord ++ tailWord_8260071).sum := by decide
  have hdescent : baseEnd_8260071 < baseStart_8260071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260102 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_8260102 : Nat := 118140960795 + 8260102 * 2 ^ 59
def prefixEnd_8260102 : Nat := 4983230072969 + 3 ^ 40 * 8260102 * 2
def baseEnd_8260102 : Nat := 4241402581164546546637489

theorem tailTrace_8260102 : CollatzResearch.WordTrace tailWord_8260102 prefixEnd_8260102 4241402581164546546637489 := by
  unfold tailWord_8260102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9414708447533395061065705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 200847113547379094636068373 9414708447533395061065705)
  ·
    refine ⟨7061031335650046295799279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9414708447533395061065705 7061031335650046295799279)
    ·
      refine ⟨10591547003475069443698919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7061031335650046295799279 10591547003475069443698919)
      ·
        refine ⟨15887320505212604165548379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10591547003475069443698919 15887320505212604165548379)
        ·
          refine ⟨23830980757818906248322569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15887320505212604165548379 23830980757818906248322569)
          ·
            refine ⟨17873235568364179686241927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23830980757818906248322569 17873235568364179686241927)
            ·
              refine ⟨26809853352546269529362891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17873235568364179686241927 26809853352546269529362891)
              ·
                refine ⟨40214780028819404294044337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26809853352546269529362891 40214780028819404294044337)
                ·
                  refine ⟨30161085021614553220533253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40214780028819404294044337 30161085021614553220533253)
                  ·
                    refine ⟨5655203441552728728849985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30161085021614553220533253 5655203441552728728849985)
                    ·
                      refine ⟨4241402581164546546637489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655203441552728728849985 4241402581164546546637489)
                      ·
                        rfl

theorem cell23_8260102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_8260102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260102 prefixEnd_8260102 := by exact prefixLift 8260102
  have htrace : WordTrace (prefixWord ++ tailWord_8260102) baseStart_8260102 baseEnd_8260102 := by
    simpa [prefixWord, tailWord_8260102, baseEnd_8260102] using wordTrace_append hprefix tailTrace_8260102
  have hstable : (prefixWord ++ tailWord_8260102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260102).length < 2 ^ (prefixWord ++ tailWord_8260102).sum := by decide
  have hdescent : baseEnd_8260102 < baseStart_8260102 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260128 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 1, 5, 2]
def baseStart_8260128 : Nat := 118140960795 + 8260128 * 2 ^ 59
def prefixEnd_8260128 : Nat := 4983230072969 + 3 ^ 40 * 8260128 * 2
def baseEnd_8260128 : Nat := 4241415931661563444912369

theorem tailTrace_8260128 : CollatzResearch.WordTrace tailWord_8260128 prefixEnd_8260128 4241415931661563444912369 := by
  unfold tailWord_8260128
  simp only [CollatzResearch.WordTrace]
  refine ⟨150635809309487224197274519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200847745745982965596366025 150635809309487224197274519)
  ·
    refine ⟨225953713964230836295911779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150635809309487224197274519 225953713964230836295911779)
    ·
      refine ⟨338930570946346254443867669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225953713964230836295911779 338930570946346254443867669)
      ·
        refine ⟨15887370513109980677056297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 338930570946346254443867669 15887370513109980677056297)
        ·
          refine ⟨11915527884832485507792223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15887370513109980677056297 11915527884832485507792223)
          ·
            refine ⟨17873291827248728261688335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915527884832485507792223 17873291827248728261688335)
            ·
              refine ⟨26809937740873092392532503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17873291827248728261688335 26809937740873092392532503)
              ·
                refine ⟨40214906611309638588798755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26809937740873092392532503 40214906611309638588798755)
                ·
                  refine ⟨60322359916964457883198133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40214906611309638588798755 60322359916964457883198133)
                  ·
                    refine ⟨5655221242215417926549825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60322359916964457883198133 5655221242215417926549825)
                    ·
                      refine ⟨4241415931661563444912369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655221242215417926549825 4241415931661563444912369)
                      ·
                        rfl

theorem cell23_8260128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_8260128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260128 prefixEnd_8260128 := by exact prefixLift 8260128
  have htrace : WordTrace (prefixWord ++ tailWord_8260128) baseStart_8260128 baseEnd_8260128 := by
    simpa [prefixWord, tailWord_8260128, baseEnd_8260128] using wordTrace_append hprefix tailTrace_8260128
  have hstable : (prefixWord ++ tailWord_8260128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260128).length < 2 ^ (prefixWord ++ tailWord_8260128).sum := by decide
  have hdescent : baseEnd_8260128 < baseStart_8260128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260138 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 1, 5]
def baseStart_8260138 : Nat := 118140960795 + 8260138 * 2 ^ 59
def prefixEnd_8260138 : Nat := 4983230072969 + 3 ^ 40 * 8260138 * 2
def baseEnd_8260138 : Nat := 1413807022156036135262441

theorem tailTrace_8260138 : CollatzResearch.WordTrace tailWord_8260138 prefixEnd_8260138 1413807022156036135262441 := by
  unfold tailWord_8260138
  simp only [CollatzResearch.WordTrace]
  refine ⟨75317995837234555025603267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200847988899292146734942045 75317995837234555025603267)
  ·
    refine ⟨112976993755851832538404901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75317995837234555025603267 112976993755851832538404901)
    ·
      refine ⟨21183186329222218600950919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112976993755851832538404901 21183186329222218600950919)
      ·
        refine ⟨31774779493833327901426379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21183186329222218600950919 31774779493833327901426379)
        ·
          refine ⟨47662169240749991852139569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31774779493833327901426379 47662169240749991852139569)
          ·
            refine ⟨35746626930562493889104677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47662169240749991852139569 35746626930562493889104677)
            ·
              refine ⟨6702492549480467604207127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35746626930562493889104677 6702492549480467604207127)
              ·
                refine ⟨10053738824220701406310691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6702492549480467604207127 10053738824220701406310691)
                ·
                  refine ⟨15080608236331052109466037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10053738824220701406310691 15080608236331052109466037)
                  ·
                    refine ⟨1413807022156036135262441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15080608236331052109466037 1413807022156036135262441)
                    ·
                      rfl

theorem cell23_8260138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_8260138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260138 prefixEnd_8260138 := by exact prefixLift 8260138
  have htrace : WordTrace (prefixWord ++ tailWord_8260138) baseStart_8260138 baseEnd_8260138 := by
    simpa [prefixWord, tailWord_8260138, baseEnd_8260138] using wordTrace_append hprefix tailTrace_8260138
  have hstable : (prefixWord ++ tailWord_8260138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260138).length < 2 ^ (prefixWord ++ tailWord_8260138).sum := by decide
  have hdescent : baseEnd_8260138 < baseStart_8260138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260147 : List Nat := [1, 1, 1, 2, 4, 2, 12]
def baseStart_8260147 : Nat := 118140960795 + 8260147 * 2 ^ 59
def prefixEnd_8260147 : Nat := 4983230072969 + 3 ^ 40 * 8260147 * 2
def baseEnd_8260147 : Nat := 52363280096222208278701

theorem tailTrace_8260147 : CollatzResearch.WordTrace tailWord_8260147 prefixEnd_8260147 52363280096222208278701 := by
  unfold tailWord_8260147
  simp only [CollatzResearch.WordTrace]
  refine ⟨301272311605905614639490695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200848207737270409759660463 301272311605905614639490695)
  ·
    refine ⟨451908467408858421959236043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301272311605905614639490695 451908467408858421959236043)
    ·
      refine ⟨677862701113287632938854065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451908467408858421959236043 677862701113287632938854065)
      ·
        refine ⟨508397025834965724704140549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677862701113287632938854065 508397025834965724704140549)
        ·
          refine ⟨95324442344056073382026353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508397025834965724704140549 95324442344056073382026353)
          ·
            refine ⟨71493331758042055036519765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95324442344056073382026353 71493331758042055036519765)
            ·
              refine ⟨52363280096222208278701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 71493331758042055036519765 52363280096222208278701)
              ·
                rfl

theorem cell23_8260147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 12].length) (baseStart_8260147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260147 prefixEnd_8260147 := by exact prefixLift 8260147
  have htrace : WordTrace (prefixWord ++ tailWord_8260147) baseStart_8260147 baseEnd_8260147 := by
    simpa [prefixWord, tailWord_8260147, baseEnd_8260147] using wordTrace_append hprefix tailTrace_8260147
  have hstable : (prefixWord ++ tailWord_8260147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260147).length < 2 ^ (prefixWord ++ tailWord_8260147).sum := by decide
  have hdescent : baseEnd_8260147 < baseStart_8260147 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260161 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_8260161 : Nat := 118140960795 + 8260161 * 2 ^ 59
def prefixEnd_8260161 : Nat := 4983230072969 + 3 ^ 40 * 8260161 * 2
def baseEnd_8260161 : Nat := 4241432876523161815799717

theorem tailTrace_8260161 : CollatzResearch.WordTrace tailWord_8260161 prefixEnd_8260161 4241432876523161815799717 := by
  unfold tailWord_8260161
  simp only [CollatzResearch.WordTrace]
  refine ⟨301272822227854895030500337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200848548151903263353666891 301272822227854895030500337)
  ·
    refine ⟨225954616670891171272875253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301272822227854895030500337 225954616670891171272875253)
    ·
      refine ⟨21183245312896047306832055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225954616670891171272875253 21183245312896047306832055)
      ·
        refine ⟨31774867969344070960248083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21183245312896047306832055 31774867969344070960248083)
        ·
          refine ⟨47662301954016106440372125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31774867969344070960248083 47662301954016106440372125)
          ·
            refine ⟨17873363232756039915139547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47662301954016106440372125 17873363232756039915139547)
            ·
              refine ⟨26810044849134059872709321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17873363232756039915139547 26810044849134059872709321)
              ·
                refine ⟨20107533636850544904531991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26810044849134059872709321 20107533636850544904531991)
                ·
                  refine ⟨30161300455275817356797987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20107533636850544904531991 30161300455275817356797987)
                  ·
                    refine ⟨45241950682913726035196981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30161300455275817356797987 45241950682913726035196981)
                    ·
                      refine ⟨4241432876523161815799717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45241950682913726035196981 4241432876523161815799717)
                      ·
                        rfl

theorem cell23_8260161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_8260161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260161 prefixEnd_8260161 := by exact prefixLift 8260161
  have htrace : WordTrace (prefixWord ++ tailWord_8260161) baseStart_8260161 baseEnd_8260161 := by
    simpa [prefixWord, tailWord_8260161, baseEnd_8260161] using wordTrace_append hprefix tailTrace_8260161
  have hstable : (prefixWord ++ tailWord_8260161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260161).length < 2 ^ (prefixWord ++ tailWord_8260161).sum := by decide
  have hdescent : baseEnd_8260161 < baseStart_8260161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260178 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_8260178 : Nat := 118140960795 + 8260178 * 2 ^ 59
def prefixEnd_8260178 : Nat := 4983230072969 + 3 ^ 40 * 8260178 * 2
def baseEnd_8260178 : Nat := 4241441605694288249287139

theorem tailTrace_8260178 : CollatzResearch.WordTrace tailWord_8260178 prefixEnd_8260178 4241441605694288249287139 := by
  unfold tailWord_8260178
  simp only [CollatzResearch.WordTrace]
  refine ⟨75318360567198326733467297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200848961512528871289246125 75318360567198326733467297)
  ·
    refine ⟨56488770425398745050100473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75318360567198326733467297 56488770425398745050100473)
    ·
      refine ⟨42366577819049058787575355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56488770425398745050100473 42366577819049058787575355)
      ·
        refine ⟨63549866728573588181363033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42366577819049058787575355 63549866728573588181363033)
        ·
          refine ⟨47662400046430191136022275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63549866728573588181363033 47662400046430191136022275)
          ·
            refine ⟨71493600069645286704033413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47662400046430191136022275 71493600069645286704033413)
            ·
              refine ⟨13405050013058491257006265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71493600069645286704033413 13405050013058491257006265)
              ·
                refine ⟨10053787509793868442754699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13405050013058491257006265 10053787509793868442754699)
                ·
                  refine ⟨15080681264690802664132049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10053787509793868442754699 15080681264690802664132049)
                  ·
                    refine ⟨11310510948518101998099037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15080681264690802664132049 11310510948518101998099037)
                    ·
                      refine ⟨4241441605694288249287139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11310510948518101998099037 4241441605694288249287139)
                      ·
                        rfl

theorem cell23_8260178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_8260178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260178 prefixEnd_8260178 := by exact prefixLift 8260178
  have htrace : WordTrace (prefixWord ++ tailWord_8260178) baseStart_8260178 baseEnd_8260178 := by
    simpa [prefixWord, tailWord_8260178, baseEnd_8260178] using wordTrace_append hprefix tailTrace_8260178
  have hstable : (prefixWord ++ tailWord_8260178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260178).length < 2 ^ (prefixWord ++ tailWord_8260178).sum := by decide
  have hdescent : baseEnd_8260178 < baseStart_8260178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260201 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 5, 3, 2]
def baseStart_8260201 : Nat := 118140960795 + 8260201 * 2 ^ 59
def prefixEnd_8260201 : Nat := 4983230072969 + 3 ^ 40 * 8260201 * 2
def baseEnd_8260201 : Nat := 4241453415749341659299533

theorem tailTrace_8260201 : CollatzResearch.WordTrace tailWord_8260201 prefixEnd_8260201 4241453415749341659299533 := by
  unfold tailWord_8260201
  simp only [CollatzResearch.WordTrace]
  refine ⟨301274281147709981861956457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200849520765139987907970971 301274281147709981861956457)
  ·
    refine ⟨225955710860782486396467343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301274281147709981861956457 225955710860782486396467343)
    ·
      refine ⟨338933566291173729594701015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225955710860782486396467343 338933566291173729594701015)
      ·
        refine ⟨508400349436760594392051523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338933566291173729594701015 508400349436760594392051523)
        ·
          refine ⟨762600524155140891588077285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508400349436760594392051523 762600524155140891588077285)
          ·
            refine ⟨142987598279088917172764491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 762600524155140891588077285 142987598279088917172764491)
            ·
              refine ⟨214481397418633375759146737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142987598279088917172764491 214481397418633375759146737)
              ·
                refine ⟨160861048063975031819360053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214481397418633375759146737 160861048063975031819360053)
                ·
                  refine ⟨15080723255997659233065005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160861048063975031819360053 15080723255997659233065005)
                  ·
                    refine ⟨5655271220999122212399377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15080723255997659233065005 5655271220999122212399377)
                    ·
                      refine ⟨4241453415749341659299533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655271220999122212399377 4241453415749341659299533)
                      ·
                        rfl

theorem cell23_8260201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 3, 2].length) (baseStart_8260201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260201 prefixEnd_8260201 := by exact prefixLift 8260201
  have htrace : WordTrace (prefixWord ++ tailWord_8260201) baseStart_8260201 baseEnd_8260201 := by
    simpa [prefixWord, tailWord_8260201, baseEnd_8260201] using wordTrace_append hprefix tailTrace_8260201
  have hstable : (prefixWord ++ tailWord_8260201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260201).length < 2 ^ (prefixWord ++ tailWord_8260201).sum := by decide
  have hdescent : baseEnd_8260201 < baseStart_8260201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260226 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_8260226 : Nat := 118140960795 + 8260226 * 2 ^ 59
def prefixEnd_8260226 : Nat := 4983230072969 + 3 ^ 40 * 8260226 * 2
def baseEnd_8260226 : Nat := 4241466252765704061486919

theorem tailTrace_8260226 : CollatzResearch.WordTrace tailWord_8260226 prefixEnd_8260226 4241466252765704061486919 := by
  unfold tailWord_8260226
  simp only [CollatzResearch.WordTrace]
  refine ⟨75318798243154852782904133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200850128648412940754411021 75318798243154852782904133)
  ·
    refine ⟨14122274670591534896794525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75318798243154852782904133 14122274670591534896794525)
    ·
      refine ⟨5295853001471825586297947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14122274670591534896794525 5295853001471825586297947)
      ·
        refine ⟨7943779502207738379446921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295853001471825586297947 7943779502207738379446921)
        ·
          refine ⟨5957834626655803784585191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7943779502207738379446921 5957834626655803784585191)
          ·
            refine ⟨8936751939983705676877787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957834626655803784585191 8936751939983705676877787)
            ·
              refine ⟨13405127909975558515316681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8936751939983705676877787 13405127909975558515316681)
              ·
                refine ⟨10053845932481668886487511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13405127909975558515316681 10053845932481668886487511)
                ·
                  refine ⟨15080768898722503329731267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10053845932481668886487511 15080768898722503329731267)
                  ·
                    refine ⟨22621153348083754994596901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15080768898722503329731267 22621153348083754994596901)
                    ·
                      refine ⟨4241466252765704061486919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22621153348083754994596901 4241466252765704061486919)
                      ·
                        rfl

theorem cell23_8260226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_8260226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260226 prefixEnd_8260226 := by exact prefixLift 8260226
  have htrace : WordTrace (prefixWord ++ tailWord_8260226) baseStart_8260226 baseEnd_8260226 := by
    simpa [prefixWord, tailWord_8260226, baseEnd_8260226] using wordTrace_append hprefix tailTrace_8260226
  have hstable : (prefixWord ++ tailWord_8260226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260226).length < 2 ^ (prefixWord ++ tailWord_8260226).sum := by decide
  have hdescent : baseEnd_8260226 < baseStart_8260226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260248 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 1, 4, 2]
def baseStart_8260248 : Nat := 118140960795 + 8260248 * 2 ^ 59
def prefixEnd_8260248 : Nat := 4983230072969 + 3 ^ 40 * 8260248 * 2
def baseEnd_8260248 : Nat := 4241477549340102975411817

theorem tailTrace_8260248 : CollatzResearch.WordTrace tailWord_8260248 prefixEnd_8260248 4241477549340102975411817 := by
  unfold tailWord_8260248
  simp only [CollatzResearch.WordTrace]
  refine ⟨150637997689269854444458699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200850663585693139259278265 150637997689269854444458699)
  ·
    refine ⟨225956996533904781666688049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150637997689269854444458699 225956996533904781666688049)
    ·
      refine ⟨169467747400428586250016037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225956996533904781666688049 169467747400428586250016037)
      ·
        refine ⟨31775202637580359921878007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169467747400428586250016037 31775202637580359921878007)
        ·
          refine ⟨47662803956370539882817011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31775202637580359921878007 47662803956370539882817011)
          ·
            refine ⟨71494205934555809824225517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47662803956370539882817011 71494205934555809824225517)
            ·
              refine ⟨26810327225458428684084569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71494205934555809824225517 26810327225458428684084569)
              ·
                refine ⟨20107745419093821513063427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26810327225458428684084569 20107745419093821513063427)
                ·
                  refine ⟨30161618128640732269595141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20107745419093821513063427 30161618128640732269595141)
                  ·
                    refine ⟨5655303399120137300549089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30161618128640732269595141 5655303399120137300549089)
                    ·
                      refine ⟨4241477549340102975411817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655303399120137300549089 4241477549340102975411817)
                      ·
                        rfl

theorem cell23_8260248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_8260248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260248 prefixEnd_8260248 := by exact prefixLift 8260248
  have htrace : WordTrace (prefixWord ++ tailWord_8260248) baseStart_8260248 baseEnd_8260248 := by
    simpa [prefixWord, tailWord_8260248, baseEnd_8260248] using wordTrace_append hprefix tailTrace_8260248
  have hstable : (prefixWord ++ tailWord_8260248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260248).length < 2 ^ (prefixWord ++ tailWord_8260248).sum := by decide
  have hdescent : baseEnd_8260248 < baseStart_8260248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260252 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_8260252 : Nat := 118140960795 + 8260252 * 2 ^ 59
def prefixEnd_8260252 : Nat := 4983230072969 + 3 ^ 40 * 8260252 * 2
def baseEnd_8260252 : Nat := 4241479603262720959761799

theorem tailTrace_8260252 : CollatzResearch.WordTrace tailWord_8260252 prefixEnd_8260252 4241479603262720959761799 := by
  unfold tailWord_8260252
  simp only [CollatzResearch.WordTrace]
  refine ⟨150638070635262608786031505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200850760847016811714708673 150638070635262608786031505)
  ·
    refine ⟨112978552976446956589523629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150638070635262608786031505 112978552976446956589523629)
    ·
      refine ⟨42366957366167608721071361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112978552976446956589523629 42366957366167608721071361)
      ·
        refine ⟨31775218024625706540803521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42366957366167608721071361 31775218024625706540803521)
        ·
          refine ⟨23831413518469279905602641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31775218024625706540803521 23831413518469279905602641)
          ·
            refine ⟨17873560138851959929201981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23831413518469279905602641 17873560138851959929201981)
            ·
              refine ⟨6702585052069484973450743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17873560138851959929201981 6702585052069484973450743)
              ·
                refine ⟨10053877578104227460176115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6702585052069484973450743 10053877578104227460176115)
                ·
                  refine ⟨15080816367156341190264173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10053877578104227460176115 15080816367156341190264173)
                  ·
                    refine ⟨5655306137683627946349065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15080816367156341190264173 5655306137683627946349065)
                    ·
                      refine ⟨4241479603262720959761799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655306137683627946349065 4241479603262720959761799)
                      ·
                        rfl

theorem cell23_8260252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_8260252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260252 prefixEnd_8260252 := by exact prefixLift 8260252
  have htrace : WordTrace (prefixWord ++ tailWord_8260252) baseStart_8260252 baseEnd_8260252 := by
    simpa [prefixWord, tailWord_8260252, baseEnd_8260252] using wordTrace_append hprefix tailTrace_8260252
  have hstable : (prefixWord ++ tailWord_8260252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260252).length < 2 ^ (prefixWord ++ tailWord_8260252).sum := by decide
  have hdescent : baseEnd_8260252 < baseStart_8260252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260274 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_8260274 : Nat := 118140960795 + 8260274 * 2 ^ 59
def prefixEnd_8260274 : Nat := 4983230072969 + 3 ^ 40 * 8260274 * 2
def baseEnd_8260274 : Nat := 4241490899837119873686697

theorem tailTrace_8260274 : CollatzResearch.WordTrace tailWord_8260274 prefixEnd_8260274 4241490899837119873686697 := by
  unfold tailWord_8260274
  simp only [CollatzResearch.WordTrace]
  refine ⟨75319235919111378832340969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200851295784297010219575917 75319235919111378832340969)
  ·
    refine ⟨56489426939333534124255727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75319235919111378832340969 56489426939333534124255727)
    ·
      refine ⟨84734140409000301186383591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56489426939333534124255727 84734140409000301186383591)
      ·
        refine ⟨127101210613500451779575387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84734140409000301186383591 127101210613500451779575387)
        ·
          refine ⟨190651815920250677669363081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127101210613500451779575387 190651815920250677669363081)
          ·
            refine ⟨142988861940188008252022311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190651815920250677669363081 142988861940188008252022311)
            ·
              refine ⟨214483292910282012378033467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142988861940188008252022311 214483292910282012378033467)
              ·
                refine ⟨321724939365423018567050201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214483292910282012378033467 321724939365423018567050201)
                ·
                  refine ⟨241293704524067263925287651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321724939365423018567050201 241293704524067263925287651)
                  ·
                    refine ⟨361940556786100895887931477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241293704524067263925287651 361940556786100895887931477)
                    ·
                      refine ⟨4241490899837119873686697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 361940556786100895887931477 4241490899837119873686697)
                      ·
                        rfl

theorem cell23_8260274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_8260274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260274 prefixEnd_8260274 := by exact prefixLift 8260274
  have htrace : WordTrace (prefixWord ++ tailWord_8260274) baseStart_8260274 baseEnd_8260274 := by
    simpa [prefixWord, tailWord_8260274, baseEnd_8260274] using wordTrace_append hprefix tailTrace_8260274
  have hstable : (prefixWord ++ tailWord_8260274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260274).length < 2 ^ (prefixWord ++ tailWord_8260274).sum := by decide
  have hdescent : baseEnd_8260274 < baseStart_8260274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260348 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 3, 4]
def baseStart_8260348 : Nat := 118140960795 + 8260348 * 2 ^ 59
def prefixEnd_8260348 : Nat := 4983230072969 + 3 ^ 40 * 8260348 * 2
def baseEnd_8260348 : Nat := 1413842965801850861387119

theorem tailTrace_8260348 : CollatzResearch.WordTrace tailWord_8260348 prefixEnd_8260348 1413842965801850861387119 := by
  unfold tailWord_8260348
  simp only [CollatzResearch.WordTrace]
  refine ⟨150639821339088712983778849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200853095118784950645038465 150639821339088712983778849)
  ·
    refine ⟨112979866004316534737834137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150639821339088712983778849 112979866004316534737834137)
    ·
      refine ⟨84734899503237401053375603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112979866004316534737834137 84734899503237401053375603)
      ·
        refine ⟨127102349254856101580063405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84734899503237401053375603 127102349254856101580063405)
        ·
          refine ⟨47663380970571038092523777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127102349254856101580063405 47663380970571038092523777)
          ·
            refine ⟨35747535727928278569392833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47663380970571038092523777 35747535727928278569392833)
            ·
              refine ⟨26810651795946208927044625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35747535727928278569392833 26810651795946208927044625)
              ·
                refine ⟨20107988846959656695283469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26810651795946208927044625 20107988846959656695283469)
                ·
                  refine ⟨7540495817609871260731301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20107988846959656695283469 7540495817609871260731301)
                  ·
                    refine ⟨1413842965801850861387119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7540495817609871260731301 1413842965801850861387119)
                    ·
                      rfl

theorem cell23_8260348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_8260348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260348 prefixEnd_8260348 := by exact prefixLift 8260348
  have htrace : WordTrace (prefixWord ++ tailWord_8260348) baseStart_8260348 baseEnd_8260348 := by
    simpa [prefixWord, tailWord_8260348, baseEnd_8260348] using wordTrace_append hprefix tailTrace_8260348
  have hstable : (prefixWord ++ tailWord_8260348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260348).length < 2 ^ (prefixWord ++ tailWord_8260348).sum := by decide
  have hdescent : baseEnd_8260348 < baseStart_8260348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260375 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 3]
def baseStart_8260375 : Nat := 118140960795 + 8260375 * 2 ^ 59
def prefixEnd_8260375 : Nat := 4983230072969 + 3 ^ 40 * 8260375 * 2
def baseEnd_8260375 : Nat := 4241542761383223978523733

theorem tailTrace_8260375 : CollatzResearch.WordTrace tailWord_8260375 prefixEnd_8260375 4241542761383223978523733 := by
  unfold tailWord_8260375
  simp only [CollatzResearch.WordTrace]
  refine ⟨301280627449079609578790579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200853751632719739719193719 301280627449079609578790579)
  ·
    refine ⟨451920941173619414368185869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301280627449079609578790579 451920941173619414368185869)
    ·
      refine ⟨169470352940107280388069701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451920941173619414368185869 169470352940107280388069701)
      ·
        refine ⟨31775691176270115072763069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169470352940107280388069701 31775691176270115072763069)
        ·
          refine ⟨11915884191101293152286151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31775691176270115072763069 11915884191101293152286151)
          ·
            refine ⟨17873826286651939728429227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915884191101293152286151 17873826286651939728429227)
            ·
              refine ⟨26810739429977909592643841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17873826286651939728429227 26810739429977909592643841)
              ·
                refine ⟨20108054572483432194482881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26810739429977909592643841 20108054572483432194482881)
                ·
                  refine ⟨15081040929362574145862161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20108054572483432194482881 15081040929362574145862161)
                  ·
                    refine ⟨11310780697021930609396621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15081040929362574145862161 11310780697021930609396621)
                    ·
                      refine ⟨4241542761383223978523733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11310780697021930609396621 4241542761383223978523733)
                      ·
                        rfl

theorem cell23_8260375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_8260375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260375 prefixEnd_8260375 := by exact prefixLift 8260375
  have htrace : WordTrace (prefixWord ++ tailWord_8260375) baseStart_8260375 baseEnd_8260375 := by
    simpa [prefixWord, tailWord_8260375, baseEnd_8260375] using wordTrace_append hprefix tailTrace_8260375
  have hstable : (prefixWord ++ tailWord_8260375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260375).length < 2 ^ (prefixWord ++ tailWord_8260375).sum := by decide
  have hdescent : baseEnd_8260375 < baseStart_8260375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260415 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 2, 3, 2]
def baseStart_8260415 : Nat := 118140960795 + 8260415 * 2 ^ 59
def prefixEnd_8260415 : Nat := 4983230072969 + 3 ^ 40 * 8260415 * 2
def baseEnd_8260415 : Nat := 4241563300609403822023549

theorem tailTrace_8260415 : CollatzResearch.WordTrace tailWord_8260415 prefixEnd_8260415 4241563300609403822023549 := by
  unfold tailWord_8260415
  simp only [CollatzResearch.WordTrace]
  refine ⟨301282086368934696410246699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200854724245956464273497799 301282086368934696410246699)
  ·
    refine ⟨451923129553402044615370049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301282086368934696410246699 451923129553402044615370049)
    ·
      refine ⟨338942347165051533461527537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451923129553402044615370049 338942347165051533461527537)
      ·
        refine ⟨254206760373788650096145653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338942347165051533461527537 254206760373788650096145653)
        ·
          refine ⟨23831883785042685946513655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254206760373788650096145653 23831883785042685946513655)
          ·
            refine ⟨35747825677564028919770483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23831883785042685946513655 35747825677564028919770483)
            ·
              refine ⟨53621738516346043379655725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35747825677564028919770483 53621738516346043379655725)
              ·
                refine ⟨20108151943629766267370897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53621738516346043379655725 20108151943629766267370897)
                ·
                  refine ⟨15081113957722324700528173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20108151943629766267370897 15081113957722324700528173)
                  ·
                    refine ⟨5655417734145871762698065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15081113957722324700528173 5655417734145871762698065)
                    ·
                      refine ⟨4241563300609403822023549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655417734145871762698065 4241563300609403822023549)
                      ·
                        rfl

theorem cell23_8260415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 3, 2].length) (baseStart_8260415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260415 prefixEnd_8260415 := by exact prefixLift 8260415
  have htrace : WordTrace (prefixWord ++ tailWord_8260415) baseStart_8260415 baseEnd_8260415 := by
    simpa [prefixWord, tailWord_8260415, baseEnd_8260415] using wordTrace_append hprefix tailTrace_8260415
  have hstable : (prefixWord ++ tailWord_8260415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260415).length < 2 ^ (prefixWord ++ tailWord_8260415).sum := by decide
  have hdescent : baseEnd_8260415 < baseStart_8260415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260425 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 1, 5]
def baseStart_8260425 : Nat := 118140960795 + 8260425 * 2 ^ 59
def prefixEnd_8260425 : Nat := 4983230072969 + 3 ^ 40 * 8260425 * 2
def baseEnd_8260425 : Nat := 1413856145138649594299501

theorem tailTrace_8260425 : CollatzResearch.WordTrace tailWord_8260425 prefixEnd_8260425 1413856145138649594299501 := by
  unfold tailWord_8260425
  simp only [CollatzResearch.WordTrace]
  refine ⟨301282451098898468118110729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200854967399265645412073819 301282451098898468118110729)
  ·
    refine ⟨225961838324173851088583047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301282451098898468118110729 225961838324173851088583047)
    ·
      refine ⟨338942757486260776632874571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225961838324173851088583047 338942757486260776632874571)
      ·
        refine ⟨508414136229391164949311857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338942757486260776632874571 508414136229391164949311857)
        ·
          refine ⟨381310602172043373711983893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508414136229391164949311857 381310602172043373711983893)
          ·
            refine ⟨17873934476814533142749245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 381310602172043373711983893 17873934476814533142749245)
            ·
              refine ⟨6702725428805449928530967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17873934476814533142749245 6702725428805449928530967)
              ·
                refine ⟨10054088143208174892796451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6702725428805449928530967 10054088143208174892796451)
                ·
                  refine ⟨15081132214812262339194677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10054088143208174892796451 15081132214812262339194677)
                  ·
                    refine ⟨1413856145138649594299501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15081132214812262339194677 1413856145138649594299501)
                    ·
                      rfl

theorem cell23_8260425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 5].length) (baseStart_8260425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260425 prefixEnd_8260425 := by exact prefixLift 8260425
  have htrace : WordTrace (prefixWord ++ tailWord_8260425) baseStart_8260425 baseEnd_8260425 := by
    simpa [prefixWord, tailWord_8260425, baseEnd_8260425] using wordTrace_append hprefix tailTrace_8260425
  have hstable : (prefixWord ++ tailWord_8260425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260425).length < 2 ^ (prefixWord ++ tailWord_8260425).sum := by decide
  have hdescent : baseEnd_8260425 < baseStart_8260425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260439 : List Nat := [1, 1, 3, 2, 4, 1, 4, 2, 1, 1, 3]
def baseStart_8260439 : Nat := 118140960795 + 8260439 * 2 ^ 59
def prefixEnd_8260439 : Nat := 4983230072969 + 3 ^ 40 * 8260439 * 2
def baseEnd_8260439 : Nat := 4241575624145111728123439

theorem tailTrace_8260439 : CollatzResearch.WordTrace tailWord_8260439 prefixEnd_8260439 4241575624145111728123439 := by
  unfold tailWord_8260439
  simp only [CollatzResearch.WordTrace]
  refine ⟨301282961720847748509120371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200855307813898499006080247 301282961720847748509120371)
  ·
    refine ⟨451924442581271622763680557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301282961720847748509120371 451924442581271622763680557)
    ·
      refine ⟨169471665967976858536380209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451924442581271622763680557 169471665967976858536380209)
      ·
        refine ⟨127103749475982643902285157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169471665967976858536380209 127103749475982643902285157)
        ·
          refine ⟨23831953026746745731678467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127103749475982643902285157 23831953026746745731678467)
          ·
            refine ⟨35747929540120118597517701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23831953026746745731678467 35747929540120118597517701)
            ·
              refine ⟨6702736788772522237034569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35747929540120118597517701 6702736788772522237034569)
              ·
                refine ⟨5027052591579391677775927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6702736788772522237034569 5027052591579391677775927)
                ·
                  refine ⟨7540578887369087516663891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027052591579391677775927 7540578887369087516663891)
                  ·
                    refine ⟨11310868331053631274995837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7540578887369087516663891 11310868331053631274995837)
                    ·
                      refine ⟨4241575624145111728123439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11310868331053631274995837 4241575624145111728123439)
                      ·
                        rfl

theorem cell23_8260439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_8260439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260439 prefixEnd_8260439 := by exact prefixLift 8260439
  have htrace : WordTrace (prefixWord ++ tailWord_8260439) baseStart_8260439 baseEnd_8260439 := by
    simpa [prefixWord, tailWord_8260439, baseEnd_8260439] using wordTrace_append hprefix tailTrace_8260439
  have hstable : (prefixWord ++ tailWord_8260439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260439).length < 2 ^ (prefixWord ++ tailWord_8260439).sum := by decide
  have hdescent : baseEnd_8260439 < baseStart_8260439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260448 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 3]
def baseStart_8260448 : Nat := 118140960795 + 8260448 * 2 ^ 59
def prefixEnd_8260448 : Nat := 4983230072969 + 3 ^ 40 * 8260448 * 2
def baseEnd_8260448 : Nat := 4241580245471002192910897

theorem tailTrace_8260448 : CollatzResearch.WordTrace tailWord_8260448 prefixEnd_8260448 4241580245471002192910897 := by
  unfold tailWord_8260448
  simp only [CollatzResearch.WordTrace]
  refine ⟨150641644988907571523098999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200855526651876762030798665 150641644988907571523098999)
  ·
    refine ⟨225962467483361357284648499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150641644988907571523098999 225962467483361357284648499)
    ·
      refine ⟨338943701225042035926972749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225962467483361357284648499 338943701225042035926972749)
      ·
        refine ⟨127103887959390763472614781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338943701225042035926972749 127103887959390763472614781)
        ·
          refine ⟨47663957984771536302230543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127103887959390763472614781 47663957984771536302230543)
          ·
            refine ⟨71495936977157304453345815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47663957984771536302230543 71495936977157304453345815)
            ·
              refine ⟨107243905465735956680018723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71495936977157304453345815 107243905465735956680018723)
              ·
                refine ⟨160865858198603935020028085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107243905465735956680018723 160865858198603935020028085)
                ·
                  refine ⟨15081174206119118908127633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160865858198603935020028085 15081174206119118908127633)
                  ·
                    refine ⟨11310880654589339181095725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15081174206119118908127633 11310880654589339181095725)
                    ·
                      refine ⟨4241580245471002192910897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11310880654589339181095725 4241580245471002192910897)
                      ·
                        rfl

theorem cell23_8260448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_8260448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260448 prefixEnd_8260448 := by exact prefixLift 8260448
  have htrace : WordTrace (prefixWord ++ tailWord_8260448) baseStart_8260448 baseEnd_8260448 := by
    simpa [prefixWord, tailWord_8260448, baseEnd_8260448] using wordTrace_append hprefix tailTrace_8260448
  have hstable : (prefixWord ++ tailWord_8260448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260448).length < 2 ^ (prefixWord ++ tailWord_8260448).sum := by decide
  have hdescent : baseEnd_8260448 < baseStart_8260448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260455 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 2, 4]
def baseStart_8260455 : Nat := 118140960795 + 8260455 * 2 ^ 59
def prefixEnd_8260455 : Nat := 4983230072969 + 3 ^ 40 * 8260455 * 2
def baseEnd_8260455 : Nat := 1413861279945194555174455

theorem tailTrace_8260455 : CollatzResearch.WordTrace tailWord_8260455 prefixEnd_8260455 1413861279945194555174455 := by
  unfold tailWord_8260455
  simp only [CollatzResearch.WordTrace]
  refine ⟨301283545288789783241702819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200855696859193188827801879 301283545288789783241702819)
  ·
    refine ⟨451925317933184674862554229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301283545288789783241702819 451925317933184674862554229)
    ·
      refine ⟨42367998556236063268364459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 451925317933184674862554229 42367998556236063268364459)
      ·
        refine ⟨63551997834354094902546689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42367998556236063268364459 63551997834354094902546689)
        ·
          refine ⟨47663998375765571176910017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63551997834354094902546689 47663998375765571176910017)
          ·
            refine ⟨35747998781824178382682513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47663998375765571176910017 35747998781824178382682513)
            ·
              refine ⟨26810999086368133787011885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35747998781824178382682513 26810999086368133787011885)
              ·
                refine ⟨10054124657388050170129457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26810999086368133787011885 10054124657388050170129457)
                ·
                  refine ⟨7540593493041037627597093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10054124657388050170129457 7540593493041037627597093)
                  ·
                    refine ⟨1413861279945194555174455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7540593493041037627597093 1413861279945194555174455)
                    ·
                      rfl

theorem cell23_8260455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_8260455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260455 prefixEnd_8260455 := by exact prefixLift 8260455
  have htrace : WordTrace (prefixWord ++ tailWord_8260455) baseStart_8260455 baseEnd_8260455 := by
    simpa [prefixWord, tailWord_8260455, baseEnd_8260455] using wordTrace_append hprefix tailTrace_8260455
  have hstable : (prefixWord ++ tailWord_8260455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260455).length < 2 ^ (prefixWord ++ tailWord_8260455).sum := by decide
  have hdescent : baseEnd_8260455 < baseStart_8260455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260535 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 1, 4, 2]
def baseStart_8260535 : Nat := 118140960795 + 8260535 * 2 ^ 59
def prefixEnd_8260535 : Nat := 4983230072969 + 3 ^ 40 * 8260535 * 2
def baseEnd_8260535 : Nat := 4241624918287943352522997

theorem tailTrace_8260535 : CollatzResearch.WordTrace tailWord_8260535 prefixEnd_8260535 4241624918287943352522997 := by
  unfold tailWord_8260535
  simp only [CollatzResearch.WordTrace]
  refine ⟨301286463128499956904615059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200857642085666637936410039 301286463128499956904615059)
  ·
    refine ⟨451929694692749935356922589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301286463128499956904615059 451929694692749935356922589)
    ·
      refine ⟨169473635509781225758845971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451929694692749935356922589 169473635509781225758845971)
      ·
        refine ⟨254210453264671838638268957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169473635509781225758845971 254210453264671838638268957)
        ·
          refine ⟨95328919974251939489350859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254210453264671838638268957 95328919974251939489350859)
          ·
            refine ⟨142993379961377909234026289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95328919974251939489350859 142993379961377909234026289)
            ·
              refine ⟨107245034971033431925519717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142993379961377909234026289 107245034971033431925519717)
              ·
                refine ⟨20108444057068768486034947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107245034971033431925519717 20108444057068768486034947)
                ·
                  refine ⟨30162666085603152729052421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20108444057068768486034947 30162666085603152729052421)
                  ·
                    refine ⟨5655499891050591136697329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30162666085603152729052421 5655499891050591136697329)
                    ·
                      refine ⟨4241624918287943352522997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655499891050591136697329 4241624918287943352522997)
                      ·
                        rfl

theorem cell23_8260535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 4, 2].length) (baseStart_8260535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260535 prefixEnd_8260535 := by exact prefixLift 8260535
  have htrace : WordTrace (prefixWord ++ tailWord_8260535) baseStart_8260535 baseEnd_8260535 := by
    simpa [prefixWord, tailWord_8260535, baseEnd_8260535] using wordTrace_append hprefix tailTrace_8260535
  have hstable : (prefixWord ++ tailWord_8260535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260535).length < 2 ^ (prefixWord ++ tailWord_8260535).sum := by decide
  have hdescent : baseEnd_8260535 < baseStart_8260535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260538 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_8260538 : Nat := 118140960795 + 8260538 * 2 ^ 59
def prefixEnd_8260538 : Nat := 4983230072969 + 3 ^ 40 * 8260538 * 2
def baseEnd_8260538 : Nat := 4241626458729906840785483

theorem tailTrace_8260538 : CollatzResearch.WordTrace tailWord_8260538 prefixEnd_8260538 4241626458729906840785483 := by
  unfold tailWord_8260538
  simp only [CollatzResearch.WordTrace]
  refine ⟨75321643136872272104243567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200857715031659392277982845 75321643136872272104243567)
  ·
    refine ⟨112982464705308408156365351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75321643136872272104243567 112982464705308408156365351)
    ·
      refine ⟨169473697057962612234548027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112982464705308408156365351 169473697057962612234548027)
      ·
        refine ⟨254210545586943918351822041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169473697057962612234548027 254210545586943918351822041)
        ·
          refine ⟨190657909190207938763866531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254210545586943918351822041 190657909190207938763866531)
          ·
            refine ⟨285986863785311908145799797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190657909190207938763866531 285986863785311908145799797)
            ·
              refine ⟨26811268479872991388668731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285986863785311908145799797 26811268479872991388668731)
              ·
                refine ⟨40216902719809487083003097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26811268479872991388668731 40216902719809487083003097)
                ·
                  refine ⟨30162677039857115312252323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40216902719809487083003097 30162677039857115312252323)
                  ·
                    refine ⟨45244015559785672968378485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30162677039857115312252323 45244015559785672968378485)
                    ·
                      refine ⟨4241626458729906840785483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45244015559785672968378485 4241626458729906840785483)
                      ·
                        rfl

theorem cell23_8260538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_8260538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260538 prefixEnd_8260538 := by exact prefixLift 8260538
  have htrace : WordTrace (prefixWord ++ tailWord_8260538) baseStart_8260538 baseEnd_8260538 := by
    simpa [prefixWord, tailWord_8260538, baseEnd_8260538] using wordTrace_append hprefix tailTrace_8260538
  have hstable : (prefixWord ++ tailWord_8260538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260538).length < 2 ^ (prefixWord ++ tailWord_8260538).sum := by decide
  have hdescent : baseEnd_8260538 < baseStart_8260538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260569 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 2, 2, 2]
def baseStart_8260569 : Nat := 118140960795 + 8260569 * 2 ^ 59
def prefixEnd_8260569 : Nat := 4983230072969 + 3 ^ 40 * 8260569 * 2
def baseEnd_8260569 : Nat := 4241642376630196219497841

theorem tailTrace_8260569 : CollatzResearch.WordTrace tailWord_8260569 prefixEnd_8260569 4241642376630196219497841 := by
  unfold tailWord_8260569
  simp only [CollatzResearch.WordTrace]
  refine ⟨301287703210376780711352761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200858468806917853807568507 301287703210376780711352761)
  ·
    refine ⟨225965777407782585533514571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301287703210376780711352761 225965777407782585533514571)
    ·
      refine ⟨338948666111673878300271857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225965777407782585533514571 338948666111673878300271857)
      ·
        refine ⟨254211499583755408725203893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338948666111673878300271857 254211499583755408725203893)
        ·
          refine ⟨23832328085977069567987865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254211499583755408725203893 23832328085977069567987865)
          ·
            refine ⟨17874246064482802175990899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23832328085977069567987865 17874246064482802175990899)
            ·
              refine ⟨26811369096724203263986349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17874246064482802175990899 26811369096724203263986349)
              ·
                refine ⟨10054263411271576223994881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26811369096724203263986349 10054263411271576223994881)
                ·
                  refine ⟨7540697558453682167996161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10054263411271576223994881 7540697558453682167996161)
                  ·
                    refine ⟨5655523168840261625997121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7540697558453682167996161 5655523168840261625997121)
                    ·
                      refine ⟨4241642376630196219497841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655523168840261625997121 4241642376630196219497841)
                      ·
                        rfl

theorem cell23_8260569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 2, 2].length) (baseStart_8260569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260569 prefixEnd_8260569 := by exact prefixLift 8260569
  have htrace : WordTrace (prefixWord ++ tailWord_8260569) baseStart_8260569 baseEnd_8260569 := by
    simpa [prefixWord, tailWord_8260569, baseEnd_8260569] using wordTrace_append hprefix tailTrace_8260569
  have hstable : (prefixWord ++ tailWord_8260569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260569).length < 2 ^ (prefixWord ++ tailWord_8260569).sum := by decide
  have hdescent : baseEnd_8260569 < baseStart_8260569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260609 : List Nat := [1, 2, 4, 1, 2, 4, 2, 2, 5]
def baseStart_8260609 : Nat := 118140960795 + 8260609 * 2 ^ 59
def prefixEnd_8260609 : Nat := 4983230072969 + 3 ^ 40 * 8260609 * 2
def baseEnd_8260609 : Nat := 471295879539597340333073

theorem tailTrace_8260609 : CollatzResearch.WordTrace tailWord_8260609 prefixEnd_8260609 471295879539597340333073 := by
  unfold tailWord_8260609
  simp only [CollatzResearch.WordTrace]
  refine ⟨301289162130231867542808881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200859441420154578361872587 301289162130231867542808881)
  ·
    refine ⟨225966871597673900657106661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301289162130231867542808881 225966871597673900657106661)
    ·
      refine ⟨42368788424563856373207499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225966871597673900657106661 42368788424563856373207499)
      ·
        refine ⟨63553182636845784559811249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42368788424563856373207499 63553182636845784559811249)
        ·
          refine ⟨47664886977634338419858437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63553182636845784559811249 47664886977634338419858437)
          ·
            refine ⟨8937166308306438453723457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47664886977634338419858437 8937166308306438453723457)
            ·
              refine ⟨6702874731229828840292593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8937166308306438453723457 6702874731229828840292593)
              ·
                refine ⟨5027156048422371630219445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6702874731229828840292593 5027156048422371630219445)
                ·
                  refine ⟨471295879539597340333073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5027156048422371630219445 471295879539597340333073)
                  ·
                    rfl

theorem cell23_8260609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 5].length) (baseStart_8260609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260609 prefixEnd_8260609 := by exact prefixLift 8260609
  have htrace : WordTrace (prefixWord ++ tailWord_8260609) baseStart_8260609 baseEnd_8260609 := by
    simpa [prefixWord, tailWord_8260609, baseEnd_8260609] using wordTrace_append hprefix tailTrace_8260609
  have hstable : (prefixWord ++ tailWord_8260609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260609).length < 2 ^ (prefixWord ++ tailWord_8260609).sum := by decide
  have hdescent : baseEnd_8260609 < baseStart_8260609 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260642 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_8260642 : Nat := 118140960795 + 8260642 * 2 ^ 59
def prefixEnd_8260642 : Nat := 4983230072969 + 3 ^ 40 * 8260642 * 2
def baseEnd_8260642 : Nat := 4241679860717974433885005

theorem tailTrace_8260642 : CollatzResearch.WordTrace tailWord_8260642 prefixEnd_8260642 4241679860717974433885005 := by
  unfold tailWord_8260642
  simp only [CollatzResearch.WordTrace]
  refine ⟨75322591434778078544690045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200860243826074876119173453 75322591434778078544690045)
  ·
    refine ⟨28245971788041779454258767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75322591434778078544690045 28245971788041779454258767)
    ·
      refine ⟨42368957682062669181388151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28245971788041779454258767 42368957682062669181388151)
      ·
        refine ⟨63553436523094003772082227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42368957682062669181388151 63553436523094003772082227)
        ·
          refine ⟨95330154784641005658123341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63553436523094003772082227 95330154784641005658123341)
          ·
            refine ⟨35748808044240377121796253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95330154784641005658123341 35748808044240377121796253)
            ·
              refine ⟨13405803016590141420673595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35748808044240377121796253 13405803016590141420673595)
              ·
                refine ⟨20108704524885212131010393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13405803016590141420673595 20108704524885212131010393)
                ·
                  refine ⟨15081528393663909098257795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20108704524885212131010393 15081528393663909098257795)
                  ·
                    refine ⟨22622292590495863647386693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15081528393663909098257795 22622292590495863647386693)
                    ·
                      refine ⟨4241679860717974433885005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22622292590495863647386693 4241679860717974433885005)
                      ·
                        rfl

theorem cell23_8260642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_8260642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260642 prefixEnd_8260642 := by exact prefixLift 8260642
  have htrace : WordTrace (prefixWord ++ tailWord_8260642) baseStart_8260642 baseEnd_8260642 := by
    simpa [prefixWord, tailWord_8260642, baseEnd_8260642] using wordTrace_append hprefix tailTrace_8260642
  have hstable : (prefixWord ++ tailWord_8260642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260642).length < 2 ^ (prefixWord ++ tailWord_8260642).sum := by decide
  have hdescent : baseEnd_8260642 < baseStart_8260642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260645 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 1, 4, 3]
def baseStart_8260645 : Nat := 118140960795 + 8260645 * 2 ^ 59
def prefixEnd_8260645 : Nat := 4983230072969 + 3 ^ 40 * 8260645 * 2
def baseEnd_8260645 : Nat := 4241681401159937922147491

theorem tailTrace_8260645 : CollatzResearch.WordTrace tailWord_8260645 prefixEnd_8260645 4241681401159937922147491 := by
  unfold tailWord_8260645
  simp only [CollatzResearch.WordTrace]
  refine ⟨301290475158101445691119389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200860316772067630460746259 301290475158101445691119389)
  ·
    refine ⟨112983928184288042134169771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301290475158101445691119389 112983928184288042134169771)
    ·
      refine ⟨169475892276432063201254657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112983928184288042134169771 169475892276432063201254657)
      ·
        refine ⟨127106919207324047400940993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169475892276432063201254657 127106919207324047400940993)
        ·
          refine ⟨95330189405493035550705745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127106919207324047400940993 95330189405493035550705745)
          ·
            refine ⟨71497642054119776663029309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95330189405493035550705745 71497642054119776663029309)
            ·
              refine ⟨26811615770294916248635991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71497642054119776663029309 26811615770294916248635991)
              ·
                refine ⟨40217423655442374372953987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26811615770294916248635991 40217423655442374372953987)
                ·
                  refine ⟨60326135483163561559430981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40217423655442374372953987 60326135483163561559430981)
                  ·
                    refine ⟨11311150403093167792393309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60326135483163561559430981 11311150403093167792393309)
                    ·
                      refine ⟨4241681401159937922147491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11311150403093167792393309 4241681401159937922147491)
                      ·
                        rfl

theorem cell23_8260645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_8260645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260645 prefixEnd_8260645 := by exact prefixLift 8260645
  have htrace : WordTrace (prefixWord ++ tailWord_8260645) baseStart_8260645 baseEnd_8260645 := by
    simpa [prefixWord, tailWord_8260645, baseEnd_8260645] using wordTrace_append hprefix tailTrace_8260645
  have hstable : (prefixWord ++ tailWord_8260645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260645).length < 2 ^ (prefixWord ++ tailWord_8260645).sum := by decide
  have hdescent : baseEnd_8260645 < baseStart_8260645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260665 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 8]
def baseStart_8260665 : Nat := 118140960795 + 8260665 * 2 ^ 59
def prefixEnd_8260665 : Nat := 4983230072969 + 3 ^ 40 * 8260665 * 2
def baseEnd_8260665 : Nat := 471299074530336427099711

theorem tailTrace_8260665 : CollatzResearch.WordTrace tailWord_8260665 prefixEnd_8260665 471299074530336427099711 := by
  unfold tailWord_8260665
  simp only [CollatzResearch.WordTrace]
  refine ⟨301291204618028989106847449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200860803078685992737898299 301291204618028989106847449)
  ·
    refine ⟨225968403463521741830135587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301291204618028989106847449 225968403463521741830135587)
    ·
      refine ⟨338952605195282612745203381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225968403463521741830135587 338952605195282612745203381)
      ·
        refine ⟨31776806737057744944862817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338952605195282612745203381 31776806737057744944862817)
        ·
          refine ⟨23832605052793308708647113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31776806737057744944862817 23832605052793308708647113)
          ·
            refine ⟨17874453789594981531485335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23832605052793308708647113 17874453789594981531485335)
            ·
              refine ⟨26811680684392472297228003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17874453789594981531485335 26811680684392472297228003)
              ·
                refine ⟨40217521026588708445842005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26811680684392472297228003 40217521026588708445842005)
                ·
                  refine ⟨471299074530336427099711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40217521026588708445842005 471299074530336427099711)
                  ·
                    rfl

theorem cell23_8260665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 8].length) (baseStart_8260665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260665 prefixEnd_8260665 := by exact prefixLift 8260665
  have htrace : WordTrace (prefixWord ++ tailWord_8260665) baseStart_8260665 baseEnd_8260665 := by
    simpa [prefixWord, tailWord_8260665, baseEnd_8260665] using wordTrace_append hprefix tailTrace_8260665
  have hstable : (prefixWord ++ tailWord_8260665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260665).length < 2 ^ (prefixWord ++ tailWord_8260665).sum := by decide
  have hdescent : baseEnd_8260665 < baseStart_8260665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260669 : List Nat := [1, 4, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_8260669 : Nat := 118140960795 + 8260669 * 2 ^ 59
def prefixEnd_8260669 : Nat := 4983230072969 + 3 ^ 40 * 8260669 * 2
def baseEnd_8260669 : Nat := 1413897908231881942749127

theorem tailTrace_8260669 : CollatzResearch.WordTrace tailWord_8260669 prefixEnd_8260669 1413897908231881942749127 := by
  unfold tailWord_8260669
  simp only [CollatzResearch.WordTrace]
  refine ⟨301291350510014497789993061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200860900340009665193328707 301291350510014497789993061)
  ·
    refine ⟨56492128220627718335623699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301291350510014497789993061 56492128220627718335623699)
    ·
      refine ⟨84738192330941577503435549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56492128220627718335623699 84738192330941577503435549)
      ·
        refine ⟨31776822124103091563788331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84738192330941577503435549 31776822124103091563788331)
        ·
          refine ⟨47665233186154637345682497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31776822124103091563788331 47665233186154637345682497)
          ·
            refine ⟨35748924889615978009261873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47665233186154637345682497 35748924889615978009261873)
            ·
              refine ⟨26811693667211983506946405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35748924889615978009261873 26811693667211983506946405)
              ·
                refine ⟨5027192562602246907552451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26811693667211983506946405 5027192562602246907552451)
                ·
                  refine ⟨7540788843903370361328677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027192562602246907552451 7540788843903370361328677)
                  ·
                    refine ⟨1413897908231881942749127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7540788843903370361328677 1413897908231881942749127)
                    ·
                      rfl

theorem cell23_8260669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_8260669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260669 prefixEnd_8260669 := by exact prefixLift 8260669
  have htrace : WordTrace (prefixWord ++ tailWord_8260669) baseStart_8260669 baseEnd_8260669 := by
    simpa [prefixWord, tailWord_8260669, baseEnd_8260669] using wordTrace_append hprefix tailTrace_8260669
  have hstable : (prefixWord ++ tailWord_8260669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260669).length < 2 ^ (prefixWord ++ tailWord_8260669).sum := by decide
  have hdescent : baseEnd_8260669 < baseStart_8260669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260688 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_8260688 : Nat := 118140960795 + 8260688 * 2 ^ 59
def prefixEnd_8260688 : Nat := 4983230072969 + 3 ^ 40 * 8260688 * 2
def baseEnd_8260688 : Nat := 4241703480828081253909793

theorem tailTrace_8260688 : CollatzResearch.WordTrace tailWord_8260688 prefixEnd_8260688 4241703480828081253909793 := by
  unfold tailWord_8260688
  simp only [CollatzResearch.WordTrace]
  refine ⟨150646021748472832017467359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200861362331297109356623145 150646021748472832017467359)
  ·
    refine ⟨225969032622709248026201039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150646021748472832017467359 225969032622709248026201039)
    ·
      refine ⟨338953548934063872039301559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225969032622709248026201039 338953548934063872039301559)
      ·
        refine ⟨508430323401095808058952339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338953548934063872039301559 508430323401095808058952339)
        ·
          refine ⟨762645485101643712088428509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508430323401095808058952339 762645485101643712088428509)
          ·
            refine ⟨285992056913116392033160691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 762645485101643712088428509 285992056913116392033160691)
            ·
              refine ⟨428988085369674588049741037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285992056913116392033160691 428988085369674588049741037)
              ·
                refine ⟨160870532013627970518652889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428988085369674588049741037 160870532013627970518652889)
                ·
                  refine ⟨120652899010220977888989667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160870532013627970518652889 120652899010220977888989667)
                  ·
                    refine ⟨180979348515331466833484501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120652899010220977888989667 180979348515331466833484501)
                    ·
                      refine ⟨4241703480828081253909793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180979348515331466833484501 4241703480828081253909793)
                      ·
                        rfl

theorem cell23_8260688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_8260688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260688 prefixEnd_8260688 := by exact prefixLift 8260688
  have htrace : WordTrace (prefixWord ++ tailWord_8260688) baseStart_8260688 baseEnd_8260688 := by
    simpa [prefixWord, tailWord_8260688, baseEnd_8260688] using wordTrace_append hprefix tailTrace_8260688
  have hstable : (prefixWord ++ tailWord_8260688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260688).length < 2 ^ (prefixWord ++ tailWord_8260688).sum := by decide
  have hdescent : baseEnd_8260688 < baseStart_8260688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260745 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 6]
def baseStart_8260745 : Nat := 118140960795 + 8260745 * 2 ^ 59
def prefixEnd_8260745 : Nat := 4983230072969 + 3 ^ 40 * 8260745 * 2
def baseEnd_8260745 : Nat := 4241732749225387530897031

theorem tailTrace_8260745 : CollatzResearch.WordTrace tailWord_8260745 prefixEnd_8260745 4241732749225387530897031 := by
  unfold tailWord_8260745
  simp only [CollatzResearch.WordTrace]
  refine ⟨301294122457739162769759689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200862748305159441846506459 301294122457739162769759689)
  ·
    refine ⟨225970591843304372077319767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301294122457739162769759689 225970591843304372077319767)
    ·
      refine ⟨338955887764956558115979651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225970591843304372077319767 338955887764956558115979651)
      ·
        refine ⟨508433831647434837173969477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338955887764956558115979651 508433831647434837173969477)
        ·
          refine ⟨95331343433894031970119277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508433831647434837173969477 95331343433894031970119277)
          ·
            refine ⟨35749253787710261988794729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95331343433894031970119277 35749253787710261988794729)
            ·
              refine ⟨26811940340782696491596047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35749253787710261988794729 26811940340782696491596047)
              ·
                refine ⟨40217910511174044737394071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26811940340782696491596047 40217910511174044737394071)
                ·
                  refine ⟨60326865766761067106091107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40217910511174044737394071 60326865766761067106091107)
                  ·
                    refine ⟨90490298650141600659136661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60326865766761067106091107 90490298650141600659136661)
                    ·
                      refine ⟨4241732749225387530897031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90490298650141600659136661 4241732749225387530897031)
                      ·
                        rfl

theorem cell23_8260745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_8260745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260745 prefixEnd_8260745 := by exact prefixLift 8260745
  have htrace : WordTrace (prefixWord ++ tailWord_8260745) baseStart_8260745 baseEnd_8260745 := by
    simpa [prefixWord, tailWord_8260745, baseEnd_8260745] using wordTrace_append hprefix tailTrace_8260745
  have hstable : (prefixWord ++ tailWord_8260745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260745).length < 2 ^ (prefixWord ++ tailWord_8260745).sum := by decide
  have hdescent : baseEnd_8260745 < baseStart_8260745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260752 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 3]
def baseStart_8260752 : Nat := 118140960795 + 8260752 * 2 ^ 59
def prefixEnd_8260752 : Nat := 4983230072969 + 3 ^ 40 * 8260752 * 2
def baseEnd_8260752 : Nat := 4241736343589969003509499

theorem tailTrace_8260752 : CollatzResearch.WordTrace tailWord_8260752 prefixEnd_8260752 4241736343589969003509499 := by
  unfold tailWord_8260752
  simp only [CollatzResearch.WordTrace]
  refine ⟨150647188884356901482632255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200862918512475868643509673 150647188884356901482632255)
  ·
    refine ⟨225970783326535352223948383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150647188884356901482632255 225970783326535352223948383)
    ·
      refine ⟨338956174989803028335922575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225970783326535352223948383 338956174989803028335922575)
      ·
        refine ⟨508434262484704542503883863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338956174989803028335922575 508434262484704542503883863)
        ·
          refine ⟨762651393727056813755825795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508434262484704542503883863 762651393727056813755825795)
          ·
            refine ⟨1143977090590585220633738693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762651393727056813755825795 1143977090590585220633738693)
            ·
              refine ⟨214495704485734728868826005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1143977090590585220633738693 214495704485734728868826005)
              ·
                refine ⟨10054486147768815415726219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214495704485734728868826005 10054486147768815415726219)
                ·
                  refine ⟨15081729221653223123589329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10054486147768815415726219 15081729221653223123589329)
                  ·
                    refine ⟨11311296916239917342691997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15081729221653223123589329 11311296916239917342691997)
                    ·
                      refine ⟨4241736343589969003509499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11311296916239917342691997 4241736343589969003509499)
                      ·
                        rfl

theorem cell23_8260752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 3].length) (baseStart_8260752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260752 prefixEnd_8260752 := by exact prefixLift 8260752
  have htrace : WordTrace (prefixWord ++ tailWord_8260752) baseStart_8260752 baseEnd_8260752 := by
    simpa [prefixWord, tailWord_8260752, baseEnd_8260752] using wordTrace_append hprefix tailTrace_8260752
  have hstable : (prefixWord ++ tailWord_8260752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260752).length < 2 ^ (prefixWord ++ tailWord_8260752).sum := by decide
  have hdescent : baseEnd_8260752 < baseStart_8260752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260762 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_8260762 : Nat := 118140960795 + 8260762 * 2 ^ 59
def prefixEnd_8260762 : Nat := 4983230072969 + 3 ^ 40 * 8260762 * 2
def baseEnd_8260762 : Nat := 4241741478396513964384453

theorem tailTrace_8260762 : CollatzResearch.WordTrace tailWord_8260762 prefixEnd_8260762 4241741478396513964384453 := by
  unfold tailWord_8260762
  simp only [CollatzResearch.WordTrace]
  refine ⟨75323685624669393668282135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200863161665785049782085693 75323685624669393668282135)
  ·
    refine ⟨112985528437004090502423203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75323685624669393668282135 112985528437004090502423203)
    ·
      refine ⟨169478292655506135753634805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112985528437004090502423203 169478292655506135753634805)
      ·
        refine ⟨15888589936453700226903263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169478292655506135753634805 15888589936453700226903263)
        ·
          refine ⟨23832884904680550340354895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15888589936453700226903263 23832884904680550340354895)
          ·
            refine ⟨35749327357020825510532343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23832884904680550340354895 35749327357020825510532343)
            ·
              refine ⟨53623991035531238265798515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35749327357020825510532343 53623991035531238265798515)
              ·
                refine ⟨80435986553296857398697773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53623991035531238265798515 80435986553296857398697773)
                ·
                  refine ⟨30163494957486321524511665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80435986553296857398697773 30163494957486321524511665)
                  ·
                    refine ⟨22622621218114741143383749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30163494957486321524511665 22622621218114741143383749)
                    ·
                      refine ⟨4241741478396513964384453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22622621218114741143383749 4241741478396513964384453)
                      ·
                        rfl

theorem cell23_8260762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_8260762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260762 prefixEnd_8260762 := by exact prefixLift 8260762
  have htrace : WordTrace (prefixWord ++ tailWord_8260762) baseStart_8260762 baseEnd_8260762 := by
    simpa [prefixWord, tailWord_8260762, baseEnd_8260762] using wordTrace_append hprefix tailTrace_8260762
  have hstable : (prefixWord ++ tailWord_8260762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260762).length < 2 ^ (prefixWord ++ tailWord_8260762).sum := by decide
  have hdescent : baseEnd_8260762 < baseStart_8260762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260783 : List Nat := [1, 1, 2, 1, 2, 3, 6, 2, 1, 2, 2]
def baseStart_8260783 : Nat := 118140960795 + 8260783 * 2 ^ 59
def prefixEnd_8260783 : Nat := 4983230072969 + 3 ^ 40 * 8260783 * 2
def baseEnd_8260783 : Nat := 4241752261490258382221857

theorem tailTrace_8260783 : CollatzResearch.WordTrace tailWord_8260783 prefixEnd_8260783 4241752261490258382221857 := by
  unfold tailWord_8260783
  simp only [CollatzResearch.WordTrace]
  refine ⟨301295508431601495259643003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200863672287734330173095335 301295508431601495259643003)
  ·
    refine ⟨451943262647402242889464505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301295508431601495259643003 451943262647402242889464505)
    ·
      refine ⟨338957446985551682167098379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451943262647402242889464505 338957446985551682167098379)
      ·
        refine ⟨508436170478327523250647569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338957446985551682167098379 508436170478327523250647569)
        ·
          refine ⟨381327127858745642437985677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508436170478327523250647569 381327127858745642437985677)
          ·
            refine ⟨142997672947029615914244629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381327127858745642437985677 142997672947029615914244629)
            ·
              refine ⟨6703015919392013245980217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142997672947029615914244629 6703015919392013245980217)
              ·
                refine ⟨5027261939544009934485163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6703015919392013245980217 5027261939544009934485163)
                ·
                  refine ⟨7540892909316014901727745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027261939544009934485163 7540892909316014901727745)
                  ·
                    refine ⟨5655669681987011176295809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7540892909316014901727745 5655669681987011176295809)
                    ·
                      refine ⟨4241752261490258382221857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655669681987011176295809 4241752261490258382221857)
                      ·
                        rfl

theorem cell23_8260783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 1, 2, 2].length) (baseStart_8260783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260783 prefixEnd_8260783 := by exact prefixLift 8260783
  have htrace : WordTrace (prefixWord ++ tailWord_8260783) baseStart_8260783 baseEnd_8260783 := by
    simpa [prefixWord, tailWord_8260783, baseEnd_8260783] using wordTrace_append hprefix tailTrace_8260783
  have hstable : (prefixWord ++ tailWord_8260783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260783).length < 2 ^ (prefixWord ++ tailWord_8260783).sum := by decide
  have hdescent : baseEnd_8260783 < baseStart_8260783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260799 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 2, 1, 3]
def baseStart_8260799 : Nat := 118140960795 + 8260799 * 2 ^ 59
def prefixEnd_8260799 : Nat := 4983230072969 + 3 ^ 40 * 8260799 * 2
def baseEnd_8260799 : Nat := 4241760477180730319621783

theorem tailTrace_8260799 : CollatzResearch.WordTrace tailWord_8260799 prefixEnd_8260799 4241760477180730319621783 := by
  unfold tailWord_8260799
  simp only [CollatzResearch.WordTrace]
  refine ⟨301296091999543529992225451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200864061333029019994816967 301296091999543529992225451)
  ·
    refine ⟨451944137999315294988338177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301296091999543529992225451 451944137999315294988338177)
    ·
      refine ⟨338958103499486471241253633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451944137999315294988338177 338958103499486471241253633)
      ·
        refine ⟨254218577624614853430940225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338958103499486471241253633 254218577624614853430940225)
        ·
          refine ⟨190663933218461140073205169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254218577624614853430940225 190663933218461140073205169)
          ·
            refine ⟨142997949913845855054903877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190663933218461140073205169 142997949913845855054903877)
            ·
              refine ⟨26812115608846097822794477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142997949913845855054903877 26812115608846097822794477)
              ·
                refine ⟨10054543353317286683547929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26812115608846097822794477 10054543353317286683547929)
                ·
                  refine ⟨7540907514987965012660947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10054543353317286683547929 7540907514987965012660947)
                  ·
                    refine ⟨11311361272481947518991421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7540907514987965012660947 11311361272481947518991421)
                    ·
                      refine ⟨4241760477180730319621783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11311361272481947518991421 4241760477180730319621783)
                      ·
                        rfl

theorem cell23_8260799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_8260799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260799 prefixEnd_8260799 := by exact prefixLift 8260799
  have htrace : WordTrace (prefixWord ++ tailWord_8260799) baseStart_8260799 baseEnd_8260799 := by
    simpa [prefixWord, tailWord_8260799, baseEnd_8260799] using wordTrace_append hprefix tailTrace_8260799
  have hstable : (prefixWord ++ tailWord_8260799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260799).length < 2 ^ (prefixWord ++ tailWord_8260799).sum := by decide
  have hdescent : baseEnd_8260799 < baseStart_8260799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260805 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_8260805 : Nat := 118140960795 + 8260805 * 2 ^ 59
def prefixEnd_8260805 : Nat := 4983230072969 + 3 ^ 40 * 8260805 * 2
def baseEnd_8260805 : Nat := 4241763558064657296146755

theorem tailTrace_8260805 : CollatzResearch.WordTrace tailWord_8260805 prefixEnd_8260805 4241763558064657296146755 := by
  unfold tailWord_8260805
  simp only [CollatzResearch.WordTrace]
  refine ⟨301296310837521793016943869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200864207225014528677962579 301296310837521793016943869)
  ·
    refine ⟨112986116564070672381353951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301296310837521793016943869 112986116564070672381353951)
    ·
      refine ⟨169479174846106008572030927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112986116564070672381353951 169479174846106008572030927)
      ·
        refine ⟨254218762269159012858046391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169479174846106008572030927 254218762269159012858046391)
        ·
          refine ⟨381328143403738519287069587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254218762269159012858046391 381328143403738519287069587)
          ·
            refine ⟨571992215105607778930604381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381328143403738519287069587 571992215105607778930604381)
            ·
              refine ⟨214497080664602917098976643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 571992215105607778930604381 214497080664602917098976643)
              ·
                refine ⟨321745620996904375648464965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214497080664602917098976643 321745620996904375648464965)
                ·
                  refine ⟨60327303936919570434087181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321745620996904375648464965 60327303936919570434087181)
                  ·
                    refine ⟨22622738976344838912782693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60327303936919570434087181 22622738976344838912782693)
                    ·
                      refine ⟨4241763558064657296146755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22622738976344838912782693 4241763558064657296146755)
                      ·
                        rfl

theorem cell23_8260805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_8260805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260805 prefixEnd_8260805 := by exact prefixLift 8260805
  have htrace : WordTrace (prefixWord ++ tailWord_8260805) baseStart_8260805 baseEnd_8260805 := by
    simpa [prefixWord, tailWord_8260805, baseEnd_8260805] using wordTrace_append hprefix tailTrace_8260805
  have hstable : (prefixWord ++ tailWord_8260805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260805).length < 2 ^ (prefixWord ++ tailWord_8260805).sum := by decide
  have hdescent : baseEnd_8260805 < baseStart_8260805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260820 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_8260820 : Nat := 118140960795 + 8260820 * 2 ^ 59
def prefixEnd_8260820 : Nat := 4983230072969 + 3 ^ 40 * 8260820 * 2
def baseEnd_8260820 : Nat := 4241771260274474737459187

theorem tailTrace_8260820 : CollatzResearch.WordTrace tailWord_8260820 prefixEnd_8260820 4241771260274474737459187 := by
  unfold tailWord_8260820
  simp only [CollatzResearch.WordTrace]
  refine ⟨150648428966233725289369957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200864571954978300385826609 150648428966233725289369957)
  ·
    refine ⟨28246580431168823491756867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150648428966233725289369957 28246580431168823491756867)
    ·
      refine ⟨42369870646753235237635301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28246580431168823491756867 42369870646753235237635301)
      ·
        refine ⟨7944350746266231607056619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42369870646753235237635301 7944350746266231607056619)
        ·
          refine ⟨11916526119399347410584929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7944350746266231607056619 11916526119399347410584929)
          ·
            refine ⟨8937394589549510557938697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11916526119399347410584929 8937394589549510557938697)
            ·
              refine ⟨6703045942162132918454023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8937394589549510557938697 6703045942162132918454023)
              ·
                refine ⟨10054568913243199377681035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703045942162132918454023 10054568913243199377681035)
                ·
                  refine ⟨15081853369864799066521553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10054568913243199377681035 15081853369864799066521553)
                  ·
                    refine ⟨11311390027398599299891165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15081853369864799066521553 11311390027398599299891165)
                    ·
                      refine ⟨4241771260274474737459187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11311390027398599299891165 4241771260274474737459187)
                      ·
                        rfl

theorem cell23_8260820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_8260820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260820 prefixEnd_8260820 := by exact prefixLift 8260820
  have htrace : WordTrace (prefixWord ++ tailWord_8260820) baseStart_8260820 baseEnd_8260820 := by
    simpa [prefixWord, tailWord_8260820, baseEnd_8260820] using wordTrace_append hprefix tailTrace_8260820
  have hstable : (prefixWord ++ tailWord_8260820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260820).length < 2 ^ (prefixWord ++ tailWord_8260820).sum := by decide
  have hdescent : baseEnd_8260820 < baseStart_8260820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260825 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_8260825 : Nat := 118140960795 + 8260825 * 2 ^ 59
def prefixEnd_8260825 : Nat := 4983230072969 + 3 ^ 40 * 8260825 * 2
def baseEnd_8260825 : Nat := 4241773827677747217896663

theorem tailTrace_8260825 : CollatzResearch.WordTrace tailWord_8260825 prefixEnd_8260825 4241773827677747217896663 := by
  unfold tailWord_8260825
  simp only [CollatzResearch.WordTrace]
  refine ⟨301297040297449336432671929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200864693531632890955114619 301297040297449336432671929)
  ·
    refine ⟨225972780223087002324503947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301297040297449336432671929 225972780223087002324503947)
    ·
      refine ⟨338959170334630503486755921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225972780223087002324503947 338959170334630503486755921)
      ·
        refine ⟨254219377750972877615066941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338959170334630503486755921 254219377750972877615066941)
        ·
          refine ⟨95332266656614829105650103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254219377750972877615066941 95332266656614829105650103)
          ·
            refine ⟨142998399984922243658475155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95332266656614829105650103 142998399984922243658475155)
            ·
              refine ⟨214497599977383365487712733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142998399984922243658475155 214497599977383365487712733)
              ·
                refine ⟨80436599991518762057892275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214497599977383365487712733 80436599991518762057892275)
                ·
                  refine ⟨120654899987278143086838413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80436599991518762057892275 120654899987278143086838413)
                  ·
                    refine ⟨45245587495229303657564405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120654899987278143086838413 45245587495229303657564405)
                    ·
                      refine ⟨4241773827677747217896663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45245587495229303657564405 4241773827677747217896663)
                      ·
                        rfl

theorem cell23_8260825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_8260825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260825 prefixEnd_8260825 := by exact prefixLift 8260825
  have htrace : WordTrace (prefixWord ++ tailWord_8260825) baseStart_8260825 baseEnd_8260825 := by
    simpa [prefixWord, tailWord_8260825, baseEnd_8260825] using wordTrace_append hprefix tailTrace_8260825
  have hstable : (prefixWord ++ tailWord_8260825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260825).length < 2 ^ (prefixWord ++ tailWord_8260825).sum := by decide
  have hdescent : baseEnd_8260825 < baseStart_8260825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260892 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_8260892 : Nat := 118140960795 + 8260892 * 2 ^ 59
def prefixEnd_8260892 : Nat := 4983230072969 + 3 ^ 40 * 8260892 * 2
def baseEnd_8260892 : Nat := 1413936076960532818586285

theorem tailTrace_8260892 : CollatzResearch.WordTrace tailWord_8260892 prefixEnd_8260892 1413936076960532818586285 := by
  unfold tailWord_8260892
  simp only [CollatzResearch.WordTrace]
  refine ⟨150649741994103303437680465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200866322658804404583573953 150649741994103303437680465)
  ·
    refine ⟨112987306495577477578260349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150649741994103303437680465 112987306495577477578260349)
    ·
      refine ⟨42370239935841554091847631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112987306495577477578260349 42370239935841554091847631)
      ·
        refine ⟨63555359903762331137771447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42370239935841554091847631 63555359903762331137771447)
        ·
          refine ⟨95333039855643496706657171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63555359903762331137771447 95333039855643496706657171)
          ·
            refine ⟨142999559783465245059985757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95333039855643496706657171 142999559783465245059985757)
            ·
              refine ⟨53624834918799466897494659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142999559783465245059985757 53624834918799466897494659)
              ·
                refine ⟨80437252378199200346241989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53624834918799466897494659 80437252378199200346241989)
                ·
                  refine ⟨15081984820912350064920373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80437252378199200346241989 15081984820912350064920373)
                  ·
                    refine ⟨1413936076960532818586285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15081984820912350064920373 1413936076960532818586285)
                    ·
                      rfl

theorem cell23_8260892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_8260892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260892 prefixEnd_8260892 := by exact prefixLift 8260892
  have htrace : WordTrace (prefixWord ++ tailWord_8260892) baseStart_8260892 baseEnd_8260892 := by
    simpa [prefixWord, tailWord_8260892, baseEnd_8260892] using wordTrace_append hprefix tailTrace_8260892
  have hstable : (prefixWord ++ tailWord_8260892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260892).length < 2 ^ (prefixWord ++ tailWord_8260892).sum := by decide
  have hdescent : baseEnd_8260892 < baseStart_8260892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260896 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 7]
def baseStart_8260896 : Nat := 118140960795 + 8260896 * 2 ^ 59
def prefixEnd_8260896 : Nat := 4983230072969 + 3 ^ 40 * 8260896 * 2
def baseEnd_8260896 : Nat := 471312253867135160012093

theorem tailTrace_8260896 : CollatzResearch.WordTrace tailWord_8260896 prefixEnd_8260896 471312253867135160012093 := by
  unfold tailWord_8260896
  simp only [CollatzResearch.WordTrace]
  refine ⟨150649814940096057779253271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200866419920128077039004361 150649814940096057779253271)
  ·
    refine ⟨225974722410144086668879907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150649814940096057779253271 225974722410144086668879907)
    ·
      refine ⟨338962083615216130003319861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225974722410144086668879907 338962083615216130003319861)
      ·
        refine ⟨31777695338926512187811237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338962083615216130003319861 31777695338926512187811237)
        ·
          refine ⟨5958317876048721035214607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31777695338926512187811237 5958317876048721035214607)
          ·
            refine ⟨8937476814073081552821911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5958317876048721035214607 8937476814073081552821911)
            ·
              refine ⟨13406215221109622329232867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8937476814073081552821911 13406215221109622329232867)
              ·
                refine ⟨20109322831664433493849301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13406215221109622329232867 20109322831664433493849301)
                ·
                  refine ⟨471312253867135160012093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20109322831664433493849301 471312253867135160012093)
                  ·
                    rfl

theorem cell23_8260896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 7].length) (baseStart_8260896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260896 prefixEnd_8260896 := by exact prefixLift 8260896
  have htrace : WordTrace (prefixWord ++ tailWord_8260896) baseStart_8260896 baseEnd_8260896 := by
    simpa [prefixWord, tailWord_8260896, baseEnd_8260896] using wordTrace_append hprefix tailTrace_8260896
  have hstable : (prefixWord ++ tailWord_8260896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260896).length < 2 ^ (prefixWord ++ tailWord_8260896).sum := by decide
  have hdescent : baseEnd_8260896 < baseStart_8260896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260905 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 3, 10]
def baseStart_8260905 : Nat := 118140960795 + 8260905 * 2 ^ 59
def prefixEnd_8260905 : Nat := 4983230072969 + 3 ^ 40 * 8260905 * 2
def baseEnd_8260905 : Nat := 1413938302043368968298765

theorem tailTrace_8260905 : CollatzResearch.WordTrace tailWord_8260905 prefixEnd_8260905 1413938302043368968298765 := by
  unfold tailWord_8260905
  simp only [CollatzResearch.WordTrace]
  refine ⟨301299958137159510095584169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200866638758106340063722779 301299958137159510095584169)
  ·
    refine ⟨225974968602869632571688127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301299958137159510095584169 225974968602869632571688127)
    ·
      refine ⟨338962452904304448857532191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225974968602869632571688127 338962452904304448857532191)
      ·
        refine ⟨508443679356456673286298287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338962452904304448857532191 508443679356456673286298287)
        ·
          refine ⟨762665519034685009929447431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508443679356456673286298287 762665519034685009929447431)
          ·
            refine ⟨1143998278552027514894171147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762665519034685009929447431 1143998278552027514894171147)
            ·
              refine ⟨1715997417828041272341256721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143998278552027514894171147 1715997417828041272341256721)
              ·
                refine ⟨1286998063371030954255942541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1715997417828041272341256721 1286998063371030954255942541)
                ·
                  refine ⟨482624273764136607845978453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1286998063371030954255942541 482624273764136607845978453)
                  ·
                    refine ⟨1413938302043368968298765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 482624273764136607845978453 1413938302043368968298765)
                    ·
                      rfl

theorem cell23_8260905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_8260905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260905 prefixEnd_8260905 := by exact prefixLift 8260905
  have htrace : WordTrace (prefixWord ++ tailWord_8260905) baseStart_8260905 baseEnd_8260905 := by
    simpa [prefixWord, tailWord_8260905, baseEnd_8260905] using wordTrace_append hprefix tailTrace_8260905
  have hstable : (prefixWord ++ tailWord_8260905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260905).length < 2 ^ (prefixWord ++ tailWord_8260905).sum := by decide
  have hdescent : baseEnd_8260905 < baseStart_8260905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260912 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 4]
def baseStart_8260912 : Nat := 118140960795 + 8260912 * 2 ^ 59
def prefixEnd_8260912 : Nat := 4983230072969 + 3 ^ 40 * 8260912 * 2
def baseEnd_8260912 : Nat := 4241818500494688377508763

theorem tailTrace_8260912 : CollatzResearch.WordTrace tailWord_8260912 prefixEnd_8260912 4241818500494688377508763 := by
  unfold tailWord_8260912
  simp only [CollatzResearch.WordTrace]
  refine ⟨150650106724067075145544495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200866808965422766860725993 150650106724067075145544495)
  ·
    refine ⟨225975160086100612718316743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150650106724067075145544495 225975160086100612718316743)
    ·
      refine ⟨338962740129150919077475115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225975160086100612718316743 338962740129150919077475115)
      ·
        refine ⟨508444110193726378616212673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338962740129150919077475115 508444110193726378616212673)
        ·
          refine ⟨381333082645294783962159505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508444110193726378616212673 381333082645294783962159505)
          ·
            refine ⟨285999811983971087971619629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381333082645294783962159505 285999811983971087971619629)
            ·
              refine ⟨107249929493989157989357361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285999811983971087971619629 107249929493989157989357361)
              ·
                refine ⟨80437447120491868492018021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107249929493989157989357361 80437447120491868492018021)
                ·
                  refine ⟨15082021335092225342253379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80437447120491868492018021 15082021335092225342253379)
                  ·
                    refine ⟨22623032002638338013380069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15082021335092225342253379 22623032002638338013380069)
                    ·
                      refine ⟨4241818500494688377508763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22623032002638338013380069 4241818500494688377508763)
                      ·
                        rfl

theorem cell23_8260912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_8260912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260912 prefixEnd_8260912 := by exact prefixLift 8260912
  have htrace : WordTrace (prefixWord ++ tailWord_8260912) baseStart_8260912 baseEnd_8260912 := by
    simpa [prefixWord, tailWord_8260912, baseEnd_8260912] using wordTrace_append hprefix tailTrace_8260912
  have hstable : (prefixWord ++ tailWord_8260912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260912).length < 2 ^ (prefixWord ++ tailWord_8260912).sum := by decide
  have hdescent : baseEnd_8260912 < baseStart_8260912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8260942 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_8260942 : Nat := 118140960795 + 8260942 * 2 ^ 59
def prefixEnd_8260942 : Nat := 4983230072969 + 3 ^ 40 * 8260942 * 2
def baseEnd_8260942 : Nat := 4241833904914323260133625

theorem tailTrace_8260942 : CollatzResearch.WordTrace tailWord_8260942 prefixEnd_8260942 4241833904914323260133625 := by
  unfold tailWord_8260942
  simp only [CollatzResearch.WordTrace]
  refine ⟨37662663454753183176835135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200867538425350310276454053 37662663454753183176835135)
  ·
    refine ⟨56493995182129774765252703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37662663454753183176835135 56493995182129774765252703)
    ·
      refine ⟨84740992773194662147879055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56493995182129774765252703 84740992773194662147879055)
      ·
        refine ⟨127111489159791993221818583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84740992773194662147879055 127111489159791993221818583)
        ·
          refine ⟨190667233739687989832727875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127111489159791993221818583 190667233739687989832727875)
          ·
            refine ⟨286000850609531984749091813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190667233739687989832727875 286000850609531984749091813)
            ·
              refine ⟨53625159489287247140454715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286000850609531984749091813 53625159489287247140454715)
              ·
                refine ⟨80437739233930870710682073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53625159489287247140454715 80437739233930870710682073)
                ·
                  refine ⟨60328304425448153033011555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80437739233930870710682073 60328304425448153033011555)
                  ·
                    refine ⟨90492456638172229549517333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60328304425448153033011555 90492456638172229549517333)
                    ·
                      refine ⟨4241833904914323260133625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90492456638172229549517333 4241833904914323260133625)
                      ·
                        rfl

theorem cell23_8260942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_8260942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8260942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8260942 prefixEnd_8260942 := by exact prefixLift 8260942
  have htrace : WordTrace (prefixWord ++ tailWord_8260942) baseStart_8260942 baseEnd_8260942 := by
    simpa [prefixWord, tailWord_8260942, baseEnd_8260942] using wordTrace_append hprefix tailTrace_8260942
  have hstable : (prefixWord ++ tailWord_8260942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8260942).length < 2 ^ (prefixWord ++ tailWord_8260942).sum := by decide
  have hdescent : baseEnd_8260942 < baseStart_8260942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8260942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261013 : List Nat := [1, 3, 2, 1, 1, 2, 4, 4, 1, 1, 3]
def baseStart_8261013 : Nat := 118140960795 + 8261013 * 2 ^ 59
def prefixEnd_8261013 : Nat := 4983230072969 + 3 ^ 40 * 8261013 * 2
def baseEnd_8261013 : Nat := 4241870362040792482345799

theorem tailTrace_8261013 : CollatzResearch.WordTrace tailWord_8261013 prefixEnd_8261013 4241870362040792482345799 := by
  unfold tailWord_8261013
  simp only [CollatzResearch.WordTrace]
  refine ⟨301303897220768244540515693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200869264813845496360343795 301303897220768244540515693)
  ·
    refine ⟨112988961457788091702693385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301303897220768244540515693 112988961457788091702693385)
    ·
      refine ⟨84741721093341068777020039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112988961457788091702693385 84741721093341068777020039)
      ·
        refine ⟨127112581640011603165530059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84741721093341068777020039 127112581640011603165530059)
        ·
          refine ⟨190668872460017404748295089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127112581640011603165530059 190668872460017404748295089)
          ·
            refine ⟨143001654345013053561221317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190668872460017404748295089 143001654345013053561221317)
            ·
              refine ⟨26812810189689947542728997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143001654345013053561221317 26812810189689947542728997)
              ·
                refine ⟨5027401910566865164261687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26812810189689947542728997 5027401910566865164261687)
                ·
                  refine ⟨7541102865850297746392531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027401910566865164261687 7541102865850297746392531)
                  ·
                    refine ⟨11311654298775446619588797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7541102865850297746392531 11311654298775446619588797)
                    ·
                      refine ⟨4241870362040792482345799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11311654298775446619588797 4241870362040792482345799)
                      ·
                        rfl

theorem cell23_8261013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_8261013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261013 prefixEnd_8261013 := by exact prefixLift 8261013
  have htrace : WordTrace (prefixWord ++ tailWord_8261013) baseStart_8261013 baseEnd_8261013 := by
    simpa [prefixWord, tailWord_8261013, baseEnd_8261013] using wordTrace_append hprefix tailTrace_8261013
  have hstable : (prefixWord ++ tailWord_8261013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261013).length < 2 ^ (prefixWord ++ tailWord_8261013).sum := by decide
  have hdescent : baseEnd_8261013 < baseStart_8261013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261039 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 3]
def baseStart_8261039 : Nat := 118140960795 + 8261039 * 2 ^ 59
def prefixEnd_8261039 : Nat := 4983230072969 + 3 ^ 40 * 8261039 * 2
def baseEnd_8261039 : Nat := 4241883712537809380620679

theorem tailTrace_8261039 : CollatzResearch.WordTrace tailWord_8261039 prefixEnd_8261039 4241883712537809380620679 := by
  unfold tailWord_8261039
  simp only [CollatzResearch.WordTrace]
  refine ⟨301304845518674050980962171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200869897012449367320641447 301304845518674050980962171)
  ·
    refine ⟨451957268278011076471443257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301304845518674050980962171 451957268278011076471443257)
    ·
      refine ⟨338967951208508307353582443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451957268278011076471443257 338967951208508307353582443)
      ·
        refine ⟨508451926812762461030373665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338967951208508307353582443 508451926812762461030373665)
        ·
          refine ⟨381338945109571845772780249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508451926812762461030373665 381338945109571845772780249)
          ·
            refine ⟨286004208832178884329585187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381338945109571845772780249 286004208832178884329585187)
            ·
              refine ⟨429006313248268326494377781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286004208832178884329585187 429006313248268326494377781)
              ·
                refine ⟨40219341867025155608847917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 429006313248268326494377781 40219341867025155608847917)
                ·
                  refine ⟨15082253200134433353317969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40219341867025155608847917 15082253200134433353317969)
                  ·
                    refine ⟨11311689900100825014988477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15082253200134433353317969 11311689900100825014988477)
                    ·
                      refine ⟨4241883712537809380620679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11311689900100825014988477 4241883712537809380620679)
                      ·
                        rfl

theorem cell23_8261039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 3].length) (baseStart_8261039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261039 prefixEnd_8261039 := by exact prefixLift 8261039
  have htrace : WordTrace (prefixWord ++ tailWord_8261039) baseStart_8261039 baseEnd_8261039 := by
    simpa [prefixWord, tailWord_8261039, baseEnd_8261039] using wordTrace_append hprefix tailTrace_8261039
  have hstable : (prefixWord ++ tailWord_8261039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261039).length < 2 ^ (prefixWord ++ tailWord_8261039).sum := by decide
  have hdescent : baseEnd_8261039 < baseStart_8261039 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261056 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 3]
def baseStart_8261056 : Nat := 118140960795 + 8261056 * 2 ^ 59
def prefixEnd_8261056 : Nat := 4983230072969 + 3 ^ 40 * 8261056 * 2
def baseEnd_8261056 : Nat := 4241892441708935814108101

theorem tailTrace_8261056 : CollatzResearch.WordTrace tailWord_8261056 prefixEnd_8261056 4241892441708935814108101 := by
  unfold tailWord_8261056
  simp only [CollatzResearch.WordTrace]
  refine ⟨150652732779806231442165511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200870310373074975256220681 150652732779806231442165511)
  ·
    refine ⟨225979099169709347163248267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150652732779806231442165511 225979099169709347163248267)
    ·
      refine ⟨338968648754564020744872401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225979099169709347163248267 338968648754564020744872401)
      ·
        refine ⟨254226486565923015558654301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338968648754564020744872401 254226486565923015558654301)
        ·
          refine ⟨95334932462221130834495363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254226486565923015558654301 95334932462221130834495363)
          ·
            refine ⟨143002398693331696251743045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95334932462221130834495363 143002398693331696251743045)
            ·
              refine ⟨26812949754999693047201821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143002398693331696251743045 26812949754999693047201821)
              ·
                refine ⟨10054856158124884892700683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26812949754999693047201821 10054856158124884892700683)
                ·
                  refine ⟨15082284237187327339051025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10054856158124884892700683 15082284237187327339051025)
                  ·
                    refine ⟨11311713177890495504288269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15082284237187327339051025 11311713177890495504288269)
                    ·
                      refine ⟨4241892441708935814108101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11311713177890495504288269 4241892441708935814108101)
                      ·
                        rfl

theorem cell23_8261056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_8261056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261056 prefixEnd_8261056 := by exact prefixLift 8261056
  have htrace : WordTrace (prefixWord ++ tailWord_8261056) baseStart_8261056 baseEnd_8261056 := by
    simpa [prefixWord, tailWord_8261056, baseEnd_8261056] using wordTrace_append hprefix tailTrace_8261056
  have hstable : (prefixWord ++ tailWord_8261056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261056).length < 2 ^ (prefixWord ++ tailWord_8261056).sum := by decide
  have hdescent : baseEnd_8261056 < baseStart_8261056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261070 : List Nat := [4, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2]
def baseStart_8261070 : Nat := 118140960795 + 8261070 * 2 ^ 59
def prefixEnd_8261070 : Nat := 4983230072969 + 3 ^ 40 * 8261070 * 2
def baseEnd_8261070 : Nat := 4241899630438098759333037

theorem tailTrace_8261070 : CollatzResearch.WordTrace tailWord_8261070 prefixEnd_8261070 4241899630438098759333037 := by
  unfold tailWord_8261070
  simp only [CollatzResearch.WordTrace]
  refine ⟨37663247022695217909417583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200870650787707828850227109 37663247022695217909417583)
  ·
    refine ⟨56494870534042826864126375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37663247022695217909417583 56494870534042826864126375)
    ·
      refine ⟨84742305801064240296189563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56494870534042826864126375 84742305801064240296189563)
      ·
        refine ⟨127113458701596360444284345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84742305801064240296189563 127113458701596360444284345)
        ·
          refine ⟨95335094026197270333213259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127113458701596360444284345 95335094026197270333213259)
          ·
            refine ⟨143002641039295905499819889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95335094026197270333213259 143002641039295905499819889)
            ·
              refine ⟨107251980779471929124864917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143002641039295905499819889 107251980779471929124864917)
              ·
                refine ⟨5027436599037746677728043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107251980779471929124864917 5027436599037746677728043)
                ·
                  refine ⟨7541154898556620016592065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027436599037746677728043 7541154898556620016592065)
                  ·
                    refine ⟨5655866173917465012444049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7541154898556620016592065 5655866173917465012444049)
                    ·
                      refine ⟨4241899630438098759333037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655866173917465012444049 4241899630438098759333037)
                      ·
                        rfl

theorem cell23_8261070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_8261070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261070 prefixEnd_8261070 := by exact prefixLift 8261070
  have htrace : WordTrace (prefixWord ++ tailWord_8261070) baseStart_8261070 baseEnd_8261070 := by
    simpa [prefixWord, tailWord_8261070, baseEnd_8261070] using wordTrace_append hprefix tailTrace_8261070
  have hstable : (prefixWord ++ tailWord_8261070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261070).length < 2 ^ (prefixWord ++ tailWord_8261070).sum := by decide
  have hdescent : baseEnd_8261070 < baseStart_8261070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261072 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 1, 9]
def baseStart_8261072 : Nat := 118140960795 + 8261072 * 2 ^ 59
def prefixEnd_8261072 : Nat := 4983230072969 + 3 ^ 40 * 8261072 * 2
def baseEnd_8261072 : Nat := 1413966885799802583836009

theorem tailTrace_8261072 : CollatzResearch.WordTrace tailWord_8261072 prefixEnd_8261072 1413966885799802583836009 := by
  unfold tailWord_8261072
  simp only [CollatzResearch.WordTrace]
  refine ⟨150653024563777248808456735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200870699418369665077942313 150653024563777248808456735)
  ·
    refine ⟨225979536845665873212685103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150653024563777248808456735 225979536845665873212685103)
    ·
      refine ⟨338969305268498809819027655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225979536845665873212685103 338969305268498809819027655)
      ·
        refine ⟨508453957902748214728541483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338969305268498809819027655 508453957902748214728541483)
        ·
          refine ⟨762680936854122322092812225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508453957902748214728541483 762680936854122322092812225)
          ·
            refine ⟨572010702640591741569609169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762680936854122322092812225 572010702640591741569609169)
            ·
              refine ⟨429008026980443806177206877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572010702640591741569609169 429008026980443806177206877)
              ·
                refine ⟨160878010117666427316452579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429008026980443806177206877 160878010117666427316452579)
                ·
                  refine ⟨241317015176499640974678869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160878010117666427316452579 241317015176499640974678869)
                  ·
                    refine ⟨1413966885799802583836009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 241317015176499640974678869 1413966885799802583836009)
                    ·
                      rfl

theorem cell23_8261072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_8261072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261072 prefixEnd_8261072 := by exact prefixLift 8261072
  have htrace : WordTrace (prefixWord ++ tailWord_8261072) baseStart_8261072 baseEnd_8261072 := by
    simpa [prefixWord, tailWord_8261072, baseEnd_8261072] using wordTrace_append hprefix tailTrace_8261072
  have hstable : (prefixWord ++ tailWord_8261072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261072).length < 2 ^ (prefixWord ++ tailWord_8261072).sum := by decide
  have hdescent : baseEnd_8261072 < baseStart_8261072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261076 : List Nat := [2, 4, 1, 2, 3, 1, 2, 8]
def baseStart_8261076 : Nat := 118140960795 + 8261076 * 2 ^ 59
def prefixEnd_8261076 : Nat := 4983230072969 + 3 ^ 40 * 8261076 * 2
def baseEnd_8261076 : Nat := 157107507826741693920667

theorem tailTrace_8261076 : CollatzResearch.WordTrace tailWord_8261076 prefixEnd_8261076 157107507826741693920667 := by
  unfold tailWord_8261076
  simp only [CollatzResearch.WordTrace]
  refine ⟨150653097509770003150029541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200870796679693337533372721 150653097509770003150029541)
  ·
    refine ⟨28247455783081875590630539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150653097509770003150029541 28247455783081875590630539)
    ·
      refine ⟨42371183674622813385945809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28247455783081875590630539 42371183674622813385945809)
      ·
        refine ⟨31778387755967110039459357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42371183674622813385945809 31778387755967110039459357)
        ·
          refine ⟨11916895408487666264797259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31778387755967110039459357 11916895408487666264797259)
          ·
            refine ⟨17875343112731499397195889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11916895408487666264797259 17875343112731499397195889)
            ·
              refine ⟨13406507334548624547896917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17875343112731499397195889 13406507334548624547896917)
              ·
                refine ⟨157107507826741693920667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13406507334548624547896917 157107507826741693920667)
                ·
                  rfl

theorem cell23_8261076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 8].length) (baseStart_8261076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261076 prefixEnd_8261076 := by exact prefixLift 8261076
  have htrace : WordTrace (prefixWord ++ tailWord_8261076) baseStart_8261076 baseEnd_8261076 := by
    simpa [prefixWord, tailWord_8261076, baseEnd_8261076] using wordTrace_append hprefix tailTrace_8261076
  have hstable : (prefixWord ++ tailWord_8261076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261076).length < 2 ^ (prefixWord ++ tailWord_8261076).sum := by decide
  have hdescent : baseEnd_8261076 < baseStart_8261076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261121 : List Nat := [1, 2, 4, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_8261121 : Nat := 118140960795 + 8261121 * 2 ^ 59
def prefixEnd_8261121 : Nat := 4983230072969 + 3 ^ 40 * 8261121 * 2
def baseEnd_8261121 : Nat := 4241925817951478059795303

theorem tailTrace_8261121 : CollatzResearch.WordTrace tailWord_8261121 prefixEnd_8261121 4241925817951478059795303 := by
  unfold tailWord_8261121
  simp only [CollatzResearch.WordTrace]
  refine ⟨301307836304376978985447217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200871890869584652656964811 301307836304376978985447217)
  ·
    refine ⟨225980877228282734239085413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301307836304376978985447217 225980877228282734239085413)
    ·
      refine ⟨42371414480303012669828515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225980877228282734239085413 42371414480303012669828515)
      ·
        refine ⟨63557121720454519004742773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42371414480303012669828515 63557121720454519004742773)
        ·
          refine ⟨5958480161292611156694635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63557121720454519004742773 5958480161292611156694635)
          ·
            refine ⟨8937720241938916735041953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5958480161292611156694635 8937720241938916735041953)
            ·
              refine ⟨6703290181454187551281465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8937720241938916735041953 6703290181454187551281465)
              ·
                refine ⟨5027467636090640663461099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6703290181454187551281465 5027467636090640663461099)
                ·
                  refine ⟨7541201454135960995191649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027467636090640663461099 7541201454135960995191649)
                  ·
                    refine ⟨5655901090601970746393737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7541201454135960995191649 5655901090601970746393737)
                    ·
                      refine ⟨4241925817951478059795303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655901090601970746393737 4241925817951478059795303)
                      ·
                        rfl

theorem cell23_8261121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_8261121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261121 prefixEnd_8261121 := by exact prefixLift 8261121
  have htrace : WordTrace (prefixWord ++ tailWord_8261121) baseStart_8261121 baseEnd_8261121 := by
    simpa [prefixWord, tailWord_8261121, baseEnd_8261121] using wordTrace_append hprefix tailTrace_8261121
  have hstable : (prefixWord ++ tailWord_8261121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261121).length < 2 ^ (prefixWord ++ tailWord_8261121).sum := by decide
  have hdescent : baseEnd_8261121 < baseStart_8261121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261129 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 1, 6, 3]
def baseStart_8261129 : Nat := 118140960795 + 8261129 * 2 ^ 59
def prefixEnd_8261129 : Nat := 4983230072969 + 3 ^ 40 * 8261129 * 2
def baseEnd_8261129 : Nat := 4241929925796714028495265

theorem tailTrace_8261129 : CollatzResearch.WordTrace tailWord_8261129 prefixEnd_8261129 4241929925796714028495265 := by
  unfold tailWord_8261129
  simp only [CollatzResearch.WordTrace]
  refine ⟨301308128088347996351738441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200872085392231997567825627 301308128088347996351738441)
  ·
    refine ⟨225981096066260997263803831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301308128088347996351738441 225981096066260997263803831)
    ·
      refine ⟨338971644099391495895705747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225981096066260997263803831 338971644099391495895705747)
      ·
        refine ⟨508457466149087243843558621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338971644099391495895705747 508457466149087243843558621)
        ·
          refine ⟨190671549805907716441334483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508457466149087243843558621 190671549805907716441334483)
          ·
            refine ⟨286007324708861574662001725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190671549805907716441334483 286007324708861574662001725)
            ·
              refine ⟨107252746765823090498250647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286007324708861574662001725 107252746765823090498250647)
              ·
                refine ⟨160879120148734635747375971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107252746765823090498250647 160879120148734635747375971)
                ·
                  refine ⟨241318680223101953621063957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160879120148734635747375971 241318680223101953621063957)
                  ·
                    refine ⟨11311813135457904075987373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 241318680223101953621063957 11311813135457904075987373)
                    ·
                      refine ⟨4241929925796714028495265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11311813135457904075987373 4241929925796714028495265)
                      ·
                        rfl

theorem cell23_8261129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6, 3].length) (baseStart_8261129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261129 prefixEnd_8261129 := by exact prefixLift 8261129
  have htrace : WordTrace (prefixWord ++ tailWord_8261129) baseStart_8261129 baseEnd_8261129 := by
    simpa [prefixWord, tailWord_8261129, baseEnd_8261129] using wordTrace_append hprefix tailTrace_8261129
  have hstable : (prefixWord ++ tailWord_8261129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261129).length < 2 ^ (prefixWord ++ tailWord_8261129).sum := by decide
  have hdescent : baseEnd_8261129 < baseStart_8261129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261139 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 4]
def baseStart_8261139 : Nat := 118140960795 + 8261139 * 2 ^ 59
def prefixEnd_8261139 : Nat := 4983230072969 + 3 ^ 40 * 8261139 * 2
def baseEnd_8261139 : Nat := 4241935060603258989370219

theorem tailTrace_8261139 : CollatzResearch.WordTrace tailWord_8261139 prefixEnd_8261139 4241935060603258989370219 := by
  unfold tailWord_8261139
  simp only [CollatzResearch.WordTrace]
  refine ⟨301308492818311768059602471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200872328545541178706401647 301308492818311768059602471)
  ·
    refine ⟨451962739227467652089403707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301308492818311768059602471 451962739227467652089403707)
    ·
      refine ⟨677944108841201478134105561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451962739227467652089403707 677944108841201478134105561)
      ·
        refine ⟨508458081630901108600579171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677944108841201478134105561 508458081630901108600579171)
        ·
          refine ⟨762687122446351662900868757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508458081630901108600579171 762687122446351662900868757)
          ·
            refine ⟨35750958864672734198478223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 762687122446351662900868757 35750958864672734198478223)
            ·
              refine ⟨53626438297009101297717335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35750958864672734198478223 53626438297009101297717335)
              ·
                refine ⟨80439657445513651946576003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53626438297009101297717335 80439657445513651946576003)
                ·
                  refine ⟨120659486168270477919864005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80439657445513651946576003 120659486168270477919864005)
                  ·
                    refine ⟨22623653656550714609974501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120659486168270477919864005 22623653656550714609974501)
                    ·
                      refine ⟨4241935060603258989370219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22623653656550714609974501 4241935060603258989370219)
                      ·
                        rfl

theorem cell23_8261139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_8261139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261139 prefixEnd_8261139 := by exact prefixLift 8261139
  have htrace : WordTrace (prefixWord ++ tailWord_8261139) baseStart_8261139 baseEnd_8261139 := by
    simpa [prefixWord, tailWord_8261139, baseEnd_8261139] using wordTrace_append hprefix tailTrace_8261139
  have hstable : (prefixWord ++ tailWord_8261139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261139).length < 2 ^ (prefixWord ++ tailWord_8261139).sum := by decide
  have hdescent : baseEnd_8261139 < baseStart_8261139 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261176 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 2, 3, 3]
def baseStart_8261176 : Nat := 118140960795 + 8261176 * 2 ^ 59
def prefixEnd_8261176 : Nat := 4983230072969 + 3 ^ 40 * 8261176 * 2
def baseEnd_8261176 : Nat := 4241954059387475344607549

theorem tailTrace_8261176 : CollatzResearch.WordTrace tailWord_8261176 prefixEnd_8261176 4241954059387475344607549 := by
  unfold tailWord_8261176
  simp only [CollatzResearch.WordTrace]
  refine ⟨150654921159588861689349691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200873228212785148919132921 150654921159588861689349691)
  ·
    refine ⟨225982381739383292534024537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150654921159588861689349691 225982381739383292534024537)
    ·
      refine ⟨169486786304537469400518403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225982381739383292534024537 169486786304537469400518403)
      ·
        refine ⟨254230179456806204100777605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169486786304537469400518403 254230179456806204100777605)
        ·
          refine ⟨47668158648151163268895801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254230179456806204100777605 47668158648151163268895801)
          ·
            refine ⟨35751118986113372451671851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47668158648151163268895801 35751118986113372451671851)
            ·
              refine ⟨53626678479170058677507777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35751118986113372451671851 53626678479170058677507777)
              ·
                refine ⟨40220008859377544008130833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53626678479170058677507777 40220008859377544008130833)
                ·
                  refine ⟨30165006644533158006098125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40220008859377544008130833 30165006644533158006098125)
                  ·
                    refine ⟨11311877491699934252286797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30165006644533158006098125 11311877491699934252286797)
                    ·
                      refine ⟨4241954059387475344607549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11311877491699934252286797 4241954059387475344607549)
                      ·
                        rfl

theorem cell23_8261176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_8261176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261176 prefixEnd_8261176 := by exact prefixLift 8261176
  have htrace : WordTrace (prefixWord ++ tailWord_8261176) baseStart_8261176 baseEnd_8261176 := by
    simpa [prefixWord, tailWord_8261176, baseEnd_8261176] using wordTrace_append hprefix tailTrace_8261176
  have hstable : (prefixWord ++ tailWord_8261176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261176).length < 2 ^ (prefixWord ++ tailWord_8261176).sum := by decide
  have hdescent : baseEnd_8261176 < baseStart_8261176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261177 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 2, 2, 2]
def baseStart_8261177 : Nat := 118140960795 + 8261177 * 2 ^ 59
def prefixEnd_8261177 : Nat := 4983230072969 + 3 ^ 40 * 8261177 * 2
def baseEnd_8261177 : Nat := 4241954572868129840695045

theorem tailTrace_8261177 : CollatzResearch.WordTrace tailWord_8261177 prefixEnd_8261177 4241954572868129840695045 := by
  unfold tailWord_8261177
  simp only [CollatzResearch.WordTrace]
  refine ⟨301309878792174100549485785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200873252528116067032990523 301309878792174100549485785)
  ·
    refine ⟨225982409094130575412114339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301309878792174100549485785 225982409094130575412114339)
    ·
      refine ⟨338973613641195863118171509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225982409094130575412114339 338973613641195863118171509)
      ·
        refine ⟨31778776278862112167328579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338973613641195863118171509 31778776278862112167328579)
        ·
          refine ⟨47668164418293168250992869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31778776278862112167328579 47668164418293168250992869)
          ·
            refine ⟨8937780828429969047061163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47668164418293168250992869 8937780828429969047061163)
            ·
              refine ⟨13406671242644953570591745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8937780828429969047061163 13406671242644953570591745)
              ·
                refine ⟨10055003431983715177943809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13406671242644953570591745 10055003431983715177943809)
                ·
                  refine ⟨7541252573987786383457857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10055003431983715177943809 7541252573987786383457857)
                  ·
                    refine ⟨5655939430490839787593393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7541252573987786383457857 5655939430490839787593393)
                    ·
                      refine ⟨4241954572868129840695045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5655939430490839787593393 4241954572868129840695045)
                      ·
                        rfl

theorem cell23_8261177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_8261177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261177 prefixEnd_8261177 := by exact prefixLift 8261177
  have htrace : WordTrace (prefixWord ++ tailWord_8261177) baseStart_8261177 baseEnd_8261177 := by
    simpa [prefixWord, tailWord_8261177, baseEnd_8261177] using wordTrace_append hprefix tailTrace_8261177
  have hstable : (prefixWord ++ tailWord_8261177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261177).length < 2 ^ (prefixWord ++ tailWord_8261177).sum := by decide
  have hdescent : baseEnd_8261177 < baseStart_8261177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261189 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_8261189 : Nat := 118140960795 + 8261189 * 2 ^ 59
def prefixEnd_8261189 : Nat := 4983230072969 + 3 ^ 40 * 8261189 * 2
def baseEnd_8261189 : Nat := 4241960734635983793744989

theorem tailTrace_8261189 : CollatzResearch.WordTrace tailWord_8261189 prefixEnd_8261189 4241960734635983793744989 := by
  unfold tailWord_8261189
  simp only [CollatzResearch.WordTrace]
  refine ⟨301310316468130626598922621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200873544312087084399281747 301310316468130626598922621)
  ·
    refine ⟨112991368675548984974595983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301310316468130626598922621 112991368675548984974595983)
    ·
      refine ⟨169487053013323477461893975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112991368675548984974595983 169487053013323477461893975)
      ·
        refine ⟨254230579519985216192840963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169487053013323477461893975 254230579519985216192840963)
        ·
          refine ⟨381345869279977824289261445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254230579519985216192840963 381345869279977824289261445)
          ·
            refine ⟨71502350489995842054236521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 381345869279977824289261445 71502350489995842054236521)
            ·
              refine ⟨53626762867496881540677391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71502350489995842054236521 53626762867496881540677391)
              ·
                refine ⟨80440144301245322311016087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53626762867496881540677391 80440144301245322311016087)
                ·
                  refine ⟨120660216451867983466524131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80440144301245322311016087 120660216451867983466524131)
                  ·
                    refine ⟨180990324677801975199786197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120660216451867983466524131 180990324677801975199786197)
                    ·
                      refine ⟨4241960734635983793744989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180990324677801975199786197 4241960734635983793744989)
                      ·
                        rfl

theorem cell23_8261189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_8261189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261189 prefixEnd_8261189 := by exact prefixLift 8261189
  have htrace : WordTrace (prefixWord ++ tailWord_8261189) baseStart_8261189 baseEnd_8261189 := by
    simpa [prefixWord, tailWord_8261189, baseEnd_8261189] using wordTrace_append hprefix tailTrace_8261189
  have hstable : (prefixWord ++ tailWord_8261189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261189).length < 2 ^ (prefixWord ++ tailWord_8261189).sum := by decide
  have hdescent : baseEnd_8261189 < baseStart_8261189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261216 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 4]
def baseStart_8261216 : Nat := 118140960795 + 8261216 * 2 ^ 59
def prefixEnd_8261216 : Nat := 4983230072969 + 3 ^ 40 * 8261216 * 2
def baseEnd_8261216 : Nat := 4241974598613655188107365

theorem tailTrace_8261216 : CollatzResearch.WordTrace tailWord_8261216 prefixEnd_8261216 4241974598613655188107365 := by
  unfold tailWord_8261216
  simp only [CollatzResearch.WordTrace]
  refine ⟨150655650619516405105077751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200874200826021873473437001 150655650619516405105077751)
  ·
    refine ⟨225983475929274607657616627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150655650619516405105077751 225983475929274607657616627)
    ·
      refine ⟨338975213893911911486424941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225983475929274607657616627 338975213893911911486424941)
      ·
        refine ⟨127115705210216966807409353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338975213893911911486424941 127115705210216966807409353)
        ·
          refine ⟨95336778907662725105557015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127115705210216966807409353 95336778907662725105557015)
          ·
            refine ⟨143005168361494087658335523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95336778907662725105557015 143005168361494087658335523)
            ·
              refine ⟨214507752542241131487503285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143005168361494087658335523 214507752542241131487503285)
              ·
                refine ⟨20110101800835106076953433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214507752542241131487503285 20110101800835106076953433)
                ·
                  refine ⟨15082576350626329557715075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20110101800835106076953433 15082576350626329557715075)
                  ·
                    refine ⟨22623864525939494336572613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15082576350626329557715075 22623864525939494336572613)
                    ·
                      refine ⟨4241974598613655188107365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22623864525939494336572613 4241974598613655188107365)
                      ·
                        rfl

theorem cell23_8261216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_8261216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261216 prefixEnd_8261216 := by exact prefixLift 8261216
  have htrace : WordTrace (prefixWord ++ tailWord_8261216) baseStart_8261216 baseEnd_8261216 := by
    simpa [prefixWord, tailWord_8261216, baseEnd_8261216] using wordTrace_append hprefix tailTrace_8261216
  have hstable : (prefixWord ++ tailWord_8261216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261216).length < 2 ^ (prefixWord ++ tailWord_8261216).sum := by decide
  have hdescent : baseEnd_8261216 < baseStart_8261216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261294 : List Nat := [4, 1, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_8261294 : Nat := 118140960795 + 8261294 * 2 ^ 59
def prefixEnd_8261294 : Nat := 4983230072969 + 3 ^ 40 * 8261294 * 2
def baseEnd_8261294 : Nat := 1414004883368235294310669

theorem tailTrace_8261294 : CollatzResearch.WordTrace tailWord_8261294 prefixEnd_8261294 1414004883368235294310669 := by
  unfold tailWord_8261294
  simp only [CollatzResearch.WordTrace]
  refine ⟨37664268266593778691436867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200876097421833486354329957 37664268266593778691436867)
  ·
    refine ⟨56496402399890668037155301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37664268266593778691436867 56496402399890668037155301)
    ·
      refine ⟨10593075449979500256966619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56496402399890668037155301 10593075449979500256966619)
      ·
        refine ⟨15889613174969250385449929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10593075449979500256966619 15889613174969250385449929)
        ·
          refine ⟨11917209881226937789087447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15889613174969250385449929 11917209881226937789087447)
          ·
            refine ⟨17875814821840406683631171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11917209881226937789087447 17875814821840406683631171)
            ·
              refine ⟨26813722232760610025446757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17875814821840406683631171 26813722232760610025446757)
              ·
                refine ⟨5027572918642614379771267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26813722232760610025446757 5027572918642614379771267)
                ·
                  refine ⟨7541359377963921569656901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027572918642614379771267 7541359377963921569656901)
                  ·
                    refine ⟨1414004883368235294310669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7541359377963921569656901 1414004883368235294310669)
                    ·
                      rfl

theorem cell23_8261294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_8261294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261294 prefixEnd_8261294 := by exact prefixLift 8261294
  have htrace : WordTrace (prefixWord ++ tailWord_8261294) baseStart_8261294 baseEnd_8261294 := by
    simpa [prefixWord, tailWord_8261294, baseEnd_8261294] using wordTrace_append hprefix tailTrace_8261294
  have hstable : (prefixWord ++ tailWord_8261294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261294).length < 2 ^ (prefixWord ++ tailWord_8261294).sum := by decide
  have hdescent : baseEnd_8261294 < baseStart_8261294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261357 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_8261357 : Nat := 118140960795 + 8261357 * 2 ^ 59
def prefixEnd_8261357 : Nat := 4983230072969 + 3 ^ 40 * 8261357 * 2
def baseEnd_8261357 : Nat := 4242046999385939136444217

theorem tailTrace_8261357 : CollatzResearch.WordTrace tailWord_8261357 prefixEnd_8261357 4242046999385939136444217 := by
  unfold tailWord_8261357
  simp only [CollatzResearch.WordTrace]
  refine ⟨301316443931521991291038325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200877629287681327527358883 301316443931521991291038325)
  ·
    refine ⟨28248416618580186683534843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301316443931521991291038325 28248416618580186683534843)
    ·
      refine ⟨42372624927870280025302265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28248416618580186683534843 42372624927870280025302265)
      ·
        refine ⟨31779468695902710018976699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42372624927870280025302265 31779468695902710018976699)
        ·
          refine ⟨47669203043854065028465049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31779468695902710018976699 47669203043854065028465049)
          ·
            refine ⟨35751902282890548771348787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47669203043854065028465049 35751902282890548771348787)
            ·
              refine ⟨53627853424335823157023181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35751902282890548771348787 53627853424335823157023181)
              ·
                refine ⟨20110445034125933683883693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53627853424335823157023181 20110445034125933683883693)
                ·
                  refine ⟨7541416887797225131456385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20110445034125933683883693 7541416887797225131456385)
                  ·
                    refine ⟨5656062665847918848592289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7541416887797225131456385 5656062665847918848592289)
                    ·
                      refine ⟨4242046999385939136444217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656062665847918848592289 4242046999385939136444217)
                      ·
                        rfl

theorem cell23_8261357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_8261357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261357 prefixEnd_8261357 := by exact prefixLift 8261357
  have htrace : WordTrace (prefixWord ++ tailWord_8261357) baseStart_8261357 baseEnd_8261357 := by
    simpa [prefixWord, tailWord_8261357, baseEnd_8261357] using wordTrace_append hprefix tailTrace_8261357
  have hstable : (prefixWord ++ tailWord_8261357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261357).length < 2 ^ (prefixWord ++ tailWord_8261357).sum := by decide
  have hdescent : baseEnd_8261357 < baseStart_8261357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261373 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_8261373 : Nat := 118140960795 + 8261373 * 2 ^ 59
def prefixEnd_8261373 : Nat := 4983230072969 + 3 ^ 40 * 8261373 * 2
def baseEnd_8261373 : Nat := 4242055215076411073844143

theorem tailTrace_8261373 : CollatzResearch.WordTrace tailWord_8261373 prefixEnd_8261373 4242055215076411073844143 := by
  unfold tailWord_8261373
  simp only [CollatzResearch.WordTrace]
  refine ⟨301317027499464026023620773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200878018332976017349080515 301317027499464026023620773)
  ·
    refine ⟨56496942656149504879428895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301317027499464026023620773 56496942656149504879428895)
    ·
      refine ⟨84745413984224257319143343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56496942656149504879428895 84745413984224257319143343)
      ·
        refine ⟨127118120976336385978715015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84745413984224257319143343 127118120976336385978715015)
        ·
          refine ⟨190677181464504578968072523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127118120976336385978715015 190677181464504578968072523)
          ·
            refine ⟨286015772196756868452108785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190677181464504578968072523 286015772196756868452108785)
            ·
              refine ⟨214511829147567651339081589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286015772196756868452108785 214511829147567651339081589)
              ·
                refine ⟨20110483982584467313038899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214511829147567651339081589 20110483982584467313038899)
                ·
                  refine ⟨30165725973876700969558349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20110483982584467313038899 30165725973876700969558349)
                  ·
                    refine ⟨11312147240203762863584381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30165725973876700969558349 11312147240203762863584381)
                    ·
                      refine ⟨4242055215076411073844143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11312147240203762863584381 4242055215076411073844143)
                      ·
                        rfl

theorem cell23_8261373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_8261373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261373 prefixEnd_8261373 := by exact prefixLift 8261373
  have htrace : WordTrace (prefixWord ++ tailWord_8261373) baseStart_8261373 baseEnd_8261373 := by
    simpa [prefixWord, tailWord_8261373, baseEnd_8261373] using wordTrace_append hprefix tailTrace_8261373
  have hstable : (prefixWord ++ tailWord_8261373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261373).length < 2 ^ (prefixWord ++ tailWord_8261373).sum := by decide
  have hdescent : baseEnd_8261373 < baseStart_8261373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261380 : List Nat := [2, 3, 2, 2, 1, 4, 2, 7]
def baseStart_8261380 : Nat := 118140960795 + 8261380 * 2 ^ 59
def prefixEnd_8261380 : Nat := 4983230072969 + 3 ^ 40 * 8261380 * 2
def baseEnd_8261380 : Nat := 157113289238555279498393

theorem tailTrace_8261380 : CollatzResearch.WordTrace tailWord_8261380 prefixEnd_8261380 157113289238555279498393 := by
  unfold tailWord_8261380
  simp only [CollatzResearch.WordTrace]
  refine ⟨150658641405219333109562797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200878188540292444146083729 150658641405219333109562797)
  ·
    refine ⟨56496990526957249916086049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150658641405219333109562797 56496990526957249916086049)
    ·
      refine ⟨42372742895217937437064537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56496990526957249916086049 42372742895217937437064537)
      ·
        refine ⟨31779557171413453077798403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42372742895217937437064537 31779557171413453077798403)
        ·
          refine ⟨47669335757120179616697605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31779557171413453077798403 47669335757120179616697605)
          ·
            refine ⟨8938000454460033678130801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47669335757120179616697605 8938000454460033678130801)
            ·
              refine ⟨6703500340845025258598101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8938000454460033678130801 6703500340845025258598101)
              ·
                refine ⟨157113289238555279498393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6703500340845025258598101 157113289238555279498393)
                ·
                  rfl

theorem cell23_8261380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 7].length) (baseStart_8261380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261380 prefixEnd_8261380 := by exact prefixLift 8261380
  have htrace : WordTrace (prefixWord ++ tailWord_8261380) baseStart_8261380 baseEnd_8261380 := by
    simpa [prefixWord, tailWord_8261380, baseEnd_8261380] using wordTrace_append hprefix tailTrace_8261380
  have hstable : (prefixWord ++ tailWord_8261380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261380).length < 2 ^ (prefixWord ++ tailWord_8261380).sum := by decide
  have hdescent : baseEnd_8261380 < baseStart_8261380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261390 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_8261390 : Nat := 118140960795 + 8261390 * 2 ^ 59
def prefixEnd_8261390 : Nat := 4983230072969 + 3 ^ 40 * 8261390 * 2
def baseEnd_8261390 : Nat := 4242063944247537507331565

theorem tailTrace_8261390 : CollatzResearch.WordTrace tailWord_8261390 prefixEnd_8261390 4242063944247537507331565 := by
  unfold tailWord_8261390
  simp only [CollatzResearch.WordTrace]
  refine ⟨37664705942550304740873703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200878431693601625284659749 37664705942550304740873703)
  ·
    refine ⟨56497058913825457111310555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37664705942550304740873703 56497058913825457111310555)
    ·
      refine ⟨84745588370738185666965833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56497058913825457111310555 84745588370738185666965833)
      ·
        refine ⟨63559191278053639250224375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84745588370738185666965833 63559191278053639250224375)
        ·
          refine ⟨95338786917080458875336563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63559191278053639250224375 95338786917080458875336563)
          ·
            refine ⟨143008180375620688313004845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95338786917080458875336563 143008180375620688313004845)
            ·
              refine ⟨53628067640857758117376817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143008180375620688313004845 53628067640857758117376817)
              ·
                refine ⟨40221050730643318588032613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53628067640857758117376817 40221050730643318588032613)
                ·
                  refine ⟨7541447011995622235256115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40221050730643318588032613 7541447011995622235256115)
                  ·
                    refine ⟨11312170517993433352884173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7541447011995622235256115 11312170517993433352884173)
                    ·
                      refine ⟨4242063944247537507331565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11312170517993433352884173 4242063944247537507331565)
                      ·
                        rfl

theorem cell23_8261390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_8261390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261390 prefixEnd_8261390 := by exact prefixLift 8261390
  have htrace : WordTrace (prefixWord ++ tailWord_8261390) baseStart_8261390 baseEnd_8261390 := by
    simpa [prefixWord, tailWord_8261390, baseEnd_8261390] using wordTrace_append hprefix tailTrace_8261390
  have hstable : (prefixWord ++ tailWord_8261390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261390).length < 2 ^ (prefixWord ++ tailWord_8261390).sum := by decide
  have hdescent : baseEnd_8261390 < baseStart_8261390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261434 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2]
def baseStart_8261434 : Nat := 118140960795 + 8261434 * 2 ^ 59
def prefixEnd_8261434 : Nat := 4983230072969 + 3 ^ 40 * 8261434 * 2
def baseEnd_8261434 : Nat := 4242086537396335335181363

theorem tailTrace_8261434 : CollatzResearch.WordTrace tailWord_8261434 prefixEnd_8261434 4242086537396335335181363 := by
  unfold tailWord_8261434
  simp only [CollatzResearch.WordTrace]
  refine ⟨75329813088060758360397839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200879501568162022294394237 75329813088060758360397839)
  ·
    refine ⟨112994719632091137540596759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75329813088060758360397839 112994719632091137540596759)
    ·
      refine ⟨169492079448136706310895139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112994719632091137540596759 169492079448136706310895139)
      ·
        refine ⟨254238119172205059466342709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169492079448136706310895139 254238119172205059466342709)
        ·
          refine ⟨23834823672394224324969629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254238119172205059466342709 23834823672394224324969629)
          ·
            refine ⟨8938058877147834121863611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23834823672394224324969629 8938058877147834121863611)
            ·
              refine ⟨13407088315721751182795417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8938058877147834121863611 13407088315721751182795417)
              ·
                refine ⟨10055316236791313387096563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13407088315721751182795417 10055316236791313387096563)
                ·
                  refine ⟨15082974355186970080644845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10055316236791313387096563 15082974355186970080644845)
                  ·
                    refine ⟨5656115383195113780241817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15082974355186970080644845 5656115383195113780241817)
                    ·
                      refine ⟨4242086537396335335181363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656115383195113780241817 4242086537396335335181363)
                      ·
                        rfl

theorem cell23_8261434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2].length) (baseStart_8261434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261434 prefixEnd_8261434 := by exact prefixLift 8261434
  have htrace : WordTrace (prefixWord ++ tailWord_8261434) baseStart_8261434 baseEnd_8261434 := by
    simpa [prefixWord, tailWord_8261434, baseEnd_8261434] using wordTrace_append hprefix tailTrace_8261434
  have hstable : (prefixWord ++ tailWord_8261434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261434).length < 2 ^ (prefixWord ++ tailWord_8261434).sum := by decide
  have hdescent : baseEnd_8261434 < baseStart_8261434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261480 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_8261480 : Nat := 118140960795 + 8261480 * 2 ^ 59
def prefixEnd_8261480 : Nat := 4983230072969 + 3 ^ 40 * 8261480 * 2
def baseEnd_8261480 : Nat := 4242110157506442155206151

theorem tailTrace_8261480 : CollatzResearch.WordTrace tailWord_8261480 prefixEnd_8261480 4242110157506442155206151 := by
  unfold tailWord_8261480
  simp only [CollatzResearch.WordTrace]
  refine ⟨150660465055038191648882947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200880620073384255531843929 150660465055038191648882947)
  ·
    refine ⟨225990697582557287473324421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150660465055038191648882947 225990697582557287473324421)
    ·
      refine ⟨42373255796729491401248329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225990697582557287473324421 42373255796729491401248329)
      ·
        refine ⟨31779941847547118550936247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42373255796729491401248329 31779941847547118550936247)
        ·
          refine ⟨47669912771320677826404371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31779941847547118550936247 47669912771320677826404371)
          ·
            refine ⟨71504869156981016739606557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47669912771320677826404371 71504869156981016739606557)
            ·
              refine ⟨26814325933867881277352459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71504869156981016739606557 26814325933867881277352459)
              ·
                refine ⟨40221488900801821916028689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26814325933867881277352459 40221488900801821916028689)
                ·
                  refine ⟨30166116675601366437021517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40221488900801821916028689 30166116675601366437021517)
                  ·
                    refine ⟨11312293753350512413883069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30166116675601366437021517 11312293753350512413883069)
                    ·
                      refine ⟨4242110157506442155206151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11312293753350512413883069 4242110157506442155206151)
                      ·
                        rfl

theorem cell23_8261480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_8261480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261480 prefixEnd_8261480 := by exact prefixLift 8261480
  have htrace : WordTrace (prefixWord ++ tailWord_8261480) baseStart_8261480 baseEnd_8261480 := by
    simpa [prefixWord, tailWord_8261480, baseEnd_8261480] using wordTrace_append hprefix tailTrace_8261480
  have hstable : (prefixWord ++ tailWord_8261480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261480).length < 2 ^ (prefixWord ++ tailWord_8261480).sum := by decide
  have hdescent : baseEnd_8261480 < baseStart_8261480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261490 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 4, 5, 2]
def baseStart_8261490 : Nat := 118140960795 + 8261490 * 2 ^ 59
def prefixEnd_8261490 : Nat := 4983230072969 + 3 ^ 40 * 8261490 * 2
def baseEnd_8261490 : Nat := 4242115292312987116081105

theorem tailTrace_8261490 : CollatzResearch.WordTrace tailWord_8261490 prefixEnd_8261490 4242115292312987116081105 := by
  unfold tailWord_8261490
  simp only [CollatzResearch.WordTrace]
  refine ⟨75330323710010038751407481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200880863226693436670419949 75330323710010038751407481)
  ·
    refine ⟨56497742782507529063555611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75330323710010038751407481 56497742782507529063555611)
    ·
      refine ⟨84746614173761293595333417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56497742782507529063555611 84746614173761293595333417)
      ·
        refine ⟨63559960630320970196500063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84746614173761293595333417 63559960630320970196500063)
        ·
          refine ⟨95339940945481455294750095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63559960630320970196500063 95339940945481455294750095)
          ·
            refine ⟨143009911418222182942125143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95339940945481455294750095 143009911418222182942125143)
            ·
              refine ⟨214514867127333274413187715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143009911418222182942125143 214514867127333274413187715)
              ·
                refine ⟨321772300690999911619781573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214514867127333274413187715 321772300690999911619781573)
                ·
                  refine ⟨60332306379562483428709045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321772300690999911619781573 60332306379562483428709045)
                  ·
                    refine ⟨5656153723083982821441473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60332306379562483428709045 5656153723083982821441473)
                    ·
                      refine ⟨4242115292312987116081105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656153723083982821441473 4242115292312987116081105)
                      ·
                        rfl

theorem cell23_8261490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_8261490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261490 prefixEnd_8261490 := by exact prefixLift 8261490
  have htrace : WordTrace (prefixWord ++ tailWord_8261490) baseStart_8261490 baseEnd_8261490 := by
    simpa [prefixWord, tailWord_8261490, baseEnd_8261490] using wordTrace_append hprefix tailTrace_8261490
  have hstable : (prefixWord ++ tailWord_8261490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261490).length < 2 ^ (prefixWord ++ tailWord_8261490).sum := by decide
  have hdescent : baseEnd_8261490 < baseStart_8261490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261520 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 2, 4, 2]
def baseStart_8261520 : Nat := 118140960795 + 8261520 * 2 ^ 59
def prefixEnd_8261520 : Nat := 4983230072969 + 3 ^ 40 * 8261520 * 2
def baseEnd_8261520 : Nat := 4242130696732621998705967

theorem tailTrace_8261520 : CollatzResearch.WordTrace tailWord_8261520 prefixEnd_8261520 4242130696732621998705967 := by
  unfold tailWord_8261520
  simp only [CollatzResearch.WordTrace]
  refine ⟨150661194514965735064611007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200881592686620980086148009 150661194514965735064611007)
  ·
    refine ⟨225991791772448602596916511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150661194514965735064611007 225991791772448602596916511)
    ·
      refine ⟨338987687658672903895374767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225991791772448602596916511 338987687658672903895374767)
      ·
        refine ⟨508481531488009355843062151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338987687658672903895374767 508481531488009355843062151)
        ·
          refine ⟨762722297232014033764593227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508481531488009355843062151 762722297232014033764593227)
          ·
            refine ⟨1144083445848021050646889841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762722297232014033764593227 1144083445848021050646889841)
            ·
              refine ⟨858062584386015787985167381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144083445848021050646889841 858062584386015787985167381)
              ·
                refine ⟨40221683643094490061804721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 858062584386015787985167381 40221683643094490061804721)
                ·
                  refine ⟨30166262732320867546353541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40221683643094490061804721 30166262732320867546353541)
                  ·
                    refine ⟨5656174262310162664941289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30166262732320867546353541 5656174262310162664941289)
                    ·
                      refine ⟨4242130696732621998705967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656174262310162664941289 4242130696732621998705967)
                      ·
                        rfl

theorem cell23_8261520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 4, 2].length) (baseStart_8261520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261520 prefixEnd_8261520 := by exact prefixLift 8261520
  have htrace : WordTrace (prefixWord ++ tailWord_8261520) baseStart_8261520 baseEnd_8261520 := by
    simpa [prefixWord, tailWord_8261520, baseEnd_8261520] using wordTrace_append hprefix tailTrace_8261520
  have hstable : (prefixWord ++ tailWord_8261520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261520).length < 2 ^ (prefixWord ++ tailWord_8261520).sum := by decide
  have hdescent : baseEnd_8261520 < baseStart_8261520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261540 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_8261540 : Nat := 118140960795 + 8261540 * 2 ^ 59
def prefixEnd_8261540 : Nat := 4983230072969 + 3 ^ 40 * 8261540 * 2
def baseEnd_8261540 : Nat := 4242140966345711920455875

theorem tailTrace_8261540 : CollatzResearch.WordTrace tailWord_8261540 prefixEnd_8261540 4242140966345711920455875 := by
  unfold tailWord_8261540
  simp only [CollatzResearch.WordTrace]
  refine ⟨150661559244929506772475037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200882078993239342363300049 150661559244929506772475037)
  ·
    refine ⟨56498084716848565039678139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150661559244929506772475037 56498084716848565039678139)
    ·
      refine ⟨84747127075272847559517209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56498084716848565039678139 84747127075272847559517209)
      ·
        refine ⟨63560345306454635669637907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84747127075272847559517209 63560345306454635669637907)
        ·
          refine ⟨95340517959681953504456861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63560345306454635669637907 95340517959681953504456861)
          ·
            refine ⟨35752694234880732564171323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95340517959681953504456861 35752694234880732564171323)
            ·
              refine ⟨53629041352321098846256985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35752694234880732564171323 53629041352321098846256985)
              ·
                refine ⟨40221781014240824134692739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53629041352321098846256985 40221781014240824134692739)
                ·
                  refine ⟨60332671521361236202039109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40221781014240824134692739 60332671521361236202039109)
                  ·
                    refine ⟨11312375910255231787882333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60332671521361236202039109 11312375910255231787882333)
                    ·
                      refine ⟨4242140966345711920455875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11312375910255231787882333 4242140966345711920455875)
                      ·
                        rfl

theorem cell23_8261540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_8261540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261540 prefixEnd_8261540 := by exact prefixLift 8261540
  have htrace : WordTrace (prefixWord ++ tailWord_8261540) baseStart_8261540 baseEnd_8261540 := by
    simpa [prefixWord, tailWord_8261540, baseEnd_8261540] using wordTrace_append hprefix tailTrace_8261540
  have hstable : (prefixWord ++ tailWord_8261540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261540).length < 2 ^ (prefixWord ++ tailWord_8261540).sum := by decide
  have hdescent : baseEnd_8261540 < baseStart_8261540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261594 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 6]
def baseStart_8261594 : Nat := 118140960795 + 8261594 * 2 ^ 59
def prefixEnd_8261594 : Nat := 4983230072969 + 3 ^ 40 * 8261594 * 2
def baseEnd_8261594 : Nat := 471352077144561634353403

theorem tailTrace_8261594 : CollatzResearch.WordTrace tailWord_8261594 prefixEnd_8261594 471352077144561634353403 := by
  unfold tailWord_8261594
  simp only [CollatzResearch.WordTrace]
  refine ⟨75331272007915845191853959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200883392021108920511610557 75331272007915845191853959)
  ·
    refine ⟨112996908011873767787780939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75331272007915845191853959 112996908011873767787780939)
    ·
      refine ⟨169495362017810651681671409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112996908011873767787780939 169495362017810651681671409)
      ·
        refine ⟨127121521513357988761253557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169495362017810651681671409 127121521513357988761253557)
        ·
          refine ⟨11917642641877311446367521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127121521513357988761253557 11917642641877311446367521)
          ·
            refine ⟨8938231981407983584775641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11917642641877311446367521 8938231981407983584775641)
            ·
              refine ⟨6703673986055987688581731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8938231981407983584775641 6703673986055987688581731)
              ·
                refine ⟨10055510979083981532872597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703673986055987688581731 10055510979083981532872597)
                ·
                  refine ⟨471352077144561634353403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10055510979083981532872597 471352077144561634353403)
                  ·
                    rfl

theorem cell23_8261594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_8261594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261594 prefixEnd_8261594 := by exact prefixLift 8261594
  have htrace : WordTrace (prefixWord ++ tailWord_8261594) baseStart_8261594 baseEnd_8261594 := by
    simpa [prefixWord, tailWord_8261594, baseEnd_8261594] using wordTrace_append hprefix tailTrace_8261594
  have hstable : (prefixWord ++ tailWord_8261594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261594).length < 2 ^ (prefixWord ++ tailWord_8261594).sum := by decide
  have hdescent : baseEnd_8261594 < baseStart_8261594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261607 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 3, 5]
def baseStart_8261607 : Nat := 118140960795 + 8261607 * 2 ^ 59
def prefixEnd_8261607 : Nat := 4983230072969 + 3 ^ 40 * 8261607 * 2
def baseEnd_8261607 : Nat := 1414058456516521052772689

theorem tailTrace_8261607 : CollatzResearch.WordTrace tailWord_8261607 prefixEnd_8261607 1414058456516521052772689 := by
  unfold tailWord_8261607
  simp only [CollatzResearch.WordTrace]
  refine ⟨301325562180616283987639075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200883708120410855991759383 301325562180616283987639075)
  ·
    refine ⟨451988343270924425981458613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301325562180616283987639075 451988343270924425981458613)
    ·
      refine ⟨42373907181649164935761745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 451988343270924425981458613 42373907181649164935761745)
      ·
        refine ⟨31780430386236873701821309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42373907181649164935761745 31780430386236873701821309)
        ·
          refine ⟨11917661394838827638182991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31780430386236873701821309 11917661394838827638182991)
          ·
            refine ⟨17876492092258241457274487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11917661394838827638182991 17876492092258241457274487)
            ·
              refine ⟨26814738138387362185911731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17876492092258241457274487 26814738138387362185911731)
              ·
                refine ⟨40222107207581043278867597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26814738138387362185911731 40222107207581043278867597)
                ·
                  refine ⟨15083290202842891229575349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40222107207581043278867597 15083290202842891229575349)
                  ·
                    refine ⟨1414058456516521052772689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15083290202842891229575349 1414058456516521052772689)
                    ·
                      rfl

theorem cell23_8261607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_8261607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261607 prefixEnd_8261607 := by exact prefixLift 8261607
  have htrace : WordTrace (prefixWord ++ tailWord_8261607) baseStart_8261607 baseEnd_8261607 := by
    simpa [prefixWord, tailWord_8261607, baseEnd_8261607] using wordTrace_append hprefix tailTrace_8261607
  have hstable : (prefixWord ++ tailWord_8261607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261607).length < 2 ^ (prefixWord ++ tailWord_8261607).sum := by decide
  have hdescent : baseEnd_8261607 < baseStart_8261607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261614 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_8261614 : Nat := 118140960795 + 8261614 * 2 ^ 59
def prefixEnd_8261614 : Nat := 4983230072969 + 3 ^ 40 * 8261614 * 2
def baseEnd_8261614 : Nat := 4242178963914144630930535

theorem tailTrace_8261614 : CollatzResearch.WordTrace tailWord_8261614 prefixEnd_8261614 4242178963914144630930535 := by
  unfold tailWord_8261614
  simp only [CollatzResearch.WordTrace]
  refine ⟨37665727186448865522892987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200883878327727282788762597 37665727186448865522892987)
  ·
    refine ⟨56498590779673298284339481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37665727186448865522892987 56498590779673298284339481)
    ·
      refine ⟨42373943084754973713254611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56498590779673298284339481 42373943084754973713254611)
      ·
        refine ⟨63560914627132460569881917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42373943084754973713254611 63560914627132460569881917)
        ·
          refine ⟨23835342985174672713705719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63560914627132460569881917 23835342985174672713705719)
          ·
            refine ⟨35753014477762009070558579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23835342985174672713705719 35753014477762009070558579)
            ·
              refine ⟨53629521716643013605837869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35753014477762009070558579 53629521716643013605837869)
              ·
                refine ⟨20111070643741130102189201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53629521716643013605837869 20111070643741130102189201)
                ·
                  refine ⟨15083302982805847576641901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20111070643741130102189201 15083302982805847576641901)
                  ·
                    refine ⟨5656238618552192841240713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15083302982805847576641901 5656238618552192841240713)
                    ·
                      refine ⟨4242178963914144630930535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656238618552192841240713 4242178963914144630930535)
                      ·
                        rfl

theorem cell23_8261614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_8261614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261614 prefixEnd_8261614 := by exact prefixLift 8261614
  have htrace : WordTrace (prefixWord ++ tailWord_8261614) baseStart_8261614 baseEnd_8261614 := by
    simpa [prefixWord, tailWord_8261614, baseEnd_8261614] using wordTrace_append hprefix tailTrace_8261614
  have hstable : (prefixWord ++ tailWord_8261614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261614).length < 2 ^ (prefixWord ++ tailWord_8261614).sum := by decide
  have hdescent : baseEnd_8261614 < baseStart_8261614 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261623 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_8261623 : Nat := 118140960795 + 8261623 * 2 ^ 59
def prefixEnd_8261623 : Nat := 4983230072969 + 3 ^ 40 * 8261623 * 2
def baseEnd_8261623 : Nat := 4242183585240035095717993

theorem tailTrace_8261623 : CollatzResearch.WordTrace tailWord_8261623 prefixEnd_8261623 4242183585240035095717993 := by
  unfold tailWord_8261623
  simp only [CollatzResearch.WordTrace]
  refine ⟨301326145748558318720221523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200884097165705545813481015 301326145748558318720221523)
  ·
    refine ⟨451989218622837478080332285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301326145748558318720221523 451989218622837478080332285)
    ·
      refine ⟨169495956983564054280124607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451989218622837478080332285 169495956983564054280124607)
      ·
        refine ⟨254243935475346081420186911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169495956983564054280124607 254243935475346081420186911)
        ·
          refine ⟨381365903213019122130280367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254243935475346081420186911 381365903213019122130280367)
          ·
            refine ⟨572048854819528683195420551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381365903213019122130280367 572048854819528683195420551)
            ·
              refine ⟨858073282229293024793130827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572048854819528683195420551 858073282229293024793130827)
              ·
                refine ⟨1287109923343939537189696241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858073282229293024793130827 1287109923343939537189696241)
                ·
                  refine ⟨965332442507954652892272181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1287109923343939537189696241 965332442507954652892272181)
                  ·
                    refine ⟨90499916485120748708650517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 965332442507954652892272181 90499916485120748708650517)
                    ·
                      refine ⟨4242183585240035095717993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90499916485120748708650517 4242183585240035095717993)
                      ·
                        rfl

theorem cell23_8261623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_8261623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261623 prefixEnd_8261623 := by exact prefixLift 8261623
  have htrace : WordTrace (prefixWord ++ tailWord_8261623) baseStart_8261623 baseEnd_8261623 := by
    simpa [prefixWord, tailWord_8261623, baseEnd_8261623] using wordTrace_append hprefix tailTrace_8261623
  have hstable : (prefixWord ++ tailWord_8261623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261623).length < 2 ^ (prefixWord ++ tailWord_8261623).sum := by decide
  have hdescent : baseEnd_8261623 < baseStart_8261623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261637 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 2, 4]
def baseStart_8261637 : Nat := 118140960795 + 8261637 * 2 ^ 59
def prefixEnd_8261637 : Nat := 4983230072969 + 3 ^ 40 * 8261637 * 2
def baseEnd_8261637 : Nat := 1414063591323066013647643

theorem tailTrace_8261637 : CollatzResearch.WordTrace tailWord_8261637 prefixEnd_8261637 1414063591323066013647643 := by
  unfold tailWord_8261637
  simp only [CollatzResearch.WordTrace]
  refine ⟨301326656370507599111231165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200884437580338399407487443 301326656370507599111231165)
  ·
    refine ⟨112997496138940349666711687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301326656370507599111231165 112997496138940349666711687)
    ·
      refine ⟨169496244208410524500067531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112997496138940349666711687 169496244208410524500067531)
      ·
        refine ⟨254244366312615786750101297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169496244208410524500067531 254244366312615786750101297)
        ·
          refine ⟨190683274734461840062575973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254244366312615786750101297 190683274734461840062575973)
          ·
            refine ⟨35753114012711595011732995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190683274734461840062575973 35753114012711595011732995)
            ·
              refine ⟨53629671019067392517599493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35753114012711595011732995 53629671019067392517599493)
              ·
                refine ⟨10055563316075136097049905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53629671019067392517599493 10055563316075136097049905)
                ·
                  refine ⟨7541672487056352072787429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10055563316075136097049905 7541672487056352072787429)
                  ·
                    refine ⟨1414063591323066013647643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7541672487056352072787429 1414063591323066013647643)
                    ·
                      rfl

theorem cell23_8261637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_8261637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261637 prefixEnd_8261637 := by exact prefixLift 8261637
  have htrace : WordTrace (prefixWord ++ tailWord_8261637) baseStart_8261637 baseEnd_8261637 := by
    simpa [prefixWord, tailWord_8261637, baseEnd_8261637] using wordTrace_append hprefix tailTrace_8261637
  have hstable : (prefixWord ++ tailWord_8261637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261637).length < 2 ^ (prefixWord ++ tailWord_8261637).sum := by decide
  have hdescent : baseEnd_8261637 < baseStart_8261637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261640 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_8261640 : Nat := 118140960795 + 8261640 * 2 ^ 59
def prefixEnd_8261640 : Nat := 4983230072969 + 3 ^ 40 * 8261640 * 2
def baseEnd_8261640 : Nat := 4242192314411161529205415

theorem tailTrace_8261640 : CollatzResearch.WordTrace tailWord_8261640 prefixEnd_8261640 4242192314411161529205415 := by
  unfold tailWord_8261640
  simp only [CollatzResearch.WordTrace]
  refine ⟨150663382894748365311795187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200884510526331153749060249 150663382894748365311795187)
  ·
    refine ⟨225995074342122547967692781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150663382894748365311795187 225995074342122547967692781)
    ·
      refine ⟨84748152878295955487884793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225995074342122547967692781 84748152878295955487884793)
      ·
        refine ⟨63561114658721966615913595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84748152878295955487884793 63561114658721966615913595)
        ·
          refine ⟨95341671988082949923870393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63561114658721966615913595 95341671988082949923870393)
          ·
            refine ⟨71506253991062212442902795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95341671988082949923870393 71506253991062212442902795)
            ·
              refine ⟨107259380986593318664354193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71506253991062212442902795 107259380986593318664354193)
              ·
                refine ⟨80444535739944988998265645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107259380986593318664354193 80444535739944988998265645)
                ·
                  refine ⟨30166700902479370874349617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80444535739944988998265645 30166700902479370874349617)
                  ·
                    refine ⟨22625025676859528155762213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30166700902479370874349617 22625025676859528155762213)
                    ·
                      refine ⟨4242192314411161529205415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22625025676859528155762213 4242192314411161529205415)
                      ·
                        rfl

theorem cell23_8261640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_8261640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261640 prefixEnd_8261640 := by exact prefixLift 8261640
  have htrace : WordTrace (prefixWord ++ tailWord_8261640) baseStart_8261640 baseEnd_8261640 := by
    simpa [prefixWord, tailWord_8261640, baseEnd_8261640] using wordTrace_append hprefix tailTrace_8261640
  have hstable : (prefixWord ++ tailWord_8261640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261640).length < 2 ^ (prefixWord ++ tailWord_8261640).sum := by decide
  have hdescent : baseEnd_8261640 < baseStart_8261640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261644 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 3, 2, 2]
def baseStart_8261644 : Nat := 118140960795 + 8261644 * 2 ^ 59
def prefixEnd_8261644 : Nat := 4983230072969 + 3 ^ 40 * 8261644 * 2
def baseEnd_8261644 : Nat := 4242194368333779513555397

theorem tailTrace_8261644 : CollatzResearch.WordTrace tailWord_8261644 prefixEnd_8261644 4242194368333779513555397 := by
  unfold tailWord_8261644
  simp only [CollatzResearch.WordTrace]
  refine ⟨150663455840741119653367993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200884607787654826204490657 150663455840741119653367993)
  ·
    refine ⟨112997591880555839740025995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150663455840741119653367993 112997591880555839740025995)
    ·
      refine ⟨169496387820833759610038993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112997591880555839740025995 169496387820833759610038993)
      ·
        refine ⟨127122290865625319707529245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169496387820833759610038993 127122290865625319707529245)
        ·
          refine ⟨47670859074609494890323467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127122290865625319707529245 47670859074609494890323467)
          ·
            refine ⟨71506288611914242335485201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47670859074609494890323467 71506288611914242335485201)
            ·
              refine ⟨53629716458935681751613901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71506288611914242335485201 53629716458935681751613901)
              ·
                refine ⟨20111143672100880656855213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53629716458935681751613901 20111143672100880656855213)
                ·
                  refine ⟨7541678877037830246320705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20111143672100880656855213 7541678877037830246320705)
                  ·
                    refine ⟨5656259157778372684740529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7541678877037830246320705 5656259157778372684740529)
                    ·
                      refine ⟨4242194368333779513555397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656259157778372684740529 4242194368333779513555397)
                      ·
                        rfl

theorem cell23_8261644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_8261644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261644 prefixEnd_8261644 := by exact prefixLift 8261644
  have htrace : WordTrace (prefixWord ++ tailWord_8261644) baseStart_8261644 baseEnd_8261644 := by
    simpa [prefixWord, tailWord_8261644, baseEnd_8261644] using wordTrace_append hprefix tailTrace_8261644
  have hstable : (prefixWord ++ tailWord_8261644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261644).length < 2 ^ (prefixWord ++ tailWord_8261644).sum := by decide
  have hdescent : baseEnd_8261644 < baseStart_8261644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261661 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_8261661 : Nat := 118140960795 + 8261661 * 2 ^ 59
def prefixEnd_8261661 : Nat := 4983230072969 + 3 ^ 40 * 8261661 * 2
def baseEnd_8261661 : Nat := 4242203097504905947042819

theorem tailTrace_8261661 : CollatzResearch.WordTrace tailWord_8261661 prefixEnd_8261661 4242203097504905947042819 := by
  unfold tailWord_8261661
  simp only [CollatzResearch.WordTrace]
  refine ⟨301327531722420651210104837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200885021148280434140069891 301327531722420651210104837)
  ·
    refine ⟨56498912197953872101894657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301327531722420651210104837 56498912197953872101894657)
    ·
      refine ⟨42374184148465404076420993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56498912197953872101894657 42374184148465404076420993)
      ·
        refine ⟨31780638111349053057315745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42374184148465404076420993 31780638111349053057315745)
        ·
          refine ⟨23835478583511789792986809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31780638111349053057315745 23835478583511789792986809)
          ·
            refine ⟨17876608937633842344740107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23835478583511789792986809 17876608937633842344740107)
            ·
              refine ⟨26814913406450763517110161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17876608937633842344740107 26814913406450763517110161)
              ·
                refine ⟨20111185054838072637832621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26814913406450763517110161 20111185054838072637832621)
                ·
                  refine ⟨7541694395564277239187233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20111185054838072637832621 7541694395564277239187233)
                  ·
                    refine ⟨5656270796673207929390425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7541694395564277239187233 5656270796673207929390425)
                    ·
                      refine ⟨4242203097504905947042819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656270796673207929390425 4242203097504905947042819)
                      ·
                        rfl

theorem cell23_8261661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_8261661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261661 prefixEnd_8261661 := by exact prefixLift 8261661
  have htrace : WordTrace (prefixWord ++ tailWord_8261661) baseStart_8261661 baseEnd_8261661 := by
    simpa [prefixWord, tailWord_8261661, baseEnd_8261661] using wordTrace_append hprefix tailTrace_8261661
  have hstable : (prefixWord ++ tailWord_8261661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261661).length < 2 ^ (prefixWord ++ tailWord_8261661).sum := by decide
  have hdescent : baseEnd_8261661 < baseStart_8261661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261678 : List Nat := [4, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_8261678 : Nat := 118140960795 + 8261678 * 2 ^ 59
def prefixEnd_8261678 : Nat := 4983230072969 + 3 ^ 40 * 8261678 * 2
def baseEnd_8261678 : Nat := 4242211826676032380530241

theorem tailTrace_8261678 : CollatzResearch.WordTrace tailWord_8261678 prefixEnd_8261678 4242211826676032380530241 := by
  unfold tailWord_8261678
  simp only [CollatzResearch.WordTrace]
  refine ⟨37666018970419882889184211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200885434508906042075649125 37666018970419882889184211)
  ·
    refine ⟨56499028455629824333776317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37666018970419882889184211 56499028455629824333776317)
    ·
      refine ⟨21187135670861184125166119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56499028455629824333776317 21187135670861184125166119)
      ·
        refine ⟨31780703506291776187749179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21187135670861184125166119 31780703506291776187749179)
        ·
          refine ⟨47671055259437664281623769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31780703506291776187749179 47671055259437664281623769)
          ·
            refine ⟨35753291444578248211217827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47671055259437664281623769 35753291444578248211217827)
            ·
              refine ⟨53629937166867372316826741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35753291444578248211217827 53629937166867372316826741)
              ·
                refine ⟨5027806609393816154702507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53629937166867372316826741 5027806609393816154702507)
                ·
                  refine ⟨7541709914090724232053761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027806609393816154702507 7541709914090724232053761)
                  ·
                    refine ⟨5656282435568043174040321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7541709914090724232053761 5656282435568043174040321)
                    ·
                      refine ⟨4242211826676032380530241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656282435568043174040321 4242211826676032380530241)
                      ·
                        rfl

theorem cell23_8261678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_8261678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261678 prefixEnd_8261678 := by exact prefixLift 8261678
  have htrace : WordTrace (prefixWord ++ tailWord_8261678) baseStart_8261678 baseEnd_8261678 := by
    simpa [prefixWord, tailWord_8261678, baseEnd_8261678] using wordTrace_append hprefix tailTrace_8261678
  have hstable : (prefixWord ++ tailWord_8261678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261678).length < 2 ^ (prefixWord ++ tailWord_8261678).sum := by decide
  have hdescent : baseEnd_8261678 < baseStart_8261678 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261681 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 1, 2, 3]
def baseStart_8261681 : Nat := 118140960795 + 8261681 * 2 ^ 59
def prefixEnd_8261681 : Nat := 4983230072969 + 3 ^ 40 * 8261681 * 2
def baseEnd_8261681 : Nat := 4242213367117995868792727

theorem tailTrace_8261681 : CollatzResearch.WordTrace tailWord_8261681 prefixEnd_8261681 4242213367117995868792727 := by
  unfold tailWord_8261681
  simp only [CollatzResearch.WordTrace]
  refine ⟨301328261182348194625832897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200885507454898796417221931 301328261182348194625832897)
  ·
    refine ⟨225996195886761145969374673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301328261182348194625832897 225996195886761145969374673)
    ·
      refine ⟨169497146915070859477031005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225996195886761145969374673 169497146915070859477031005)
      ·
        refine ⟨63561430093151572303886627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169497146915070859477031005 63561430093151572303886627)
        ·
          refine ⟨95342145139727358455829941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63561430093151572303886627 95342145139727358455829941)
          ·
            refine ⟨8938326106849439855234057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95342145139727358455829941 8938326106849439855234057)
            ·
              refine ⟨6703744580137079891425543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8938326106849439855234057 6703744580137079891425543)
              ·
                refine ⟨10055616870205619837138315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703744580137079891425543 10055616870205619837138315)
                ·
                  refine ⟨15083425305308429755707473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10055616870205619837138315 15083425305308429755707473)
                  ·
                    refine ⟨11312568978981322316780605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15083425305308429755707473 11312568978981322316780605)
                    ·
                      refine ⟨4242213367117995868792727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11312568978981322316780605 4242213367117995868792727)
                      ·
                        rfl

theorem cell23_8261681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_8261681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261681 prefixEnd_8261681 := by exact prefixLift 8261681
  have htrace : WordTrace (prefixWord ++ tailWord_8261681) baseStart_8261681 baseEnd_8261681 := by
    simpa [prefixWord, tailWord_8261681, baseEnd_8261681] using wordTrace_append hprefix tailTrace_8261681
  have hstable : (prefixWord ++ tailWord_8261681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261681).length < 2 ^ (prefixWord ++ tailWord_8261681).sum := by decide
  have hdescent : baseEnd_8261681 < baseStart_8261681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261757 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 7]
def baseStart_8261757 : Nat := 118140960795 + 8261757 * 2 ^ 59
def prefixEnd_8261757 : Nat := 4983230072969 + 3 ^ 40 * 8261757 * 2
def baseEnd_8261757 : Nat := 471361376849748619049153

theorem tailTrace_8261757 : CollatzResearch.WordTrace tailWord_8261757 prefixEnd_8261757 471361376849748619049153 := by
  unfold tailWord_8261757
  simp only [CollatzResearch.WordTrace]
  refine ⟨301331033130072859605599525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200887355420048573070399683 301331033130072859605599525)
  ·
    refine ⟨56499568711888661176049911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301331033130072859605599525 56499568711888661176049911)
    ·
      refine ⟨84749353067832991764074867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56499568711888661176049911 84749353067832991764074867)
      ·
        refine ⟨127124029601749487646112301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84749353067832991764074867 127124029601749487646112301)
        ·
          refine ⟨47671511100656057867292113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127124029601749487646112301 47671511100656057867292113)
          ·
            refine ⟨35753633325492043400469085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47671511100656057867292113 35753633325492043400469085)
            ·
              refine ⟨13407612497059516275175907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35753633325492043400469085 13407612497059516275175907)
              ·
                refine ⟨20111418745589274412763861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13407612497059516275175907 20111418745589274412763861)
                ·
                  refine ⟨471361376849748619049153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20111418745589274412763861 471361376849748619049153)
                  ·
                    rfl

theorem cell23_8261757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_8261757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261757 prefixEnd_8261757 := by exact prefixLift 8261757
  have htrace : WordTrace (prefixWord ++ tailWord_8261757) baseStart_8261757 baseEnd_8261757 := by
    simpa [prefixWord, tailWord_8261757, baseEnd_8261757] using wordTrace_append hprefix tailTrace_8261757
  have hstable : (prefixWord ++ tailWord_8261757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261757).length < 2 ^ (prefixWord ++ tailWord_8261757).sum := by decide
  have hdescent : baseEnd_8261757 < baseStart_8261757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261767 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_8261767 : Nat := 118140960795 + 8261767 * 2 ^ 59
def prefixEnd_8261767 : Nat := 4983230072969 + 3 ^ 40 * 8261767 * 2
def baseEnd_8261767 : Nat := 4242257526454282532317331

theorem tailTrace_8261767 : CollatzResearch.WordTrace tailWord_8261767 prefixEnd_8261767 4242257526454282532317331 := by
  unfold tailWord_8261767
  simp only [CollatzResearch.WordTrace]
  refine ⟨301331397860036631313463555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200887598573357754208975703 301331397860036631313463555)
  ·
    refine ⟨451997096790054946970195333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301331397860036631313463555 451997096790054946970195333)
    ·
      refine ⟨84749455648135302556911625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451997096790054946970195333 84749455648135302556911625)
      ·
        refine ⟨63562091736101476917683719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84749455648135302556911625 63562091736101476917683719)
        ·
          refine ⟨95343137604152215376525579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63562091736101476917683719 95343137604152215376525579)
          ·
            refine ⟨143014706406228323064788369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95343137604152215376525579 143014706406228323064788369)
            ·
              refine ⟨107261029804671242298591277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143014706406228323064788369 107261029804671242298591277)
              ·
                refine ⟨40222886176751715861971729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107261029804671242298591277 40222886176751715861971729)
                ·
                  refine ⟨30167164632563786896478797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40222886176751715861971729 30167164632563786896478797)
                  ·
                    refine ⟨11312686737211420086179549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30167164632563786896478797 11312686737211420086179549)
                    ·
                      refine ⟨4242257526454282532317331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11312686737211420086179549 4242257526454282532317331)
                      ·
                        rfl

theorem cell23_8261767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_8261767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261767 prefixEnd_8261767 := by exact prefixLift 8261767
  have htrace : WordTrace (prefixWord ++ tailWord_8261767) baseStart_8261767 baseEnd_8261767 := by
    simpa [prefixWord, tailWord_8261767, baseEnd_8261767] using wordTrace_append hprefix tailTrace_8261767
  have hstable : (prefixWord ++ tailWord_8261767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261767).length < 2 ^ (prefixWord ++ tailWord_8261767).sum := by decide
  have hdescent : baseEnd_8261767 < baseStart_8261767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261768 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 2, 2, 2]
def baseStart_8261768 : Nat := 118140960795 + 8261768 * 2 ^ 59
def prefixEnd_8261768 : Nat := 4983230072969 + 3 ^ 40 * 8261768 * 2
def baseEnd_8261768 : Nat := 4242258039934937028404827

theorem tailTrace_8261768 : CollatzResearch.WordTrace tailWord_8261768 prefixEnd_8261768 4242258039934937028404827 := by
  unfold tailWord_8261768
  simp only [CollatzResearch.WordTrace]
  refine ⟨150665717166516504242124979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200887622888688672322833305 150665717166516504242124979)
  ·
    refine ⟨225998575749774756363187469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150665717166516504242124979 225998575749774756363187469)
    ·
      refine ⟨84749465906165533636195301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225998575749774756363187469 84749465906165533636195301)
      ·
        refine ⟨15890524857406037556786619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84749465906165533636195301 15890524857406037556786619)
        ·
          refine ⟨23835787286109056335179929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15890524857406037556786619 23835787286109056335179929)
          ·
            refine ⟨17876840464581792251384947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23835787286109056335179929 17876840464581792251384947)
            ·
              refine ⟨26815260696872688377077421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17876840464581792251384947 26815260696872688377077421)
              ·
                refine ⟨10055722761327258141404033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26815260696872688377077421 10055722761327258141404033)
                ·
                  refine ⟨7541792070995443606053025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10055722761327258141404033 7541792070995443606053025)
                  ·
                    refine ⟨5656344053246582704539769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7541792070995443606053025 5656344053246582704539769)
                    ·
                      refine ⟨4242258039934937028404827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656344053246582704539769 4242258039934937028404827)
                      ·
                        rfl

theorem cell23_8261768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_8261768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261768 prefixEnd_8261768 := by exact prefixLift 8261768
  have htrace : WordTrace (prefixWord ++ tailWord_8261768) baseStart_8261768 baseEnd_8261768 := by
    simpa [prefixWord, tailWord_8261768, baseEnd_8261768] using wordTrace_append hprefix tailTrace_8261768
  have hstable : (prefixWord ++ tailWord_8261768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261768).length < 2 ^ (prefixWord ++ tailWord_8261768).sum := by decide
  have hdescent : baseEnd_8261768 < baseStart_8261768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261824 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 1, 6, 2]
def baseStart_8261824 : Nat := 118140960795 + 8261824 * 2 ^ 59
def prefixEnd_8261824 : Nat := 4983230072969 + 3 ^ 40 * 8261824 * 2
def baseEnd_8261824 : Nat := 4242286794851588809304569

theorem tailTrace_8261824 : CollatzResearch.WordTrace tailWord_8261824 prefixEnd_8261824 4242286794851588809304569 := by
  unfold tailWord_8261824
  simp only [CollatzResearch.WordTrace]
  refine ⟨150666738410415065024144263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200888984547220086698859017 150666738410415065024144263)
  ·
    refine ⟨226000107615622597536216395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150666738410415065024144263 226000107615622597536216395)
    ·
      refine ⟨339000161423433896304324593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226000107615622597536216395 339000161423433896304324593)
      ·
        refine ⟨254250121067575422228243445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339000161423433896304324593 254250121067575422228243445)
        ·
          refine ⟨23835948850085195833897823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254250121067575422228243445 23835948850085195833897823)
          ·
            refine ⟨35753923275127793750846735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23835948850085195833897823 35753923275127793750846735)
            ·
              refine ⟨53630884912691690626270103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35753923275127793750846735 53630884912691690626270103)
              ·
                refine ⟨80446327369037535939405155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53630884912691690626270103 80446327369037535939405155)
                ·
                  refine ⟨120669491053556303909107733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80446327369037535939405155 120669491053556303909107733)
                  ·
                    refine ⟨5656382393135451745739425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120669491053556303909107733 5656382393135451745739425)
                    ·
                      refine ⟨4242286794851588809304569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656382393135451745739425 4242286794851588809304569)
                      ·
                        rfl

theorem cell23_8261824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 6, 2].length) (baseStart_8261824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261824 prefixEnd_8261824 := by exact prefixLift 8261824
  have htrace : WordTrace (prefixWord ++ tailWord_8261824) baseStart_8261824 baseEnd_8261824 := by
    simpa [prefixWord, tailWord_8261824, baseEnd_8261824] using wordTrace_append hprefix tailTrace_8261824
  have hstable : (prefixWord ++ tailWord_8261824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261824).length < 2 ^ (prefixWord ++ tailWord_8261824).sum := by decide
  have hdescent : baseEnd_8261824 < baseStart_8261824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261834 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 3, 4]
def baseStart_8261834 : Nat := 118140960795 + 8261834 * 2 ^ 59
def prefixEnd_8261834 : Nat := 4983230072969 + 3 ^ 40 * 8261834 * 2
def baseEnd_8261834 : Nat := 1414097309886044590059841

theorem tailTrace_8261834 : CollatzResearch.WordTrace tailWord_8261834 prefixEnd_8261834 1414097309886044590059841 := by
  unfold tailWord_8261834
  simp only [CollatzResearch.WordTrace]
  refine ⟨75333460387698475439038139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200889227700529267837435037 75333460387698475439038139)
  ·
    refine ⟨113000190581547713158557209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75333460387698475439038139 113000190581547713158557209)
    ·
      refine ⟨84750142936160784868917907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113000190581547713158557209 84750142936160784868917907)
      ·
        refine ⟨127125214404241177303376861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84750142936160784868917907 127125214404241177303376861)
        ·
          refine ⟨47671955401590441488766323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127125214404241177303376861 47671955401590441488766323)
          ·
            refine ⟨71507933102385662233149485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47671955401590441488766323 71507933102385662233149485)
            ·
              refine ⟨26815474913394623337431057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71507933102385662233149485 26815474913394623337431057)
              ·
                refine ⟨20111606185045967503073293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26815474913394623337431057 20111606185045967503073293)
                ·
                  refine ⟨7541852319392237813652485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20111606185045967503073293 7541852319392237813652485)
                  ·
                    refine ⟨1414097309886044590059841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7541852319392237813652485 1414097309886044590059841)
                    ·
                      rfl

theorem cell23_8261834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_8261834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261834 prefixEnd_8261834 := by exact prefixLift 8261834
  have htrace : WordTrace (prefixWord ++ tailWord_8261834) baseStart_8261834 baseEnd_8261834 := by
    simpa [prefixWord, tailWord_8261834, baseEnd_8261834] using wordTrace_append hprefix tailTrace_8261834
  have hstable : (prefixWord ++ tailWord_8261834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261834).length < 2 ^ (prefixWord ++ tailWord_8261834).sum := by decide
  have hdescent : baseEnd_8261834 < baseStart_8261834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261864 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 6]
def baseStart_8261864 : Nat := 118140960795 + 8261864 * 2 ^ 59
def prefixEnd_8261864 : Nat := 4983230072969 + 3 ^ 40 * 8261864 * 2
def baseEnd_8261864 : Nat := 471367481564196516978265

theorem tailTrace_8261864 : CollatzResearch.WordTrace tailWord_8261864 prefixEnd_8261864 471367481564196516978265 := by
  unfold tailWord_8261864
  simp only [CollatzResearch.WordTrace]
  refine ⟨150667467870342608439872323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200889957160456811253163097 150667467870342608439872323)
  ·
    refine ⟨226001201805513912659808485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150667467870342608439872323 226001201805513912659808485)
    ·
      refine ⟨42375225338533858623714091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226001201805513912659808485 42375225338533858623714091)
      ·
        refine ⟨63562838007800787935571137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42375225338533858623714091 63562838007800787935571137)
        ·
          refine ⟨47672128505850590951678353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63562838007800787935571137 47672128505850590951678353)
          ·
            refine ⟨35754096379387943213758765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47672128505850590951678353 35754096379387943213758765)
            ·
              refine ⟨13407786142270478705159537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35754096379387943213758765 13407786142270478705159537)
              ·
                refine ⟨10055839606702859028869653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13407786142270478705159537 10055839606702859028869653)
                ·
                  refine ⟨471367481564196516978265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10055839606702859028869653 471367481564196516978265)
                  ·
                    rfl

theorem cell23_8261864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 6].length) (baseStart_8261864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261864 prefixEnd_8261864 := by exact prefixLift 8261864
  have htrace : WordTrace (prefixWord ++ tailWord_8261864) baseStart_8261864 baseEnd_8261864 := by
    simpa [prefixWord, tailWord_8261864, baseEnd_8261864] using wordTrace_append hprefix tailTrace_8261864
  have hstable : (prefixWord ++ tailWord_8261864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261864).length < 2 ^ (prefixWord ++ tailWord_8261864).sum := by decide
  have hdescent : baseEnd_8261864 < baseStart_8261864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261907 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 1, 6]
def baseStart_8261907 : Nat := 118140960795 + 8261907 * 2 ^ 59
def prefixEnd_8261907 : Nat := 4983230072969 + 3 ^ 40 * 8261907 * 2
def baseEnd_8261907 : Nat := 1414109804581970661522229

theorem tailTrace_8261907 : CollatzResearch.WordTrace tailWord_8261907 prefixEnd_8261907 1414109804581970661522229 := by
  unfold tailWord_8261907
  simp only [CollatzResearch.WordTrace]
  refine ⟨301336504079529435223559975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200891002719686290149039983 301336504079529435223559975)
  ·
    refine ⟨452004756119294152835339963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301336504079529435223559975 452004756119294152835339963)
    ·
      refine ⟨678007134178941229253009945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452004756119294152835339963 678007134178941229253009945)
      ·
        refine ⟨508505350634205921939757459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678007134178941229253009945 508505350634205921939757459)
        ·
          refine ⟨762758025951308882909636189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508505350634205921939757459 762758025951308882909636189)
          ·
            refine ⟨286034259731740831091113571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 762758025951308882909636189 286034259731740831091113571)
            ·
              refine ⟨429051389597611246636670357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286034259731740831091113571 429051389597611246636670357)
              ·
                refine ⟨20111783887388027186093923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 429051389597611246636670357 20111783887388027186093923)
                ·
                  refine ⟨30167675831082040779140885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20111783887388027186093923 30167675831082040779140885)
                  ·
                    refine ⟨1414109804581970661522229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30167675831082040779140885 1414109804581970661522229)
                    ·
                      rfl

theorem cell23_8261907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 6].length) (baseStart_8261907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261907 prefixEnd_8261907 := by exact prefixLift 8261907
  have htrace : WordTrace (prefixWord ++ tailWord_8261907) baseStart_8261907 baseEnd_8261907 := by
    simpa [prefixWord, tailWord_8261907, baseEnd_8261907] using wordTrace_append hprefix tailTrace_8261907
  have hstable : (prefixWord ++ tailWord_8261907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261907).length < 2 ^ (prefixWord ++ tailWord_8261907).sum := by decide
  have hdescent : baseEnd_8261907 < baseStart_8261907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261925 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 3, 1, 3]
def baseStart_8261925 : Nat := 118140960795 + 8261925 * 2 ^ 59
def prefixEnd_8261925 : Nat := 4983230072969 + 3 ^ 40 * 8261925 * 2
def baseEnd_8261925 : Nat := 4242338656397692914141605

theorem tailTrace_8261925 : CollatzResearch.WordTrace tailWord_8261925 prefixEnd_8261925 4242338656397692914141605 := by
  unfold tailWord_8261925
  simp only [CollatzResearch.WordTrace]
  refine ⟨301337160593464224297715229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200891440395642816198476819 301337160593464224297715229)
  ·
    refine ⟨113001435222549084111643211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301337160593464224297715229 113001435222549084111643211)
    ·
      refine ⟨169502152833823626167464817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113001435222549084111643211 169502152833823626167464817)
      ·
        refine ⟨127126614625367719625598613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169502152833823626167464817 127126614625367719625598613)
        ·
          refine ⟨5959060060564111857449935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127126614625367719625598613 5959060060564111857449935)
          ·
            refine ⟨8938590090846167786174903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959060060564111857449935 8938590090846167786174903)
            ·
              refine ⟨13407885136269251679262355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8938590090846167786174903 13407885136269251679262355)
              ·
                refine ⟨20111827704403877518893533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13407885136269251679262355 20111827704403877518893533)
                ·
                  refine ⟨7541935389151454069585075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20111827704403877518893533 7541935389151454069585075)
                  ·
                    refine ⟨11312903083727181104377613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7541935389151454069585075 11312903083727181104377613)
                    ·
                      refine ⟨4242338656397692914141605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11312903083727181104377613 4242338656397692914141605)
                      ·
                        rfl

theorem cell23_8261925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_8261925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261925 prefixEnd_8261925 := by exact prefixLift 8261925
  have htrace : WordTrace (prefixWord ++ tailWord_8261925) baseStart_8261925 baseEnd_8261925 := by
    simpa [prefixWord, tailWord_8261925, baseEnd_8261925] using wordTrace_append hprefix tailTrace_8261925
  have hstable : (prefixWord ++ tailWord_8261925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261925).length < 2 ^ (prefixWord ++ tailWord_8261925).sum := by decide
  have hdescent : baseEnd_8261925 < baseStart_8261925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261941 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 2, 4]
def baseStart_8261941 : Nat := 118140960795 + 8261941 * 2 ^ 59
def prefixEnd_8261941 : Nat := 4983230072969 + 3 ^ 40 * 8261941 * 2
def baseEnd_8261941 : Nat := 1414115624029388283847177

theorem tailTrace_8261941 : CollatzResearch.WordTrace tailWord_8261941 prefixEnd_8261941 1414115624029388283847177 := by
  unfold tailWord_8261941
  simp only [CollatzResearch.WordTrace]
  refine ⟨301337744161406259030297677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200891829440937506020198451 301337744161406259030297677)
  ·
    refine ⟨113001654060527347136361629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301337744161406259030297677 113001654060527347136361629)
    ·
      refine ⟨42375620272697755176135611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113001654060527347136361629 42375620272697755176135611)
      ·
        refine ⟨63563430409046632764203417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42375620272697755176135611 63563430409046632764203417)
        ·
          refine ⟨47672572806784974573152563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63563430409046632764203417 47672572806784974573152563)
          ·
            refine ⟨71508859210177461859728845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47672572806784974573152563 71508859210177461859728845)
            ·
              refine ⟨26815822203816548197398317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71508859210177461859728845 26815822203816548197398317)
              ·
                refine ⟨10055933326431205574024369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26815822203816548197398317 10055933326431205574024369)
                ·
                  refine ⟨7541949994823404180518277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10055933326431205574024369 7541949994823404180518277)
                  ·
                    refine ⟨1414115624029388283847177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7541949994823404180518277 1414115624029388283847177)
                    ·
                      rfl

theorem cell23_8261941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_8261941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261941 prefixEnd_8261941 := by exact prefixLift 8261941
  have htrace : WordTrace (prefixWord ++ tailWord_8261941) baseStart_8261941 baseEnd_8261941 := by
    simpa [prefixWord, tailWord_8261941, baseEnd_8261941] using wordTrace_append hprefix tailTrace_8261941
  have hstable : (prefixWord ++ tailWord_8261941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261941).length < 2 ^ (prefixWord ++ tailWord_8261941).sum := by decide
  have hdescent : baseEnd_8261941 < baseStart_8261941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8261968 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 1, 2, 3]
def baseStart_8261968 : Nat := 118140960795 + 8261968 * 2 ^ 59
def prefixEnd_8261968 : Nat := 4983230072969 + 3 ^ 40 * 8261968 * 2
def baseEnd_8261968 : Nat := 4242360736065836245903907

theorem tailTrace_8261968 : CollatzResearch.WordTrace tailWord_8261968 prefixEnd_8261968 4242360736065836245903907 := by
  unfold tailWord_8261968
  simp only [CollatzResearch.WordTrace]
  refine ⟨150669364466154221320765279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200892485954872295094353705 150669364466154221320765279)
  ·
    refine ⟨226004046699231331981147919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150669364466154221320765279 226004046699231331981147919)
    ·
      refine ⟨339006070048846997971721879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226004046699231331981147919 339006070048846997971721879)
      ·
        refine ⟨508509105073270496957582819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339006070048846997971721879 508509105073270496957582819)
        ·
          refine ⟨762763657609905745436374229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508509105073270496957582819 762763657609905745436374229)
          ·
            refine ⟨17877273225232165908665021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 762763657609905745436374229 17877273225232165908665021)
            ·
              refine ⟨6703977459462062215749383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17877273225232165908665021 6703977459462062215749383)
              ·
                refine ⟨10055966189193093323624075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703977459462062215749383 10055966189193093323624075)
                ·
                  refine ⟨15083949283789639985436113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10055966189193093323624075 15083949283789639985436113)
                  ·
                    refine ⟨11312961962842229989077085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15083949283789639985436113 11312961962842229989077085)
                    ·
                      refine ⟨4242360736065836245903907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11312961962842229989077085 4242360736065836245903907)
                      ·
                        rfl

theorem cell23_8261968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 2, 3].length) (baseStart_8261968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8261968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8261968 prefixEnd_8261968 := by exact prefixLift 8261968
  have htrace : WordTrace (prefixWord ++ tailWord_8261968) baseStart_8261968 baseEnd_8261968 := by
    simpa [prefixWord, tailWord_8261968, baseEnd_8261968] using wordTrace_append hprefix tailTrace_8261968
  have hstable : (prefixWord ++ tailWord_8261968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8261968).length < 2 ^ (prefixWord ++ tailWord_8261968).sum := by decide
  have hdescent : baseEnd_8261968 < baseStart_8261968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8261968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262024 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_8262024 : Nat := 118140960795 + 8262024 * 2 ^ 59
def prefixEnd_8262024 : Nat := 4983230072969 + 3 ^ 40 * 8262024 * 2
def baseEnd_8262024 : Nat := 4242389490982488026803649

theorem tailTrace_8262024 : CollatzResearch.WordTrace tailWord_8262024 prefixEnd_8262024 4242389490982488026803649 := by
  unfold tailWord_8262024
  simp only [CollatzResearch.WordTrace]
  refine ⟨150670385710052782102784563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200893847613403709470379417 150670385710052782102784563)
  ·
    refine ⟨226005578565079173154176845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150670385710052782102784563 226005578565079173154176845)
    ·
      refine ⟨84752091961904689932816317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226005578565079173154176845 84752091961904689932816317)
      ·
        refine ⟨31782034485714258724806119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84752091961904689932816317 31782034485714258724806119)
        ·
          refine ⟨47673051728571388087209179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31782034485714258724806119 47673051728571388087209179)
          ·
            refine ⟨71509577592857082130813769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47673051728571388087209179 71509577592857082130813769)
            ·
              refine ⟨53632183194642811598110327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71509577592857082130813769 53632183194642811598110327)
              ·
                refine ⟨80448274791964217397165491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53632183194642811598110327 80448274791964217397165491)
                ·
                  refine ⟨120672412187946326095748237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80448274791964217397165491 120672412187946326095748237)
                  ·
                    refine ⟨45252154570479872285905589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120672412187946326095748237 45252154570479872285905589)
                    ·
                      refine ⟨4242389490982488026803649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45252154570479872285905589 4242389490982488026803649)
                      ·
                        rfl

theorem cell23_8262024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_8262024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262024 prefixEnd_8262024 := by exact prefixLift 8262024
  have htrace : WordTrace (prefixWord ++ tailWord_8262024) baseStart_8262024 baseEnd_8262024 := by
    simpa [prefixWord, tailWord_8262024, baseEnd_8262024] using wordTrace_append hprefix tailTrace_8262024
  have hstable : (prefixWord ++ tailWord_8262024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262024).length < 2 ^ (prefixWord ++ tailWord_8262024).sum := by decide
  have hdescent : baseEnd_8262024 < baseStart_8262024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262025 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 1, 3, 2]
def baseStart_8262025 : Nat := 118140960795 + 8262025 * 2 ^ 59
def prefixEnd_8262025 : Nat := 4983230072969 + 3 ^ 40 * 8262025 * 2
def baseEnd_8262025 : Nat := 4242390004463142522891145

theorem tailTrace_8262025 : CollatzResearch.WordTrace tailWord_8262025 prefixEnd_8262025 4242390004463142522891145 := by
  unfold tailWord_8262025
  simp only [CollatzResearch.WordTrace]
  refine ⟨301340807893101941376355529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200893871928734627584237019 301340807893101941376355529)
  ·
    refine ⟨226005605919826456032266647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301340807893101941376355529 226005605919826456032266647)
    ·
      refine ⟨339008408879739684048399971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226005605919826456032266647 339008408879739684048399971)
      ·
        refine ⟨508512613319609526072599957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339008408879739684048399971 508512613319609526072599957)
        ·
          refine ⟨23836528749356696534653123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 508512613319609526072599957 23836528749356696534653123)
          ·
            refine ⟨35754793124035044801979685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23836528749356696534653123 35754793124035044801979685)
            ·
              refine ⟨6704023710756570900371191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35754793124035044801979685 6704023710756570900371191)
              ·
                refine ⟨10056035566134856350556787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6704023710756570900371191 10056035566134856350556787)
                ·
                  refine ⟨15084053349202284525835181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10056035566134856350556787 15084053349202284525835181)
                  ·
                    refine ⟨5656520005950856697188193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15084053349202284525835181 5656520005950856697188193)
                    ·
                      refine ⟨4242390004463142522891145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656520005950856697188193 4242390004463142522891145)
                      ·
                        rfl

theorem cell23_8262025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 3, 2].length) (baseStart_8262025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262025 prefixEnd_8262025 := by exact prefixLift 8262025
  have htrace : WordTrace (prefixWord ++ tailWord_8262025) baseStart_8262025 baseEnd_8262025 := by
    simpa [prefixWord, tailWord_8262025, baseEnd_8262025] using wordTrace_append hprefix tailTrace_8262025
  have hstable : (prefixWord ++ tailWord_8262025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262025).length < 2 ^ (prefixWord ++ tailWord_8262025).sum := by decide
  have hdescent : baseEnd_8262025 < baseStart_8262025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262055 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_8262055 : Nat := 118140960795 + 8262055 * 2 ^ 59
def prefixEnd_8262055 : Nat := 4983230072969 + 3 ^ 40 * 8262055 * 2
def baseEnd_8262055 : Nat := 4242405408882777405516007

theorem tailTrace_8262055 : CollatzResearch.WordTrace tailWord_8262055 prefixEnd_8262055 4242405408882777405516007 := by
  unfold tailWord_8262055
  simp only [CollatzResearch.WordTrace]
  refine ⟨301341902082993256499947619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200894601388662170999965079 301341902082993256499947619)
  ·
    refine ⟨452012853124489884749921429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301341902082993256499947619 452012853124489884749921429)
    ·
      refine ⟨21188102490210463347652567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 452012853124489884749921429 21188102490210463347652567)
      ·
        refine ⟨31782153735315695021478851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21188102490210463347652567 31782153735315695021478851)
        ·
          refine ⟨47673230602973542532218277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31782153735315695021478851 47673230602973542532218277)
          ·
            refine ⟨8938730738057539224790927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47673230602973542532218277 8938730738057539224790927)
            ·
              refine ⟨13408096107086308837186391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8938730738057539224790927 13408096107086308837186391)
              ·
                refine ⟨20112144160629463255779587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13408096107086308837186391 20112144160629463255779587)
                ·
                  refine ⟨30168216240944194883669381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20112144160629463255779587 30168216240944194883669381)
                  ·
                    refine ⟨5656540545177036540688009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30168216240944194883669381 5656540545177036540688009)
                    ·
                      refine ⟨4242405408882777405516007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656540545177036540688009 4242405408882777405516007)
                      ·
                        rfl

theorem cell23_8262055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_8262055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262055 prefixEnd_8262055 := by exact prefixLift 8262055
  have htrace : WordTrace (prefixWord ++ tailWord_8262055) baseStart_8262055 baseEnd_8262055 := by
    simpa [prefixWord, tailWord_8262055, baseEnd_8262055] using wordTrace_append hprefix tailTrace_8262055
  have hstable : (prefixWord ++ tailWord_8262055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262055).length < 2 ^ (prefixWord ++ tailWord_8262055).sum := by decide
  have hdescent : baseEnd_8262055 < baseStart_8262055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262074 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_8262074 : Nat := 118140960795 + 8262074 * 2 ^ 59
def prefixEnd_8262074 : Nat := 4983230072969 + 3 ^ 40 * 8262074 * 2
def baseEnd_8262074 : Nat := 1414138388338404277059473

theorem tailTrace_8262074 : CollatzResearch.WordTrace tailWord_8262074 prefixEnd_8262074 1414138388338404277059473 := by
  unfold tailWord_8262074
  simp only [CollatzResearch.WordTrace]
  refine ⟨75335648767481105686222319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200895063379949615163259517 75335648767481105686222319)
  ·
    refine ⟨113003473151221658529333479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75335648767481105686222319 113003473151221658529333479)
    ·
      refine ⟨169505209726832487794000219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113003473151221658529333479 169505209726832487794000219)
      ·
        refine ⟨254257814590248731691000329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169505209726832487794000219 254257814590248731691000329)
        ·
          refine ⟨190693360942686548768250247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254257814590248731691000329 190693360942686548768250247)
          ·
            refine ⟨286040041414029823152375371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190693360942686548768250247 286040041414029823152375371)
            ·
              refine ⟨429060062121044734728563057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286040041414029823152375371 429060062121044734728563057)
              ·
                refine ⟨321795046590783551046422293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429060062121044734728563057 321795046590783551046422293)
                ·
                  refine ⟨15084142808942978955301045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 321795046590783551046422293 15084142808942978955301045)
                  ·
                    refine ⟨1414138388338404277059473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15084142808942978955301045 1414138388338404277059473)
                    ·
                      rfl

theorem cell23_8262074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_8262074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262074 prefixEnd_8262074 := by exact prefixLift 8262074
  have htrace : WordTrace (prefixWord ++ tailWord_8262074) baseStart_8262074 baseEnd_8262074 := by
    simpa [prefixWord, tailWord_8262074, baseEnd_8262074] using wordTrace_append hprefix tailTrace_8262074
  have hstable : (prefixWord ++ tailWord_8262074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262074).length < 2 ^ (prefixWord ++ tailWord_8262074).sum := by decide
  have hdescent : baseEnd_8262074 < baseStart_8262074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262078 : List Nat := [4, 2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_8262078 : Nat := 118140960795 + 8262078 * 2 ^ 59
def prefixEnd_8262078 : Nat := 4983230072969 + 3 ^ 40 * 8262078 * 2
def baseEnd_8262078 : Nat := 471379690993092312836489

theorem tailTrace_8262078 : CollatzResearch.WordTrace tailWord_8262078 prefixEnd_8262078 471379690993092312836489 := by
  unfold tailWord_8262078
  simp only [CollatzResearch.WordTrace]
  refine ⟨37667842620238741428504361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200895160641273287618689925 37667842620238741428504361)
  ·
    refine ⟨28250881965179056071378271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37667842620238741428504361 28250881965179056071378271)
    ·
      refine ⟨42376322947768584107067407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28250881965179056071378271 42376322947768584107067407)
      ·
        refine ⟨63564484421652876160601111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42376322947768584107067407 63564484421652876160601111)
        ·
          refine ⟨95346726632479314240901667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63564484421652876160601111 95346726632479314240901667)
          ·
            refine ⟨143020089948718971361352501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95346726632479314240901667 143020089948718971361352501)
            ·
              refine ⟨13408133432692403565126797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143020089948718971361352501 13408133432692403565126797)
              ·
                refine ⟨5028050037259651336922549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13408133432692403565126797 5028050037259651336922549)
                ·
                  refine ⟨471379690993092312836489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5028050037259651336922549 471379690993092312836489)
                  ·
                    rfl

theorem cell23_8262078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_8262078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262078 prefixEnd_8262078 := by exact prefixLift 8262078
  have htrace : WordTrace (prefixWord ++ tailWord_8262078) baseStart_8262078 baseEnd_8262078 := by
    simpa [prefixWord, tailWord_8262078, baseEnd_8262078] using wordTrace_append hprefix tailTrace_8262078
  have hstable : (prefixWord ++ tailWord_8262078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262078).length < 2 ^ (prefixWord ++ tailWord_8262078).sum := by decide
  have hdescent : baseEnd_8262078 < baseStart_8262078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262101 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_8262101 : Nat := 118140960795 + 8262101 * 2 ^ 59
def prefixEnd_8262101 : Nat := 4983230072969 + 3 ^ 40 * 8262101 * 2
def baseEnd_8262101 : Nat := 4242429028992884225540795

theorem tailTrace_8262101 : CollatzResearch.WordTrace tailWord_8262101 prefixEnd_8262101 4242429028992884225540795 := by
  unfold tailWord_8262101
  simp only [CollatzResearch.WordTrace]
  refine ⟨301343579840826606356122157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200895719893884404237414771 301343579840826606356122157)
  ·
    refine ⟨113003842440309977383545809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301343579840826606356122157 113003842440309977383545809)
    ·
      refine ⟨84752881830232483037659357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113003842440309977383545809 84752881830232483037659357)
      ·
        refine ⟨31782330686337181139122259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84752881830232483037659357 31782330686337181139122259)
        ·
          refine ⟨47673496029505771708683389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31782330686337181139122259 47673496029505771708683389)
          ·
            refine ⟨17877561011064664390756271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47673496029505771708683389 17877561011064664390756271)
            ·
              refine ⟨26816341516596996586134407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17877561011064664390756271 26816341516596996586134407)
              ·
                refine ⟨40224512274895494879201611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26816341516596996586134407 40224512274895494879201611)
                ·
                  refine ⟨60336768412343242318802417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40224512274895494879201611 60336768412343242318802417)
                  ·
                    refine ⟨45252576309257431739101813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60336768412343242318802417 45252576309257431739101813)
                    ·
                      refine ⟨4242429028992884225540795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45252576309257431739101813 4242429028992884225540795)
                      ·
                        rfl

theorem cell23_8262101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_8262101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262101 prefixEnd_8262101 := by exact prefixLift 8262101
  have htrace : WordTrace (prefixWord ++ tailWord_8262101) baseStart_8262101 baseEnd_8262101 := by
    simpa [prefixWord, tailWord_8262101, baseEnd_8262101] using wordTrace_append hprefix tailTrace_8262101
  have hstable : (prefixWord ++ tailWord_8262101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262101).length < 2 ^ (prefixWord ++ tailWord_8262101).sum := by decide
  have hdescent : baseEnd_8262101 < baseStart_8262101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262155 : List Nat := [1, 1, 1, 1, 7, 2, 1, 4, 1, 4]
def baseStart_8262155 : Nat := 118140960795 + 8262155 * 2 ^ 59
def prefixEnd_8262155 : Nat := 4983230072969 + 3 ^ 40 * 8262155 * 2
def baseEnd_8262155 : Nat := 1414152252316075671421849

theorem tailTrace_8262155 : CollatzResearch.WordTrace tailWord_8262155 prefixEnd_8262155 1414152252316075671421849 := by
  unfold tailWord_8262155
  simp only [CollatzResearch.WordTrace]
  refine ⟨301345549382630973578587919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200897032921753982385725279 301345549382630973578587919)
  ·
    refine ⟨452018324073946460367881879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301345549382630973578587919 452018324073946460367881879)
    ·
      refine ⟨678027486110919690551822819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452018324073946460367881879 678027486110919690551822819)
      ·
        refine ⟨1017041229166379535827734229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678027486110919690551822819 1017041229166379535827734229)
        ·
          refine ⟨23836903808587020370962521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1017041229166379535827734229 23836903808587020370962521)
          ·
            refine ⟨17877677856440265278221891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23836903808587020370962521 17877677856440265278221891)
            ·
              refine ⟨26816516784660397917332837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17877677856440265278221891 26816516784660397917332837)
              ·
                refine ⟨5028096897123824609499907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26816516784660397917332837 5028096897123824609499907)
                ·
                  refine ⟨7542145345685736914249861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028096897123824609499907 7542145345685736914249861)
                  ·
                    refine ⟨1414152252316075671421849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7542145345685736914249861 1414152252316075671421849)
                    ·
                      rfl

theorem cell23_8262155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 1, 4].length) (baseStart_8262155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262155 prefixEnd_8262155 := by exact prefixLift 8262155
  have htrace : WordTrace (prefixWord ++ tailWord_8262155) baseStart_8262155 baseEnd_8262155 := by
    simpa [prefixWord, tailWord_8262155, baseEnd_8262155] using wordTrace_append hprefix tailTrace_8262155
  have hstable : (prefixWord ++ tailWord_8262155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262155).length < 2 ^ (prefixWord ++ tailWord_8262155).sum := by decide
  have hdescent : baseEnd_8262155 < baseStart_8262155 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262181 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_8262181 : Nat := 118140960795 + 8262181 * 2 ^ 59
def prefixEnd_8262181 : Nat := 4983230072969 + 3 ^ 40 * 8262181 * 2
def baseEnd_8262181 : Nat := 1414156702481747970846809

theorem tailTrace_8262181 : CollatzResearch.WordTrace tailWord_8262181 prefixEnd_8262181 1414156702481747970846809 := by
  unfold tailWord_8262181
  simp only [CollatzResearch.WordTrace]
  refine ⟨301346497680536780019034397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200897665120357853346022931 301346497680536780019034397)
  ·
    refine ⟨113004936630201292507137899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301346497680536780019034397 113004936630201292507137899)
    ·
      refine ⟨169507404945301938760706849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113004936630201292507137899 169507404945301938760706849)
      ·
        refine ⟨127130553708976454070530137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169507404945301938760706849 127130553708976454070530137)
        ·
          refine ⟨95347915281732340552897603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127130553708976454070530137 95347915281732340552897603)
          ·
            refine ⟨143021872922598510829346405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95347915281732340552897603 143021872922598510829346405)
            ·
              refine ⟨26816601172987220780502451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143021872922598510829346405 26816601172987220780502451)
              ·
                refine ⟨40224901759480831170753677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26816601172987220780502451 40224901759480831170753677)
                ·
                  refine ⟨15084338159805311689032629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40224901759480831170753677 15084338159805311689032629)
                  ·
                    refine ⟨1414156702481747970846809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15084338159805311689032629 1414156702481747970846809)
                    ·
                      rfl

theorem cell23_8262181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_8262181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262181 prefixEnd_8262181 := by exact prefixLift 8262181
  have htrace : WordTrace (prefixWord ++ tailWord_8262181) baseStart_8262181 baseEnd_8262181 := by
    simpa [prefixWord, tailWord_8262181, baseEnd_8262181] using wordTrace_append hprefix tailTrace_8262181
  have hstable : (prefixWord ++ tailWord_8262181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262181).length < 2 ^ (prefixWord ++ tailWord_8262181).sum := by decide
  have hdescent : baseEnd_8262181 < baseStart_8262181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262228 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_8262228 : Nat := 118140960795 + 8262228 * 2 ^ 59
def prefixEnd_8262228 : Nat := 4983230072969 + 3 ^ 40 * 8262228 * 2
def baseEnd_8262228 : Nat := 1414164747012001742884237

theorem tailTrace_8262228 : CollatzResearch.WordTrace tailWord_8262228 prefixEnd_8262228 1414164747012001742884237 := by
  unfold tailWord_8262228
  simp only [CollatzResearch.WordTrace]
  refine ⟨150674105955683253522997669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200898807940911004697330225 150674105955683253522997669)
  ·
    refine ⟨28251394866690610035562063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150674105955683253522997669 28251394866690610035562063)
    ·
      refine ⟨42377092300035915053343095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28251394866690610035562063 42377092300035915053343095)
      ·
        refine ⟨63565638450053872580014643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42377092300035915053343095 63565638450053872580014643)
        ·
          refine ⟨95348457675080808870021965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63565638450053872580014643 95348457675080808870021965)
          ·
            refine ⟨35755671628155303326258237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95348457675080808870021965 35755671628155303326258237)
            ·
              refine ⟨13408376860558238747346839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35755671628155303326258237 13408376860558238747346839)
              ·
                refine ⟨20112565290837358121020259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13408376860558238747346839 20112565290837358121020259)
                ·
                  refine ⟨30168847936256037181530389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20112565290837358121020259 30168847936256037181530389)
                  ·
                    refine ⟨1414164747012001742884237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30168847936256037181530389 1414164747012001742884237)
                    ·
                      rfl

theorem cell23_8262228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_8262228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262228 prefixEnd_8262228 := by exact prefixLift 8262228
  have htrace : WordTrace (prefixWord ++ tailWord_8262228) baseStart_8262228 baseEnd_8262228 := by
    simpa [prefixWord, tailWord_8262228, baseEnd_8262228] using wordTrace_append hprefix tailTrace_8262228
  have hstable : (prefixWord ++ tailWord_8262228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262228).length < 2 ^ (prefixWord ++ tailWord_8262228).sum := by decide
  have hdescent : baseEnd_8262228 < baseStart_8262228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262231 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_8262231 : Nat := 118140960795 + 8262231 * 2 ^ 59
def prefixEnd_8262231 : Nat := 4983230072969 + 3 ^ 40 * 8262231 * 2
def baseEnd_8262231 : Nat := 4242495781477968716915197

theorem tailTrace_8262231 : CollatzResearch.WordTrace tailWord_8262231 prefixEnd_8262231 4242495781477968716915197 := by
  unfold tailWord_8262231
  simp only [CollatzResearch.WordTrace]
  refine ⟨301348321330355638558354547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200898880886903759038903031 301348321330355638558354547)
  ·
    refine ⟨452022481995533457837531821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301348321330355638558354547 452022481995533457837531821)
    ·
      refine ⟨169508430748325046689074433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452022481995533457837531821 169508430748325046689074433)
      ·
        refine ⟨127131323061243785016805825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169508430748325046689074433 127131323061243785016805825)
        ·
          refine ⟨95348492295932838762604369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127131323061243785016805825 95348492295932838762604369)
          ·
            refine ⟨71511369221949629071953277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95348492295932838762604369 71511369221949629071953277)
            ·
              refine ⟨26816763458231110901982479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71511369221949629071953277 26816763458231110901982479)
              ·
                refine ⟨40225145187346666352973719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26816763458231110901982479 40225145187346666352973719)
                ·
                  refine ⟨60337717781019999529460579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40225145187346666352973719 60337717781019999529460579)
                  ·
                    refine ⟨90506576671529999294190869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60337717781019999529460579 90506576671529999294190869)
                    ·
                      refine ⟨4242495781477968716915197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90506576671529999294190869 4242495781477968716915197)
                      ·
                        rfl

theorem cell23_8262231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_8262231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262231 prefixEnd_8262231 := by exact prefixLift 8262231
  have htrace : WordTrace (prefixWord ++ tailWord_8262231) baseStart_8262231 baseEnd_8262231 := by
    simpa [prefixWord, tailWord_8262231, baseEnd_8262231] using wordTrace_append hprefix tailTrace_8262231
  have hstable : (prefixWord ++ tailWord_8262231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262231).length < 2 ^ (prefixWord ++ tailWord_8262231).sum := by decide
  have hdescent : baseEnd_8262231 < baseStart_8262231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262241 : List Nat := [1, 2, 3, 1, 1, 5, 1, 9]
def baseStart_8262241 : Nat := 118140960795 + 8262241 * 2 ^ 59
def prefixEnd_8262241 : Nat := 4983230072969 + 3 ^ 40 * 8262241 * 2
def baseEnd_8262241 : Nat := 157129663566093099177413

theorem tailTrace_8262241 : CollatzResearch.WordTrace tailWord_8262241 prefixEnd_8262241 157129663566093099177413 := by
  unfold tailWord_8262241
  simp only [CollatzResearch.WordTrace]
  refine ⟨301348686060319410266218577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200899124040212940177479051 301348686060319410266218577)
  ·
    refine ⟨226011514545239557699663933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301348686060319410266218577 226011514545239557699663933)
    ·
      refine ⟨84754317954464834137373975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226011514545239557699663933 84754317954464834137373975)
      ·
        refine ⟨127131476931697251206060963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84754317954464834137373975 127131476931697251206060963)
        ·
          refine ⟨190697215397545876809091445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127131476931697251206060963 190697215397545876809091445)
          ·
            refine ⟨17877863943519925950852323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190697215397545876809091445 17877863943519925950852323)
            ·
              refine ⟨26816795915279888926278485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17877863943519925950852323 26816795915279888926278485)
              ·
                refine ⟨157129663566093099177413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26816795915279888926278485 157129663566093099177413)
                ·
                  rfl

theorem cell23_8262241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 9].length) (baseStart_8262241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262241 prefixEnd_8262241 := by exact prefixLift 8262241
  have htrace : WordTrace (prefixWord ++ tailWord_8262241) baseStart_8262241 baseEnd_8262241 := by
    simpa [prefixWord, tailWord_8262241, baseEnd_8262241] using wordTrace_append hprefix tailTrace_8262241
  have hstable : (prefixWord ++ tailWord_8262241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262241).length < 2 ^ (prefixWord ++ tailWord_8262241).sum := by decide
  have hdescent : baseEnd_8262241 < baseStart_8262241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262258 : List Nat := [3, 2, 1, 2, 4, 2, 9]
def baseStart_8262258 : Nat := 118140960795 + 8262258 * 2 ^ 59
def prefixEnd_8262258 : Nat := 4983230072969 + 3 ^ 40 * 8262258 * 2
def baseEnd_8262258 : Nat := 52376662289575803842933

theorem tailTrace_8262258 : CollatzResearch.WordTrace tailWord_8262258 prefixEnd_8262258 52376662289575803842933 := by
  unfold tailWord_8262258
  simp only [CollatzResearch.WordTrace]
  refine ⟨75337326525314455542396857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200899537400838548113058285 75337326525314455542396857)
  ·
    refine ⟨56502994893985841656797643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75337326525314455542396857 56502994893985841656797643)
    ·
      refine ⟨84754492340978762485196465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56502994893985841656797643 84754492340978762485196465)
      ·
        refine ⟨63565869255734071863897349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84754492340978762485196465 63565869255734071863897349)
        ·
          refine ⟨11918600485450138474480753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63565869255734071863897349 11918600485450138474480753)
          ·
            refine ⟨8938950364087603855860565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11918600485450138474480753 8938950364087603855860565)
            ·
              refine ⟨52376662289575803842933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8938950364087603855860565 52376662289575803842933)
              ·
                rfl

theorem cell23_8262258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 9].length) (baseStart_8262258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262258 prefixEnd_8262258 := by exact prefixLift 8262258
  have htrace : WordTrace (prefixWord ++ tailWord_8262258) baseStart_8262258 baseEnd_8262258 := by
    simpa [prefixWord, tailWord_8262258, baseEnd_8262258] using wordTrace_append hprefix tailTrace_8262258
  have hstable : (prefixWord ++ tailWord_8262258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262258).length < 2 ^ (prefixWord ++ tailWord_8262258).sum := by decide
  have hdescent : baseEnd_8262258 < baseStart_8262258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262269 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 3, 2, 2]
def baseStart_8262269 : Nat := 118140960795 + 8262269 * 2 ^ 59
def prefixEnd_8262269 : Nat := 4983230072969 + 3 ^ 40 * 8262269 * 2
def baseEnd_8262269 : Nat := 4242515293742839568240023

theorem tailTrace_8262269 : CollatzResearch.WordTrace tailWord_8262269 prefixEnd_8262269 4242515293742839568240023 := by
  unfold tailWord_8262269
  simp only [CollatzResearch.WordTrace]
  refine ⟨301349707304217971048237861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200899804869478647365491907 301349707304217971048237861)
  ·
    refine ⟨56503070119540869571544599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301349707304217971048237861 56503070119540869571544599)
    ·
      refine ⟨84754605179311304357316899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56503070119540869571544599 84754605179311304357316899)
      ·
        refine ⟨127131907768966956535975349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84754605179311304357316899 127131907768966956535975349)
        ·
          refine ⟨11918616353340652175247689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127131907768966956535975349 11918616353340652175247689)
          ·
            refine ⟨8938962265005489131435767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11918616353340652175247689 8938962265005489131435767)
            ·
              refine ⟨13408443397508233697153651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8938962265005489131435767 13408443397508233697153651)
              ·
                refine ⟨20112665096262350545730477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13408443397508233697153651 20112665096262350545730477)
                ·
                  refine ⟨7542249411098381454648929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20112665096262350545730477 7542249411098381454648929)
                  ·
                    refine ⟨5656687058323786090986697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7542249411098381454648929 5656687058323786090986697)
                    ·
                      refine ⟨4242515293742839568240023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656687058323786090986697 4242515293742839568240023)
                      ·
                        rfl

theorem cell23_8262269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_8262269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262269 prefixEnd_8262269 := by exact prefixLift 8262269
  have htrace : WordTrace (prefixWord ++ tailWord_8262269) baseStart_8262269 baseEnd_8262269 := by
    simpa [prefixWord, tailWord_8262269, baseEnd_8262269] using wordTrace_append hprefix tailTrace_8262269
  have hstable : (prefixWord ++ tailWord_8262269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262269).length < 2 ^ (prefixWord ++ tailWord_8262269).sum := by decide
  have hdescent : baseEnd_8262269 < baseStart_8262269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262291 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 4]
def baseStart_8262291 : Nat := 118140960795 + 8262291 * 2 ^ 59
def prefixEnd_8262291 : Nat := 4983230072969 + 3 ^ 40 * 8262291 * 2
def baseEnd_8262291 : Nat := 4242526590317238482164921

theorem tailTrace_8262291 : CollatzResearch.WordTrace tailWord_8262291 prefixEnd_8262291 4242526590317238482164921 := by
  unfold tailWord_8262291
  simp only [CollatzResearch.WordTrace]
  refine ⟨301350509710138268805538727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200900339806758845870359151 301350509710138268805538727)
  ·
    refine ⟨452025764565207403208308091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301350509710138268805538727 452025764565207403208308091)
    ·
      refine ⟨678038646847811104812462137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452025764565207403208308091 678038646847811104812462137)
      ·
        refine ⟨508528985135858328609346603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678038646847811104812462137 508528985135858328609346603)
        ·
          refine ⟨762793477703787492914019905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508528985135858328609346603 762793477703787492914019905)
          ·
            refine ⟨572095108277840619685514929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762793477703787492914019905 572095108277840619685514929)
            ·
              refine ⟨429071331208380464764136197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572095108277840619685514929 429071331208380464764136197)
              ·
                refine ⟨80450874601571337143275537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429071331208380464764136197 80450874601571337143275537)
                ·
                  refine ⟨60338155951178502857456653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80450874601571337143275537 60338155951178502857456653)
                  ·
                    refine ⟨22626808481691938571546245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60338155951178502857456653 22626808481691938571546245)
                    ·
                      refine ⟨4242526590317238482164921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22626808481691938571546245 4242526590317238482164921)
                      ·
                        rfl

theorem cell23_8262291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_8262291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262291 prefixEnd_8262291 := by exact prefixLift 8262291
  have htrace : WordTrace (prefixWord ++ tailWord_8262291) baseStart_8262291 baseEnd_8262291 := by
    simpa [prefixWord, tailWord_8262291, baseEnd_8262291] using wordTrace_append hprefix tailTrace_8262291
  have hstable : (prefixWord ++ tailWord_8262291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262291).length < 2 ^ (prefixWord ++ tailWord_8262291).sum := by decide
  have hdescent : baseEnd_8262291 < baseStart_8262291 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262295 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 3, 3, 2]
def baseStart_8262295 : Nat := 118140960795 + 8262295 * 2 ^ 59
def prefixEnd_8262295 : Nat := 4983230072969 + 3 ^ 40 * 8262295 * 2
def baseEnd_8262295 : Nat := 4242528644239856466514903

theorem tailTrace_8262295 : CollatzResearch.WordTrace tailWord_8262295 prefixEnd_8262295 4242528644239856466514903 := by
  unfold tailWord_8262295
  simp only [CollatzResearch.WordTrace]
  refine ⟨301350655602123777488684339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200900437068082518325789559 301350655602123777488684339)
  ·
    refine ⟨452025983403185666233026509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301350655602123777488684339 452025983403185666233026509)
    ·
      refine ⟨169509743776194624837384941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452025983403185666233026509 169509743776194624837384941)
      ·
        refine ⟨63566153916072984314019353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169509743776194624837384941 63566153916072984314019353)
        ·
          refine ⟨47674615437054738235514515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63566153916072984314019353 47674615437054738235514515)
          ·
            refine ⟨71511923155582107353271773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47674615437054738235514515 71511923155582107353271773)
            ·
              refine ⟨26816971183343290257476915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71511923155582107353271773 26816971183343290257476915)
              ·
                refine ⟨40225456775014935386215373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26816971183343290257476915 40225456775014935386215373)
                ·
                  refine ⟨15084546290630600769830765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40225456775014935386215373 15084546290630600769830765)
                  ·
                    refine ⟨5656704858986475288686537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15084546290630600769830765 5656704858986475288686537)
                    ·
                      refine ⟨4242528644239856466514903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656704858986475288686537 4242528644239856466514903)
                      ·
                        rfl

theorem cell23_8262295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_8262295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262295 prefixEnd_8262295 := by exact prefixLift 8262295
  have htrace : WordTrace (prefixWord ++ tailWord_8262295) baseStart_8262295 baseEnd_8262295 := by
    simpa [prefixWord, tailWord_8262295, baseEnd_8262295] using wordTrace_append hprefix tailTrace_8262295
  have hstable : (prefixWord ++ tailWord_8262295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262295).length < 2 ^ (prefixWord ++ tailWord_8262295).sum := by decide
  have hdescent : baseEnd_8262295 < baseStart_8262295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262348 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 9]
def baseStart_8262348 : Nat := 118140960795 + 8262348 * 2 ^ 59
def prefixEnd_8262348 : Nat := 4983230072969 + 3 ^ 40 * 8262348 * 2
def baseEnd_8262348 : Nat := 471395095412727195461351

theorem tailTrace_8262348 : CollatzResearch.WordTrace tailWord_8262348 prefixEnd_8262348 471395095412727195461351 := by
  unfold tailWord_8262348
  simp only [CollatzResearch.WordTrace]
  refine ⟨150676294335465883770181849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200901725780621178360242465 150676294335465883770181849)
  ·
    refine ⟨113007220751599412827636387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150676294335465883770181849 113007220751599412827636387)
    ·
      refine ⟨169510831127399119241454581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113007220751599412827636387 169510831127399119241454581)
      ·
        refine ⟨15891640418193667428886367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169510831127399119241454581 15891640418193667428886367)
        ·
          refine ⟨23837460627290501143329551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15891640418193667428886367 23837460627290501143329551)
          ·
            refine ⟨35756190940935751714994327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23837460627290501143329551 35756190940935751714994327)
            ·
              refine ⟨53634286411403627572491491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35756190940935751714994327 53634286411403627572491491)
              ·
                refine ⟨80451429617105441358737237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53634286411403627572491491 80451429617105441358737237)
                ·
                  refine ⟨471395095412727195461351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80451429617105441358737237 471395095412727195461351)
                  ·
                    rfl

theorem cell23_8262348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_8262348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262348 prefixEnd_8262348 := by exact prefixLift 8262348
  have htrace : WordTrace (prefixWord ++ tailWord_8262348) baseStart_8262348 baseEnd_8262348 := by
    simpa [prefixWord, tailWord_8262348, baseEnd_8262348] using wordTrace_append hprefix tailTrace_8262348
  have hstable : (prefixWord ++ tailWord_8262348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262348).length < 2 ^ (prefixWord ++ tailWord_8262348).sum := by decide
  have hdescent : baseEnd_8262348 < baseStart_8262348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262376 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_8262376 : Nat := 118140960795 + 8262376 * 2 ^ 59
def prefixEnd_8262376 : Nat := 4983230072969 + 3 ^ 40 * 8262376 * 2
def baseEnd_8262376 : Nat := 4242570236172870649602031

theorem tailTrace_8262376 : CollatzResearch.WordTrace tailWord_8262376 prefixEnd_8262376 4242570236172870649602031 := by
  unfold tailWord_8262376
  simp only [CollatzResearch.WordTrace]
  refine ⟨150676804957415164161191491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200902406609886885548255321 150676804957415164161191491)
  ·
    refine ⟨226015207436122746241787237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150676804957415164161191491 226015207436122746241787237)
    ·
      refine ⟨42377851394273014920335107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226015207436122746241787237 42377851394273014920335107)
      ·
        refine ⟨63566777091409522380502661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42377851394273014920335107 63566777091409522380502661)
        ·
          refine ⟨11918770704639285446344249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63566777091409522380502661 11918770704639285446344249)
          ·
            refine ⟨8939078028479464084758187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11918770704639285446344249 8939078028479464084758187)
            ·
              refine ⟨13408617042719196127137281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8939078028479464084758187 13408617042719196127137281)
              ·
                refine ⟨10056462782039397095352961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13408617042719196127137281 10056462782039397095352961)
                ·
                  refine ⟨7542347086529547821514721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10056462782039397095352961 7542347086529547821514721)
                  ·
                    refine ⟨5656760314897160866136041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7542347086529547821514721 5656760314897160866136041)
                    ·
                      refine ⟨4242570236172870649602031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656760314897160866136041 4242570236172870649602031)
                      ·
                        rfl

theorem cell23_8262376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_8262376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262376 prefixEnd_8262376 := by exact prefixLift 8262376
  have htrace : WordTrace (prefixWord ++ tailWord_8262376) baseStart_8262376 baseEnd_8262376 := by
    simpa [prefixWord, tailWord_8262376, baseEnd_8262376] using wordTrace_append hprefix tailTrace_8262376
  have hstable : (prefixWord ++ tailWord_8262376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262376).length < 2 ^ (prefixWord ++ tailWord_8262376).sum := by decide
  have hdescent : baseEnd_8262376 < baseStart_8262376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262378 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_8262378 : Nat := 118140960795 + 8262378 * 2 ^ 59
def prefixEnd_8262378 : Nat := 4983230072969 + 3 ^ 40 * 8262378 * 2
def baseEnd_8262378 : Nat := 1414190421044726547259007

theorem tailTrace_8262378 : CollatzResearch.WordTrace tailWord_8262378 prefixEnd_8262378 1414190421044726547259007 := by
  unfold tailWord_8262378
  simp only [CollatzResearch.WordTrace]
  refine ⟨75338420715205770665988947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200902455240548721775970525 75338420715205770665988947)
  ·
    refine ⟨113007631072808655998983421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75338420715205770665988947 113007631072808655998983421)
    ·
      refine ⟨42377861652303245999618783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113007631072808655998983421 42377861652303245999618783)
      ·
        refine ⟨63566792478454868999428175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42377861652303245999618783 63566792478454868999428175)
        ·
          refine ⟨95350188717682303499142263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63566792478454868999428175 95350188717682303499142263)
          ·
            refine ⟨143025283076523455248713395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95350188717682303499142263 143025283076523455248713395)
            ·
              refine ⟨214537924614785182873070093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143025283076523455248713395 214537924614785182873070093)
              ·
                refine ⟨80451721730544443577401285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214537924614785182873070093 80451721730544443577401285)
                ·
                  refine ⟨15084697824477083170762741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80451721730544443577401285 15084697824477083170762741)
                  ·
                    refine ⟨1414190421044726547259007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15084697824477083170762741 1414190421044726547259007)
                    ·
                      rfl

theorem cell23_8262378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_8262378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262378 prefixEnd_8262378 := by exact prefixLift 8262378
  have htrace : WordTrace (prefixWord ++ tailWord_8262378) baseStart_8262378 baseEnd_8262378 := by
    simpa [prefixWord, tailWord_8262378, baseEnd_8262378] using wordTrace_append hprefix tailTrace_8262378
  have hstable : (prefixWord ++ tailWord_8262378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262378).length < 2 ^ (prefixWord ++ tailWord_8262378).sum := by decide
  have hdescent : baseEnd_8262378 < baseStart_8262378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262478 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_8262478 : Nat := 118140960795 + 8262478 * 2 ^ 59
def prefixEnd_8262478 : Nat := 4983230072969 + 3 ^ 40 * 8262478 * 2
def baseEnd_8262478 : Nat := 4242622611199629250526561

theorem tailTrace_8262478 : CollatzResearch.WordTrace tailWord_8262478 prefixEnd_8262478 4242622611199629250526561 := by
  unfold tailWord_8262478
  simp only [CollatzResearch.WordTrace]
  refine ⟨37669666270057599967824511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200904886773640533161730725 37669666270057599967824511)
  ·
    refine ⟨56504499405086399951736767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37669666270057599967824511 56504499405086399951736767)
    ·
      refine ⟨84756749107629599927605151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56504499405086399951736767 84756749107629599927605151)
      ·
        refine ⟨127135123661444399891407727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84756749107629599927605151 127135123661444399891407727)
        ·
          refine ⟨190702685492166599837111591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127135123661444399891407727 190702685492166599837111591)
          ·
            refine ⟨286054028238249899755667387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190702685492166599837111591 286054028238249899755667387)
            ·
              refine ⟨429081042357374849633501081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286054028238249899755667387 429081042357374849633501081)
              ·
                refine ⟨321810781768031137225125811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429081042357374849633501081 321810781768031137225125811)
                ·
                  refine ⟨482716172652046705837688717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321810781768031137225125811 482716172652046705837688717)
                  ·
                    refine ⟨181018564744517514689133269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482716172652046705837688717 181018564744517514689133269)
                    ·
                      refine ⟨4242622611199629250526561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181018564744517514689133269 4242622611199629250526561)
                      ·
                        rfl

theorem cell23_8262478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_8262478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262478 prefixEnd_8262478 := by exact prefixLift 8262478
  have htrace : WordTrace (prefixWord ++ tailWord_8262478) baseStart_8262478 baseEnd_8262478 := by
    simpa [prefixWord, tailWord_8262478, baseEnd_8262478] using wordTrace_append hprefix tailTrace_8262478
  have hstable : (prefixWord ++ tailWord_8262478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262478).length < 2 ^ (prefixWord ++ tailWord_8262478).sum := by decide
  have hdescent : baseEnd_8262478 < baseStart_8262478 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262505 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 4, 6, 2]
def baseStart_8262505 : Nat := 118140960795 + 8262505 * 2 ^ 59
def prefixEnd_8262505 : Nat := 4983230072969 + 3 ^ 40 * 8262505 * 2
def baseEnd_8262505 : Nat := 4242636475177300644888937

theorem tailTrace_8262505 : CollatzResearch.WordTrace tailWord_8262505 prefixEnd_8262505 4242636475177300644888937 := by
  unfold tailWord_8262505
  simp only [CollatzResearch.WordTrace]
  refine ⟨301358314931362983353828969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200905543287575322235885979 301358314931362983353828969)
  ·
    refine ⟨226018736198522237515371727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301358314931362983353828969 226018736198522237515371727)
    ·
      refine ⟨339028104297783356273057591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226018736198522237515371727 339028104297783356273057591)
      ·
        refine ⟨508542156446675034409586387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339028104297783356273057591 508542156446675034409586387)
        ·
          refine ⟨762813234670012551614379581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508542156446675034409586387 762813234670012551614379581)
          ·
            refine ⟨286054963001254706855392343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 762813234670012551614379581 286054963001254706855392343)
            ·
              refine ⟨429082444501882060283088515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286054963001254706855392343 429082444501882060283088515)
              ·
                refine ⟨643623666752823090424632773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429082444501882060283088515 643623666752823090424632773)
                ·
                  refine ⟨120679437516154329454618645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 643623666752823090424632773 120679437516154329454618645)
                  ·
                    refine ⟨5656848633569734193185249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120679437516154329454618645 5656848633569734193185249)
                    ·
                      refine ⟨4242636475177300644888937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656848633569734193185249 4242636475177300644888937)
                      ·
                        rfl

theorem cell23_8262505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 6, 2].length) (baseStart_8262505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262505 prefixEnd_8262505 := by exact prefixLift 8262505
  have htrace : WordTrace (prefixWord ++ tailWord_8262505) baseStart_8262505 baseEnd_8262505 := by
    simpa [prefixWord, tailWord_8262505, baseEnd_8262505] using wordTrace_append hprefix tailTrace_8262505
  have hstable : (prefixWord ++ tailWord_8262505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262505).length < 2 ^ (prefixWord ++ tailWord_8262505).sum := by decide
  have hdescent : baseEnd_8262505 < baseStart_8262505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262526 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_8262526 : Nat := 118140960795 + 8262526 * 2 ^ 59
def prefixEnd_8262526 : Nat := 4983230072969 + 3 ^ 40 * 8262526 * 2
def baseEnd_8262526 : Nat := 4242647258271045062726341

theorem tailTrace_8262526 : CollatzResearch.WordTrace tailWord_8262526 prefixEnd_8262526 4242647258271045062726341 := by
  unfold tailWord_8262526
  simp only [CollatzResearch.WordTrace]
  refine ⟨37669885108035862992542929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200906053909524602626895621 37669885108035862992542929)
  ·
    refine ⟨28252413831026897244407197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37669885108035862992542929 28252413831026897244407197)
    ·
      refine ⟨10594655186635086466652699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28252413831026897244407197 10594655186635086466652699)
      ·
        refine ⟨15891982779952629699979049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10594655186635086466652699 15891982779952629699979049)
        ·
          refine ⟨11918987084964472274984287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15891982779952629699979049 11918987084964472274984287)
          ·
            refine ⟨17878480627446708412476431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11918987084964472274984287 17878480627446708412476431)
            ·
              refine ⟨26817720941170062618714647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17878480627446708412476431 26817720941170062618714647)
              ·
                refine ⟨40226581411755093928071971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26817720941170062618714647 40226581411755093928071971)
                ·
                  refine ⟨60339872117632640892107957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40226581411755093928071971 60339872117632640892107957)
                  ·
                    refine ⟨5656863011028060083635121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60339872117632640892107957 5656863011028060083635121)
                    ·
                      refine ⟨4242647258271045062726341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656863011028060083635121 4242647258271045062726341)
                      ·
                        rfl

theorem cell23_8262526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_8262526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262526 prefixEnd_8262526 := by exact prefixLift 8262526
  have htrace : WordTrace (prefixWord ++ tailWord_8262526) baseStart_8262526 baseEnd_8262526 := by
    simpa [prefixWord, tailWord_8262526, baseEnd_8262526] using wordTrace_append hprefix tailTrace_8262526
  have hstable : (prefixWord ++ tailWord_8262526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262526).length < 2 ^ (prefixWord ++ tailWord_8262526).sum := by decide
  have hdescent : baseEnd_8262526 < baseStart_8262526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262549 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 2, 4]
def baseStart_8262549 : Nat := 118140960795 + 8262549 * 2 ^ 59
def prefixEnd_8262549 : Nat := 4983230072969 + 3 ^ 40 * 8262549 * 2
def baseEnd_8262549 : Nat := 1414219689442032824246245

theorem tailTrace_8262549 : CollatzResearch.WordTrace tailWord_8262549 prefixEnd_8262549 1414219689442032824246245 := by
  unfold tailWord_8262549
  simp only [CollatzResearch.WordTrace]
  refine ⟨301359919743203578868430701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200906613162135719245620467 301359919743203578868430701)
  ·
    refine ⟨113009969903701342075661513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301359919743203578868430701 113009969903701342075661513)
    ·
      refine ⟨84757477427776006556746135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113009969903701342075661513 84757477427776006556746135)
      ·
        refine ⟨127136216141664009835119203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84757477427776006556746135 127136216141664009835119203)
        ·
          refine ⟨190704324212496014752678805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127136216141664009835119203 190704324212496014752678805)
          ·
            refine ⟨8939265197460750691531819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190704324212496014752678805 8939265197460750691531819)
            ·
              refine ⟨13408897796191126037297729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8939265197460750691531819 13408897796191126037297729)
              ·
                refine ⟨10056673347143344527973297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13408897796191126037297729 10056673347143344527973297)
                ·
                  refine ⟨7542505010357508395979973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10056673347143344527973297 7542505010357508395979973)
                  ·
                    refine ⟨1414219689442032824246245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7542505010357508395979973 1414219689442032824246245)
                    ·
                      rfl

theorem cell23_8262549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_8262549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262549 prefixEnd_8262549 := by exact prefixLift 8262549
  have htrace : WordTrace (prefixWord ++ tailWord_8262549) baseStart_8262549 baseEnd_8262549 := by
    simpa [prefixWord, tailWord_8262549, baseEnd_8262549] using wordTrace_append hprefix tailTrace_8262549
  have hstable : (prefixWord ++ tailWord_8262549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262549).length < 2 ^ (prefixWord ++ tailWord_8262549).sum := by decide
  have hdescent : baseEnd_8262549 < baseStart_8262549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262550 : List Nat := [5, 3, 1, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_8262550 : Nat := 118140960795 + 8262550 * 2 ^ 59
def prefixEnd_8262550 : Nat := 4983230072969 + 3 ^ 40 * 8262550 * 2
def baseEnd_8262550 : Nat := 4242659581806752968826231

theorem tailTrace_8262550 : CollatzResearch.WordTrace tailWord_8262550 prefixEnd_8262550 4242659581806752968826231 := by
  unfold tailWord_8262550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18834997263512497252451069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200906637477466637359478069 18834997263512497252451069)
  ·
    refine ⟨7063123973817186469669151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18834997263512497252451069 7063123973817186469669151)
    ·
      refine ⟨10594685960725779704503727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7063123973817186469669151 10594685960725779704503727)
      ·
        refine ⟨15892028941088669556755591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10594685960725779704503727 15892028941088669556755591)
        ·
          refine ⟨23838043411633004335133387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15892028941088669556755591 23838043411633004335133387)
          ·
            refine ⟨35757065117449506502700081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23838043411633004335133387 35757065117449506502700081)
            ·
              refine ⟨26817798838087129877025061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35757065117449506502700081 26817798838087129877025061)
              ·
                refine ⟨5028337282141336851942199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26817798838087129877025061 5028337282141336851942199)
                ·
                  refine ⟨7542505923212005277913299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028337282141336851942199 7542505923212005277913299)
                  ·
                    refine ⟨11313758884818007916869949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7542505923212005277913299 11313758884818007916869949)
                    ·
                      refine ⟨4242659581806752968826231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11313758884818007916869949 4242659581806752968826231)
                      ·
                        rfl

theorem cell23_8262550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_8262550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262550 prefixEnd_8262550 := by exact prefixLift 8262550
  have htrace : WordTrace (prefixWord ++ tailWord_8262550) baseStart_8262550 baseEnd_8262550 := by
    simpa [prefixWord, tailWord_8262550, baseEnd_8262550] using wordTrace_append hprefix tailTrace_8262550
  have hstable : (prefixWord ++ tailWord_8262550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262550).length < 2 ^ (prefixWord ++ tailWord_8262550).sum := by decide
  have hdescent : baseEnd_8262550 < baseStart_8262550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262585 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 5]
def baseStart_8262585 : Nat := 118140960795 + 8262585 * 2 ^ 59
def prefixEnd_8262585 : Nat := 4983230072969 + 3 ^ 40 * 8262585 * 2
def baseEnd_8262585 : Nat := 4242677553629660331888569

theorem tailTrace_8262585 : CollatzResearch.WordTrace tailWord_8262585 prefixEnd_8262585 4242677553629660331888569 := by
  unfold tailWord_8262585
  simp only [CollatzResearch.WordTrace]
  refine ⟨301361232771073157016741209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200907488514048771344494139 301361232771073157016741209)
  ·
    refine ⟨226020924578304867762555907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301361232771073157016741209 226020924578304867762555907)
    ·
      refine ⟨339031386867457301643833861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226020924578304867762555907 339031386867457301643833861)
      ·
        refine ⟨63568385037648244058218849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339031386867457301643833861 63568385037648244058218849)
        ·
          refine ⟨47676288778236183043664137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63568385037648244058218849 47676288778236183043664137)
          ·
            refine ⟨35757216583677137282748103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47676288778236183043664137 35757216583677137282748103)
            ·
              refine ⟨53635824875515705924122155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35757216583677137282748103 53635824875515705924122155)
              ·
                refine ⟨80453737313273558886183233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53635824875515705924122155 80453737313273558886183233)
                ·
                  refine ⟨60340302984955169164637425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80453737313273558886183233 60340302984955169164637425)
                  ·
                    refine ⟨45255227238716376873478069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60340302984955169164637425 45255227238716376873478069)
                    ·
                      refine ⟨4242677553629660331888569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45255227238716376873478069 4242677553629660331888569)
                      ·
                        rfl

theorem cell23_8262585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_8262585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262585 prefixEnd_8262585 := by exact prefixLift 8262585
  have htrace : WordTrace (prefixWord ++ tailWord_8262585) baseStart_8262585 baseEnd_8262585 := by
    simpa [prefixWord, tailWord_8262585, baseEnd_8262585] using wordTrace_append hprefix tailTrace_8262585
  have hstable : (prefixWord ++ tailWord_8262585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262585).length < 2 ^ (prefixWord ++ tailWord_8262585).sum := by decide
  have hdescent : baseEnd_8262585 < baseStart_8262585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262599 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 1, 3, 2]
def baseStart_8262599 : Nat := 118140960795 + 8262599 * 2 ^ 59
def prefixEnd_8262599 : Nat := 4983230072969 + 3 ^ 40 * 8262599 * 2
def baseEnd_8262599 : Nat := 4242684742358823277113505

theorem tailTrace_8262599 : CollatzResearch.WordTrace tailWord_8262599 prefixEnd_8262599 4242684742358823277113505 := by
  unfold tailWord_8262599
  simp only [CollatzResearch.WordTrace]
  refine ⟨301361743393022437407750851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200907828928681624938500567 301361743393022437407750851)
  ·
    refine ⟨452042615089533656111626277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301361743393022437407750851 452042615089533656111626277)
    ·
      refine ⟨84757990329287560520929927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452042615089533656111626277 84757990329287560520929927)
      ·
        refine ⟨127136985493931340781394891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84757990329287560520929927 127136985493931340781394891)
        ·
          refine ⟨190705478240897011172092337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127136985493931340781394891 190705478240897011172092337)
          ·
            refine ⟨143029108680672758379069253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190705478240897011172092337 143029108680672758379069253)
            ·
              refine ⟨26817957877626142196075485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143029108680672758379069253 26817957877626142196075485)
              ·
                refine ⟨10056734204109803323528307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26817957877626142196075485 10056734204109803323528307)
                ·
                  refine ⟨15085101306164704985292461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10056734204109803323528307 15085101306164704985292461)
                  ·
                    refine ⟨5656912989811764369484673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15085101306164704985292461 5656912989811764369484673)
                    ·
                      refine ⟨4242684742358823277113505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656912989811764369484673 4242684742358823277113505)
                      ·
                        rfl

theorem cell23_8262599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_8262599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262599 prefixEnd_8262599 := by exact prefixLift 8262599
  have htrace : WordTrace (prefixWord ++ tailWord_8262599) baseStart_8262599 baseEnd_8262599 := by
    simpa [prefixWord, tailWord_8262599, baseEnd_8262599] using wordTrace_append hprefix tailTrace_8262599
  have hstable : (prefixWord ++ tailWord_8262599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262599).length < 2 ^ (prefixWord ++ tailWord_8262599).sum := by decide
  have hdescent : baseEnd_8262599 < baseStart_8262599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262623 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 2, 1, 3]
def baseStart_8262623 : Nat := 118140960795 + 8262623 * 2 ^ 59
def prefixEnd_8262623 : Nat := 4983230072969 + 3 ^ 40 * 8262623 * 2
def baseEnd_8262623 : Nat := 4242697065894531183213395

theorem tailTrace_8262623 : CollatzResearch.WordTrace tailWord_8262623 prefixEnd_8262623 4242697065894531183213395 := by
  unfold tailWord_8262623
  simp only [CollatzResearch.WordTrace]
  refine ⟨301362618744935489506624523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200908412496623659671083015 301362618744935489506624523)
  ·
    refine ⟨452043928117403234259936785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301362618744935489506624523 452043928117403234259936785)
    ·
      refine ⟨339032946088052425694952589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452043928117403234259936785 339032946088052425694952589)
      ·
        refine ⟨127137354783019659635607221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339032946088052425694952589 127137354783019659635607221)
        ·
          refine ⟨11919127010908093090838177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127137354783019659635607221 11919127010908093090838177)
          ·
            refine ⟨8939345258181069818128633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11919127010908093090838177 8939345258181069818128633)
            ·
              refine ⟨6704508943635802363596475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8939345258181069818128633 6704508943635802363596475)
              ·
                refine ⟨10056763415453703545394713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6704508943635802363596475 10056763415453703545394713)
                ·
                  refine ⟨7542572561590277659046035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10056763415453703545394713 7542572561590277659046035)
                  ·
                    refine ⟨11313858842385416488569053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7542572561590277659046035 11313858842385416488569053)
                    ·
                      refine ⟨4242697065894531183213395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11313858842385416488569053 4242697065894531183213395)
                      ·
                        rfl

theorem cell23_8262623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_8262623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262623 prefixEnd_8262623 := by exact prefixLift 8262623
  have htrace : WordTrace (prefixWord ++ tailWord_8262623) baseStart_8262623 baseEnd_8262623 := by
    simpa [prefixWord, tailWord_8262623, baseEnd_8262623] using wordTrace_append hprefix tailTrace_8262623
  have hstable : (prefixWord ++ tailWord_8262623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262623).length < 2 ^ (prefixWord ++ tailWord_8262623).sum := by decide
  have hdescent : baseEnd_8262623 < baseStart_8262623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262625 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_8262625 : Nat := 118140960795 + 8262625 * 2 ^ 59
def prefixEnd_8262625 : Nat := 4983230072969 + 3 ^ 40 * 8262625 * 2
def baseEnd_8262625 : Nat := 4242698092855840175388385

theorem tailTrace_8262625 : CollatzResearch.WordTrace tailWord_8262625 prefixEnd_8262625 4242698092855840175388385 := by
  unfold tailWord_8262625
  simp only [CollatzResearch.WordTrace]
  refine ⟨301362691690928243848197329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200908461127285495898798219 301362691690928243848197329)
  ·
    refine ⟨226022018768196182886147997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301362691690928243848197329 226022018768196182886147997)
    ·
      refine ⟨84758257038073568582305499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226022018768196182886147997 84758257038073568582305499)
      ·
        refine ⟨127137385557110352873458249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84758257038073568582305499 127137385557110352873458249)
        ·
          refine ⟨95353039167832764655093687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127137385557110352873458249 95353039167832764655093687)
          ·
            refine ⟨143029558751749146982640531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95353039167832764655093687 143029558751749146982640531)
            ·
              refine ⟨214544338127623720473960797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143029558751749146982640531 214544338127623720473960797)
              ·
                refine ⟨80454126797858895177735299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214544338127623720473960797 80454126797858895177735299)
                ·
                  refine ⟨120681190196788342766602949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80454126797858895177735299 120681190196788342766602949)
                  ·
                    refine ⟨22627723161897814268738053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120681190196788342766602949 22627723161897814268738053)
                    ·
                      refine ⟨4242698092855840175388385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22627723161897814268738053 4242698092855840175388385)
                      ·
                        rfl

theorem cell23_8262625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_8262625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262625 prefixEnd_8262625 := by exact prefixLift 8262625
  have htrace : WordTrace (prefixWord ++ tailWord_8262625) baseStart_8262625 baseEnd_8262625 := by
    simpa [prefixWord, tailWord_8262625, baseEnd_8262625] using wordTrace_append hprefix tailTrace_8262625
  have hstable : (prefixWord ++ tailWord_8262625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262625).length < 2 ^ (prefixWord ++ tailWord_8262625).sum := by decide
  have hdescent : baseEnd_8262625 < baseStart_8262625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262646 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_8262646 : Nat := 118140960795 + 8262646 * 2 ^ 59
def prefixEnd_8262646 : Nat := 4983230072969 + 3 ^ 40 * 8262646 * 2
def baseEnd_8262646 : Nat := 4242708875949584593225789

theorem tailTrace_8262646 : CollatzResearch.WordTrace tailWord_8262646 prefixEnd_8262646 4242708875949584593225789 := by
  unfold tailWord_8262646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18835216101490760277169487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200908971749234776289807861 18835216101490760277169487)
  ·
    refine ⟨28252824152236140415754231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18835216101490760277169487 28252824152236140415754231)
    ·
      refine ⟨42379236228354210623631347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28252824152236140415754231 42379236228354210623631347)
      ·
        refine ⟨63568854342531315935447021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42379236228354210623631347 63568854342531315935447021)
        ·
          refine ⟨23838320378449243475792633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63568854342531315935447021 23838320378449243475792633)
          ·
            refine ⟨17878740283836932606844475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23838320378449243475792633 17878740283836932606844475)
            ·
              refine ⟨26818110425755398910266713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17878740283836932606844475 26818110425755398910266713)
              ·
                refine ⟨20113582819316549182700035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26818110425755398910266713 20113582819316549182700035)
                ·
                  refine ⟨30170374228974823774050053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20113582819316549182700035 30170374228974823774050053)
                  ·
                    refine ⟨5656945167932779457634385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30170374228974823774050053 5656945167932779457634385)
                    ·
                      refine ⟨4242708875949584593225789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5656945167932779457634385 4242708875949584593225789)
                      ·
                        rfl

theorem cell23_8262646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_8262646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262646 prefixEnd_8262646 := by exact prefixLift 8262646
  have htrace : WordTrace (prefixWord ++ tailWord_8262646) baseStart_8262646 baseEnd_8262646 := by
    simpa [prefixWord, tailWord_8262646, baseEnd_8262646] using wordTrace_append hprefix tailTrace_8262646
  have hstable : (prefixWord ++ tailWord_8262646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262646).length < 2 ^ (prefixWord ++ tailWord_8262646).sum := by decide
  have hdescent : baseEnd_8262646 < baseStart_8262646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262679 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 3]
def baseStart_8262679 : Nat := 118140960795 + 8262679 * 2 ^ 59
def prefixEnd_8262679 : Nat := 4983230072969 + 3 ^ 40 * 8262679 * 2
def baseEnd_8262679 : Nat := 4242725820811182964113137

theorem tailTrace_8262679 : CollatzResearch.WordTrace tailWord_8262679 prefixEnd_8262679 4242725820811182964113137 := by
  unfold tailWord_8262679
  simp only [CollatzResearch.WordTrace]
  refine ⟨301364661232732611070663091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200909774155155074047108727 301364661232732611070663091)
  ·
    refine ⟨452046991849098916605994637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301364661232732611070663091 452046991849098916605994637)
    ·
      refine ⟨169517621943412093727247989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452046991849098916605994637 169517621943412093727247989)
      ·
        refine ⟨15892277057194883786929499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169517621943412093727247989 15892277057194883786929499)
        ·
          refine ⟨23838415585792325680394249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15892277057194883786929499 23838415585792325680394249)
          ·
            refine ⟨17878811689344244260295687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23838415585792325680394249 17878811689344244260295687)
            ·
              refine ⟨26818217534016366390443531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17878811689344244260295687 26818217534016366390443531)
              ·
                refine ⟨40227326301024549585665297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26818217534016366390443531 40227326301024549585665297)
                ·
                  refine ⟨30170494725768412189248973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40227326301024549585665297 30170494725768412189248973)
                  ·
                    refine ⟨11313935522163154570968365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30170494725768412189248973 11313935522163154570968365)
                    ·
                      refine ⟨4242725820811182964113137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11313935522163154570968365 4242725820811182964113137)
                      ·
                        rfl

theorem cell23_8262679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_8262679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262679 prefixEnd_8262679 := by exact prefixLift 8262679
  have htrace : WordTrace (prefixWord ++ tailWord_8262679) baseStart_8262679 baseEnd_8262679 := by
    simpa [prefixWord, tailWord_8262679, baseEnd_8262679] using wordTrace_append hprefix tailTrace_8262679
  have hstable : (prefixWord ++ tailWord_8262679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262679).length < 2 ^ (prefixWord ++ tailWord_8262679).sum := by decide
  have hdescent : baseEnd_8262679 < baseStart_8262679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262752 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 3]
def baseStart_8262752 : Nat := 118140960795 + 8262752 * 2 ^ 59
def prefixEnd_8262752 : Nat := 4983230072969 + 3 ^ 40 * 8262752 * 2
def baseEnd_8262752 : Nat := 4242763304898961178500301

theorem tailTrace_8262752 : CollatzResearch.WordTrace tailWord_8262752 prefixEnd_8262752 4242763304898961178500301 := by
  unfold tailWord_8262752
  simp only [CollatzResearch.WordTrace]
  refine ⟨150683661880734072269035255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200911549174312096358713673 150683661880734072269035255)
  ·
    refine ⟨226025492821101108403552883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150683661880734072269035255 226025492821101108403552883)
    ·
      refine ⟨339038239231651662605329325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226025492821101108403552883 339038239231651662605329325)
      ·
        refine ⟨127139339711869373476998497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339038239231651662605329325 127139339711869373476998497)
        ·
          refine ⟨95354504783902030107748873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127139339711869373476998497 95354504783902030107748873)
          ·
            refine ⟨71515878587926522580811655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95354504783902030107748873 71515878587926522580811655)
            ·
              refine ⟨107273817881889783871217483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71515878587926522580811655 107273817881889783871217483)
              ·
                refine ⟨160910726822834675806826225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107273817881889783871217483 160910726822834675806826225)
                ·
                  refine ⟨120683045117126006855119669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160910726822834675806826225 120683045117126006855119669)
                  ·
                    refine ⟨11314035479730563142667469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120683045117126006855119669 11314035479730563142667469)
                    ·
                      refine ⟨4242763304898961178500301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11314035479730563142667469 4242763304898961178500301)
                      ·
                        rfl

theorem cell23_8262752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_8262752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262752 prefixEnd_8262752 := by exact prefixLift 8262752
  have htrace : WordTrace (prefixWord ++ tailWord_8262752) baseStart_8262752 baseEnd_8262752 := by
    simpa [prefixWord, tailWord_8262752, baseEnd_8262752] using wordTrace_append hprefix tailTrace_8262752
  have hstable : (prefixWord ++ tailWord_8262752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262752).length < 2 ^ (prefixWord ++ tailWord_8262752).sum := by decide
  have hdescent : baseEnd_8262752 < baseStart_8262752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262773 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_8262773 : Nat := 118140960795 + 8262773 * 2 ^ 59
def prefixEnd_8262773 : Nat := 4983230072969 + 3 ^ 40 * 8262773 * 2
def baseEnd_8262773 : Nat := 4242774087992705596337705

theorem tailTrace_8262773 : CollatzResearch.WordTrace tailWord_8262773 prefixEnd_8262773 4242774087992705596337705 := by
  unfold tailWord_8262773
  simp only [CollatzResearch.WordTrace]
  refine ⟨301368089694392065124584973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200912059796261376749723315 301368089694392065124584973)
  ·
    refine ⟨113013033635397024421719365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301368089694392065124584973 113013033635397024421719365)
    ·
      refine ⟨21189943806636942079072381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113013033635397024421719365 21189943806636942079072381)
      ·
        refine ⟨7946228927488853279652143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21189943806636942079072381 7946228927488853279652143)
        ·
          refine ⟨11919343391233279919478215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7946228927488853279652143 11919343391233279919478215)
          ·
            refine ⟨17879015086849919879217323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11919343391233279919478215 17879015086849919879217323)
            ·
              refine ⟨26818522630274879818825985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17879015086849919879217323 26818522630274879818825985)
              ·
                refine ⟨20113891972706159864119489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26818522630274879818825985 20113891972706159864119489)
                ·
                  refine ⟨15085418979529619898089617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20113891972706159864119489 15085418979529619898089617)
                  ·
                    refine ⟨11314064234647214923567213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15085418979529619898089617 11314064234647214923567213)
                    ·
                      refine ⟨4242774087992705596337705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11314064234647214923567213 4242774087992705596337705)
                      ·
                        rfl

theorem cell23_8262773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_8262773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262773 prefixEnd_8262773 := by exact prefixLift 8262773
  have htrace : WordTrace (prefixWord ++ tailWord_8262773) baseStart_8262773 baseEnd_8262773 := by
    simpa [prefixWord, tailWord_8262773, baseEnd_8262773] using wordTrace_append hprefix tailTrace_8262773
  have hstable : (prefixWord ++ tailWord_8262773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262773).length < 2 ^ (prefixWord ++ tailWord_8262773).sum := by decide
  have hdescent : baseEnd_8262773 < baseStart_8262773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
