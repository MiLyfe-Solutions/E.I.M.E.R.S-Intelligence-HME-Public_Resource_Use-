import V185TrunkScan23Chunk1248

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7398308 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 3, 2, 2]
def baseStart_7398308 : Nat := 118140960795 + 7398308 * 2 ^ 59
def prefixEnd_7398308 : Nat := 4983230072969 + 3 ^ 40 * 7398308 * 2
def baseEnd_7398308 : Nat := 3798888034003745319625807

theorem tailTrace_7398308 : CollatzResearch.WordTrace tailWord_7398308 prefixEnd_7398308 3798888034003745319625807 := by
  unfold tailWord_7398308
  simp only [CollatzResearch.WordTrace]
  refine ⟨134919230440600560628357789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179892307254134080837810385 134919230440600560628357789)
  ·
    refine ⟨50594711415225210235634171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134919230440600560628357789 50594711415225210235634171)
    ·
      refine ⟨75892067122837815353451257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50594711415225210235634171 75892067122837815353451257)
      ·
        refine ⟨56919050342128361515088443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75892067122837815353451257 56919050342128361515088443)
        ·
          refine ⟨85378575513192542272632665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56919050342128361515088443 85378575513192542272632665)
          ·
            refine ⟨64033931634894406704474499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85378575513192542272632665 64033931634894406704474499)
            ·
              refine ⟨96050897452341610056711749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64033931634894406704474499 96050897452341610056711749)
              ·
                refine ⟨18009543272314051885633453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96050897452341610056711749 18009543272314051885633453)
                ·
                  refine ⟨6753578727117769457112545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18009543272314051885633453 6753578727117769457112545)
                  ·
                    refine ⟨5065184045338327092834409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6753578727117769457112545 5065184045338327092834409)
                    ·
                      refine ⟨3798888034003745319625807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065184045338327092834409 3798888034003745319625807)
                      ·
                        rfl

theorem cell23_7398308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_7398308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398308 prefixEnd_7398308 := by exact prefixLift 7398308
  have htrace : WordTrace (prefixWord ++ tailWord_7398308) baseStart_7398308 baseEnd_7398308 := by
    simpa [prefixWord, tailWord_7398308, baseEnd_7398308] using wordTrace_append hprefix tailTrace_7398308
  have hstable : (prefixWord ++ tailWord_7398308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398308).length < 2 ^ (prefixWord ++ tailWord_7398308).sum := by decide
  have hdescent : baseEnd_7398308 < baseStart_7398308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398394 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_7398394 : Nat := 118140960795 + 7398394 * 2 ^ 59
def prefixEnd_7398394 : Nat := 4983230072969 + 3 ^ 40 * 7398394 * 2
def baseEnd_7398394 : Nat := 3798932193340031983150411

theorem tailTrace_7398394 : CollatzResearch.WordTrace tailWord_7398394 prefixEnd_7398394 3798932193340031983150411 := by
  unfold tailWord_7398394
  simp only [CollatzResearch.WordTrace]
  refine ⟨67460399389722389486086559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179894398372593038629564157 67460399389722389486086559)
  ·
    refine ⟨101190599084583584229129839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67460399389722389486086559 101190599084583584229129839)
    ·
      refine ⟨151785898626875376343694759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101190599084583584229129839 151785898626875376343694759)
      ·
        refine ⟨227678847940313064515542139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151785898626875376343694759 227678847940313064515542139)
        ·
          refine ⟨341518271910469596773313209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227678847940313064515542139 341518271910469596773313209)
          ·
            refine ⟨256138703932852197579984907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341518271910469596773313209 256138703932852197579984907)
            ·
              refine ⟨384208055899278296369977361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256138703932852197579984907 384208055899278296369977361)
              ·
                refine ⟨288156041924458722277483021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384208055899278296369977361 288156041924458722277483021)
                ·
                  refine ⟨108058515721672020854056133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288156041924458722277483021 108058515721672020854056133)
                  ·
                    refine ⟨20260971697813503910135525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108058515721672020854056133 20260971697813503910135525)
                    ·
                      refine ⟨3798932193340031983150411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20260971697813503910135525 3798932193340031983150411)
                      ·
                        rfl

theorem cell23_7398394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_7398394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398394 prefixEnd_7398394 := by exact prefixLift 7398394
  have htrace : WordTrace (prefixWord ++ tailWord_7398394) baseStart_7398394 baseEnd_7398394 := by
    simpa [prefixWord, tailWord_7398394, baseEnd_7398394] using wordTrace_append hprefix tailTrace_7398394
  have hstable : (prefixWord ++ tailWord_7398394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398394).length < 2 ^ (prefixWord ++ tailWord_7398394).sum := by decide
  have hdescent : baseEnd_7398394 < baseStart_7398394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398401 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_7398401 : Nat := 118140960795 + 7398401 * 2 ^ 59
def prefixEnd_7398401 : Nat := 4983230072969 + 3 ^ 40 * 7398401 * 2
def baseEnd_7398401 : Nat := 3798935787704613455762879

theorem tailTrace_7398401 : CollatzResearch.WordTrace tailWord_7398401 prefixEnd_7398401 3798935787704613455762879 := by
  unfold tailWord_7398401
  simp only [CollatzResearch.WordTrace]
  refine ⟨269841852869864198139851057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179894568579909465426567371 269841852869864198139851057)
  ·
    refine ⟨202381389652398148604888293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269841852869864198139851057 202381389652398148604888293)
    ·
      refine ⟨37946510559824652863416555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202381389652398148604888293 37946510559824652863416555)
      ·
        refine ⟨56919765839736979295124833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37946510559824652863416555 56919765839736979295124833)
        ·
          refine ⟨42689824379802734471343625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56919765839736979295124833 42689824379802734471343625)
          ·
            refine ⟨32017368284852050853507719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42689824379802734471343625 32017368284852050853507719)
            ·
              refine ⟨48026052427278076280261579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32017368284852050853507719 48026052427278076280261579)
              ·
                refine ⟨72039078640917114420392369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48026052427278076280261579 72039078640917114420392369)
                ·
                  refine ⟨54029308980687835815294277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72039078640917114420392369 54029308980687835815294277)
                  ·
                    refine ⟨10130495433878969215367677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54029308980687835815294277 10130495433878969215367677)
                    ·
                      refine ⟨3798935787704613455762879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10130495433878969215367677 3798935787704613455762879)
                      ·
                        rfl

theorem cell23_7398401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_7398401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398401 prefixEnd_7398401 := by exact prefixLift 7398401
  have htrace : WordTrace (prefixWord ++ tailWord_7398401) baseStart_7398401 baseEnd_7398401 := by
    simpa [prefixWord, tailWord_7398401, baseEnd_7398401] using wordTrace_append hprefix tailTrace_7398401
  have hstable : (prefixWord ++ tailWord_7398401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398401).length < 2 ^ (prefixWord ++ tailWord_7398401).sum := by decide
  have hdescent : baseEnd_7398401 < baseStart_7398401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398411 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 4]
def baseStart_7398411 : Nat := 118140960795 + 7398411 * 2 ^ 59
def prefixEnd_7398411 : Nat := 4983230072969 + 3 ^ 40 * 7398411 * 2
def baseEnd_7398411 : Nat := 3798940922511158416637833

theorem tailTrace_7398411 : CollatzResearch.WordTrace tailWord_7398411 prefixEnd_7398411 3798940922511158416637833 := by
  unfold tailWord_7398411
  simp only [CollatzResearch.WordTrace]
  refine ⟨269842217599827969847715087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179894811733218646565143391 269842217599827969847715087)
  ·
    refine ⟨404763326399741954771572631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269842217599827969847715087 404763326399741954771572631)
    ·
      refine ⟨607144989599612932157358947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404763326399741954771572631 607144989599612932157358947)
      ·
        refine ⟨910717484399419398236038421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607144989599612932157358947 910717484399419398236038421)
        ·
          refine ⟨42689882081222784292314301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 910717484399419398236038421 42689882081222784292314301)
          ·
            refine ⟨16008705780458544109617863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42689882081222784292314301 16008705780458544109617863)
            ·
              refine ⟨24013058670687816164426795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16008705780458544109617863 24013058670687816164426795)
              ·
                refine ⟨36019588006031724246640193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24013058670687816164426795 36019588006031724246640193)
                ·
                  refine ⟨27014691004523793184980145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36019588006031724246640193 27014691004523793184980145)
                  ·
                    refine ⟨20261018253392844888735109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27014691004523793184980145 20261018253392844888735109)
                    ·
                      refine ⟨3798940922511158416637833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20261018253392844888735109 3798940922511158416637833)
                      ·
                        rfl

theorem cell23_7398411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 4].length) (baseStart_7398411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398411 prefixEnd_7398411 := by exact prefixLift 7398411
  have htrace : WordTrace (prefixWord ++ tailWord_7398411) baseStart_7398411 baseEnd_7398411 := by
    simpa [prefixWord, tailWord_7398411, baseEnd_7398411] using wordTrace_append hprefix tailTrace_7398411
  have hstable : (prefixWord ++ tailWord_7398411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398411).length < 2 ^ (prefixWord ++ tailWord_7398411).sum := by decide
  have hdescent : baseEnd_7398411 < baseStart_7398411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398421 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 7]
def baseStart_7398421 : Nat := 118140960795 + 7398421 * 2 ^ 59
def prefixEnd_7398421 : Nat := 4983230072969 + 3 ^ 40 * 7398421 * 2
def baseEnd_7398421 : Nat := 422105117479744819723643

theorem tailTrace_7398421 : CollatzResearch.WordTrace tailWord_7398421 prefixEnd_7398421 422105117479744819723643 := by
  unfold tailWord_7398421
  simp only [CollatzResearch.WordTrace]
  refine ⟨269842582329791741555579117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179895054886527827703719411 269842582329791741555579117)
  ·
    refine ⟨101190968373671903083342169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269842582329791741555579117 101190968373671903083342169)
    ·
      refine ⟨75893226280253927312506627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101190968373671903083342169 75893226280253927312506627)
      ·
        refine ⟨113839839420380890968759941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75893226280253927312506627 113839839420380890968759941)
        ·
          refine ⟨21344969891321417056642489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113839839420380890968759941 21344969891321417056642489)
          ·
            refine ⟨16008727418491062792481867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21344969891321417056642489 16008727418491062792481867)
            ·
              refine ⟨24013091127736594188722801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16008727418491062792481867 24013091127736594188722801)
              ·
                refine ⟨18009818345802445641542101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24013091127736594188722801 18009818345802445641542101)
                ·
                  refine ⟨422105117479744819723643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18009818345802445641542101 422105117479744819723643)
                  ·
                    rfl

theorem cell23_7398421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_7398421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398421 prefixEnd_7398421 := by exact prefixLift 7398421
  have htrace : WordTrace (prefixWord ++ tailWord_7398421) baseStart_7398421 baseEnd_7398421 := by
    simpa [prefixWord, tailWord_7398421, baseEnd_7398421] using wordTrace_append hprefix tailTrace_7398421
  have hstable : (prefixWord ++ tailWord_7398421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398421).length < 2 ^ (prefixWord ++ tailWord_7398421).sum := by decide
  have hdescent : baseEnd_7398421 < baseStart_7398421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398471 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_7398471 : Nat := 118140960795 + 7398471 * 2 ^ 59
def prefixEnd_7398471 : Nat := 4983230072969 + 3 ^ 40 * 7398471 * 2
def baseEnd_7398471 : Nat := 3798971731350428181887557

theorem tailTrace_7398471 : CollatzResearch.WordTrace tailWord_7398471 prefixEnd_7398471 3798971731350428181887557 := by
  unfold tailWord_7398471
  simp only [CollatzResearch.WordTrace]
  refine ⟨269844405979610600094899267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179896270653073733396599511 269844405979610600094899267)
  ·
    refine ⟨404766608969415900142348901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269844405979610600094899267 404766608969415900142348901)
    ·
      refine ⟨75893739181765481276690419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404766608969415900142348901 75893739181765481276690419)
      ·
        refine ⟨113840608772648221915035629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75893739181765481276690419 113840608772648221915035629)
        ·
          refine ⟨42690228289743083218138361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113840608772648221915035629 42690228289743083218138361)
          ·
            refine ⟨32017671217307312413603771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42690228289743083218138361 32017671217307312413603771)
            ·
              refine ⟨48026506825960968620405657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32017671217307312413603771 48026506825960968620405657)
              ·
                refine ⟨36019880119470726465304243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48026506825960968620405657 36019880119470726465304243)
                ·
                  refine ⟨54029820179206089697956365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36019880119470726465304243 54029820179206089697956365)
                  ·
                    refine ⟨20261182567202283636733637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54029820179206089697956365 20261182567202283636733637)
                    ·
                      refine ⟨3798971731350428181887557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20261182567202283636733637 3798971731350428181887557)
                      ·
                        rfl

theorem cell23_7398471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_7398471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398471 prefixEnd_7398471 := by exact prefixLift 7398471
  have htrace : WordTrace (prefixWord ++ tailWord_7398471) baseStart_7398471 baseEnd_7398471 := by
    simpa [prefixWord, tailWord_7398471, baseEnd_7398471] using wordTrace_append hprefix tailTrace_7398471
  have hstable : (prefixWord ++ tailWord_7398471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398471).length < 2 ^ (prefixWord ++ tailWord_7398471).sum := by decide
  have hdescent : baseEnd_7398471 < baseStart_7398471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398508 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 3]
def baseStart_7398508 : Nat := 118140960795 + 7398508 * 2 ^ 59
def prefixEnd_7398508 : Nat := 4983230072969 + 3 ^ 40 * 7398508 * 2
def baseEnd_7398508 : Nat := 3798990730134644537124887

theorem tailTrace_7398508 : CollatzResearch.WordTrace tailWord_7398508 prefixEnd_7398508 3798990730134644537124887 := by
  unfold tailWord_7398508
  simp only [CollatzResearch.WordTrace]
  refine ⟨134922877740238277706998089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179897170320317703609330785 134922877740238277706998089)
  ·
    refine ⟨101192158305178708280248567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134922877740238277706998089 101192158305178708280248567)
    ·
      refine ⟨151788237457768062420372851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101192158305178708280248567 151788237457768062420372851)
      ·
        refine ⟨227682356186652093630559277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151788237457768062420372851 227682356186652093630559277)
        ·
          refine ⟨85380883569994535111459729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227682356186652093630559277 85380883569994535111459729)
          ·
            refine ⟨64035662677495901333594797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85380883569994535111459729 64035662677495901333594797)
            ·
              refine ⟨24013373504060963000098049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64035662677495901333594797 24013373504060963000098049)
              ·
                refine ⟨18010030128045722250073537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24013373504060963000098049 18010030128045722250073537)
                ·
                  refine ⟨13507522596034291687555153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18010030128045722250073537 13507522596034291687555153)
                  ·
                    refine ⟨10130641947025718765666365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13507522596034291687555153 10130641947025718765666365)
                    ·
                      refine ⟨3798990730134644537124887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10130641947025718765666365 3798990730134644537124887)
                      ·
                        rfl

theorem cell23_7398508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_7398508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398508 prefixEnd_7398508 := by exact prefixLift 7398508
  have htrace : WordTrace (prefixWord ++ tailWord_7398508) baseStart_7398508 baseEnd_7398508 := by
    simpa [prefixWord, tailWord_7398508, baseEnd_7398508] using wordTrace_append hprefix tailTrace_7398508
  have hstable : (prefixWord ++ tailWord_7398508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398508).length < 2 ^ (prefixWord ++ tailWord_7398508).sum := by decide
  have hdescent : baseEnd_7398508 < baseStart_7398508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398511 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 6]
def baseStart_7398511 : Nat := 118140960795 + 7398511 * 2 ^ 59
def prefixEnd_7398511 : Nat := 4983230072969 + 3 ^ 40 * 7398511 * 2
def baseEnd_7398511 : Nat := 422110252286289780598597

theorem tailTrace_7398511 : CollatzResearch.WordTrace tailWord_7398511 prefixEnd_7398511 422110252286289780598597 := by
  unfold tailWord_7398511
  simp only [CollatzResearch.WordTrace]
  refine ⟨269845864899465686926355387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179897243266310457950903591 269845864899465686926355387)
  ·
    refine ⟨404768797349198530389533081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269845864899465686926355387 404768797349198530389533081)
    ·
      refine ⟨303576598011898897792149811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404768797349198530389533081 303576598011898897792149811)
      ·
        refine ⟨455364897017848346688224717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303576598011898897792149811 455364897017848346688224717)
        ·
          refine ⟨170761836381693130008084269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455364897017848346688224717 170761836381693130008084269)
          ·
            refine ⟨64035688643134923753031601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170761836381693130008084269 64035688643134923753031601)
            ·
              refine ⟨48026766482351192814773701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64035688643134923753031601 48026766482351192814773701)
              ·
                refine ⟨9005018715440848652770069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48026766482351192814773701 9005018715440848652770069)
                ·
                  refine ⟨422110252286289780598597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9005018715440848652770069 422110252286289780598597)
                  ·
                    rfl

theorem cell23_7398511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 6].length) (baseStart_7398511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398511 prefixEnd_7398511 := by exact prefixLift 7398511
  have htrace : WordTrace (prefixWord ++ tailWord_7398511) baseStart_7398511 baseEnd_7398511 := by
    simpa [prefixWord, tailWord_7398511, baseEnd_7398511] using wordTrace_append hprefix tailTrace_7398511
  have hstable : (prefixWord ++ tailWord_7398511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398511).length < 2 ^ (prefixWord ++ tailWord_7398511).sum := by decide
  have hdescent : baseEnd_7398511 < baseStart_7398511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398528 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 6]
def baseStart_7398528 : Nat := 118140960795 + 7398528 * 2 ^ 59
def prefixEnd_7398528 : Nat := 4983230072969 + 3 ^ 40 * 7398528 * 2
def baseEnd_7398528 : Nat := 422111222194192717652755

theorem tailTrace_7398528 : CollatzResearch.WordTrace tailWord_7398528 prefixEnd_7398528 422111222194192717652755 := by
  unfold tailWord_7398528
  simp only [CollatzResearch.WordTrace]
  refine ⟨134923242470202049414862119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179897656626936065886482825 134923242470202049414862119)
  ·
    refine ⟨202384863705303074122293179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134923242470202049414862119 202384863705303074122293179)
    ·
      refine ⟨303577295557954611183439769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202384863705303074122293179 303577295557954611183439769)
      ·
        refine ⟨227682971668465958387579827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303577295557954611183439769 227682971668465958387579827)
        ·
          refine ⟨341524457502698937581369741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227682971668465958387579827 341524457502698937581369741)
          ·
            refine ⟨128071671563512101593013653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341524457502698937581369741 128071671563512101593013653)
            ·
              refine ⟨6003359604539629762172515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128071671563512101593013653 6003359604539629762172515)
              ·
                refine ⟨9005039406809444643258773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6003359604539629762172515 9005039406809444643258773)
                ·
                  refine ⟨422111222194192717652755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9005039406809444643258773 422111222194192717652755)
                  ·
                    rfl

theorem cell23_7398528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 6].length) (baseStart_7398528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398528 prefixEnd_7398528 := by exact prefixLift 7398528
  have htrace : WordTrace (prefixWord ++ tailWord_7398528) baseStart_7398528 baseEnd_7398528 := by
    simpa [prefixWord, tailWord_7398528, baseEnd_7398528] using wordTrace_append hprefix tailTrace_7398528
  have hstable : (prefixWord ++ tailWord_7398528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398528).length < 2 ^ (prefixWord ++ tailWord_7398528).sum := by decide
  have hdescent : baseEnd_7398528 < baseStart_7398528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398565 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 2, 3, 2]
def baseStart_7398565 : Nat := 118140960795 + 7398565 * 2 ^ 59
def prefixEnd_7398565 : Nat := 4983230072969 + 3 ^ 40 * 7398565 * 2
def baseEnd_7398565 : Nat := 3799019998531950814112125

theorem tailTrace_7398565 : CollatzResearch.WordTrace tailWord_7398565 prefixEnd_7398565 3799019998531950814112125 := by
  unfold tailWord_7398565
  simp only [CollatzResearch.WordTrace]
  refine ⟨269847834441270054148821149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179898556294180036099214099 269847834441270054148821149)
  ·
    refine ⟨101192937915476270305807931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269847834441270054148821149 101192937915476270305807931)
    ·
      refine ⟨151789406873214405458711897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101192937915476270305807931 151789406873214405458711897)
      ·
        refine ⟨113842055154910804094033923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151789406873214405458711897 113842055154910804094033923)
        ·
          refine ⟨170763082732366206141050885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113842055154910804094033923 170763082732366206141050885)
          ·
            refine ⟨32018078012318663651447041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170763082732366206141050885 32018078012318663651447041)
            ·
              refine ⟨24013558509238997738585281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32018078012318663651447041 24013558509238997738585281)
              ·
                refine ⟨18010168881929248303938961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24013558509238997738585281 18010168881929248303938961)
                ·
                  refine ⟨13507626661446936227954221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18010168881929248303938961 13507626661446936227954221)
                  ·
                    refine ⟨5065359998042601085482833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13507626661446936227954221 5065359998042601085482833)
                    ·
                      refine ⟨3799019998531950814112125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065359998042601085482833 3799019998531950814112125)
                      ·
                        rfl

theorem cell23_7398565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_7398565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398565 prefixEnd_7398565 := by exact prefixLift 7398565
  have htrace : WordTrace (prefixWord ++ tailWord_7398565) baseStart_7398565 baseEnd_7398565 := by
    simpa [prefixWord, tailWord_7398565, baseEnd_7398565] using wordTrace_append hprefix tailTrace_7398565
  have hstable : (prefixWord ++ tailWord_7398565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398565).length < 2 ^ (prefixWord ++ tailWord_7398565).sum := by decide
  have hdescent : baseEnd_7398565 < baseStart_7398565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398578 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_7398578 : Nat := 118140960795 + 7398578 * 2 ^ 59
def prefixEnd_7398578 : Nat := 4983230072969 + 3 ^ 40 * 7398578 * 2
def baseEnd_7398578 : Nat := 3799026673780459263249565

theorem tailTrace_7398578 : CollatzResearch.WordTrace tailWord_7398578 prefixEnd_7398578 3799026673780459263249565 := by
  unfold tailWord_7398578
  simp only [CollatzResearch.WordTrace]
  refine ⟨67462077147555739342261097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179898872393481971579362925 67462077147555739342261097)
  ·
    refine ⟨50596557860666804506695823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67462077147555739342261097 50596557860666804506695823)
    ·
      refine ⟨75894836791000206760043735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50596557860666804506695823 75894836791000206760043735)
      ·
        refine ⟨113842255186500310140065603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75894836791000206760043735 113842255186500310140065603)
        ·
          refine ⟨170763382779750465210098405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113842255186500310140065603 170763382779750465210098405)
          ·
            refine ⟨32018134271203212226893451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170763382779750465210098405 32018134271203212226893451)
            ·
              refine ⟨48027201406804818340340177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32018134271203212226893451 48027201406804818340340177)
              ·
                refine ⟨36020401055103613755255133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48027201406804818340340177 36020401055103613755255133)
                ·
                  refine ⟨13507650395663855158220675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36020401055103613755255133 13507650395663855158220675)
                  ·
                    refine ⟨20261475593495782737331013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13507650395663855158220675 20261475593495782737331013)
                    ·
                      refine ⟨3799026673780459263249565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20261475593495782737331013 3799026673780459263249565)
                      ·
                        rfl

theorem cell23_7398578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_7398578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398578 prefixEnd_7398578 := by exact prefixLift 7398578
  have htrace : WordTrace (prefixWord ++ tailWord_7398578) baseStart_7398578 baseEnd_7398578 := by
    simpa [prefixWord, tailWord_7398578, baseEnd_7398578] using wordTrace_append hprefix tailTrace_7398578
  have hstable : (prefixWord ++ tailWord_7398578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398578).length < 2 ^ (prefixWord ++ tailWord_7398578).sum := by decide
  have hdescent : baseEnd_7398578 < baseStart_7398578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398588 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_7398588 : Nat := 118140960795 + 7398588 * 2 ^ 59
def prefixEnd_7398588 : Nat := 4983230072969 + 3 ^ 40 * 7398588 * 2
def baseEnd_7398588 : Nat := 1266343936195668074708173

theorem tailTrace_7398588 : CollatzResearch.WordTrace tailWord_7398588 prefixEnd_7398588 1266343936195668074708173 := by
  unfold tailWord_7398588
  simp only [CollatzResearch.WordTrace]
  refine ⟨134924336660093364538454209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179899115546791152717938945 134924336660093364538454209)
  ·
    refine ⟨101193252495070023403840657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134924336660093364538454209 101193252495070023403840657)
    ·
      refine ⟨75894939371302517552880493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101193252495070023403840657 75894939371302517552880493)
      ·
        refine ⟨28460602264238444082330185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75894939371302517552880493 28460602264238444082330185)
        ·
          refine ⟨21345451698178833061747639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28460602264238444082330185 21345451698178833061747639)
          ·
            refine ⟨32018177547268249592621459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21345451698178833061747639 32018177547268249592621459)
            ·
              refine ⟨48027266320902374388932189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32018177547268249592621459 48027266320902374388932189)
              ·
                refine ⟨18010224870338390395849571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48027266320902374388932189 18010224870338390395849571)
                ·
                  refine ⟨27015337305507585593774357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18010224870338390395849571 27015337305507585593774357)
                  ·
                    refine ⟨1266343936195668074708173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27015337305507585593774357 1266343936195668074708173)
                    ·
                      rfl

theorem cell23_7398588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_7398588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398588 prefixEnd_7398588 := by exact prefixLift 7398588
  have htrace : WordTrace (prefixWord ++ tailWord_7398588) baseStart_7398588 baseEnd_7398588 := by
    simpa [prefixWord, tailWord_7398588, baseEnd_7398588] using wordTrace_append hprefix tailTrace_7398588
  have hstable : (prefixWord ++ tailWord_7398588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398588).length < 2 ^ (prefixWord ++ tailWord_7398588).sum := by decide
  have hdescent : baseEnd_7398588 < baseStart_7398588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398591 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 6]
def baseStart_7398591 : Nat := 118140960795 + 7398591 * 2 ^ 59
def prefixEnd_7398591 : Nat := 4983230072969 + 3 ^ 40 * 7398591 * 2
def baseEnd_7398591 : Nat := 3799033349028967712387005

theorem tailTrace_7398591 : CollatzResearch.WordTrace tailWord_7398591 prefixEnd_7398591 3799033349028967712387005 := by
  unfold tailWord_7398591
  simp only [CollatzResearch.WordTrace]
  refine ⟨269848782739175860589267627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179899188492783907059511751 269848782739175860589267627)
  ·
    refine ⟨404773174108763790883901441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269848782739175860589267627 404773174108763790883901441)
    ·
      refine ⟨303579880581572843162926081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404773174108763790883901441 303579880581572843162926081)
      ·
        refine ⟨227684910436179632372194561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303579880581572843162926081 227684910436179632372194561)
        ·
          refine ⟨170763682827134724279145921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227684910436179632372194561 170763682827134724279145921)
          ·
            refine ⟨128072762120351043209359441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170763682827134724279145921 128072762120351043209359441)
            ·
              refine ⟨96054571590263282407019581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128072762120351043209359441 96054571590263282407019581)
              ·
                refine ⟨36020464346348730902632343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96054571590263282407019581 36020464346348730902632343)
                ·
                  refine ⟨54030696519523096353948515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36020464346348730902632343 54030696519523096353948515)
                  ·
                    refine ⟨81046044779284644530922773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54030696519523096353948515 81046044779284644530922773)
                    ·
                      refine ⟨3799033349028967712387005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81046044779284644530922773 3799033349028967712387005)
                      ·
                        rfl

theorem cell23_7398591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_7398591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398591 prefixEnd_7398591 := by exact prefixLift 7398591
  have htrace : WordTrace (prefixWord ++ tailWord_7398591) baseStart_7398591 baseEnd_7398591 := by
    simpa [prefixWord, tailWord_7398591, baseEnd_7398591] using wordTrace_append hprefix tailTrace_7398591
  have hstable : (prefixWord ++ tailWord_7398591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398591).length < 2 ^ (prefixWord ++ tailWord_7398591).sum := by decide
  have hdescent : baseEnd_7398591 < baseStart_7398591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398628 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_7398628 : Nat := 118140960795 + 7398628 * 2 ^ 59
def prefixEnd_7398628 : Nat := 4983230072969 + 3 ^ 40 * 7398628 * 2
def baseEnd_7398628 : Nat := 3799052347813184067624335

theorem tailTrace_7398628 : CollatzResearch.WordTrace tailWord_7398628 prefixEnd_7398628 3799052347813184067624335 := by
  unfold tailWord_7398628
  simp only [CollatzResearch.WordTrace]
  refine ⟨134925066120020907954182269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179900088160027877272243025 134925066120020907954182269)
  ·
    refine ⟨50596899795007840482818351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134925066120020907954182269 50596899795007840482818351)
    ·
      refine ⟨75895349692511760724227527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50596899795007840482818351 75895349692511760724227527)
      ·
        refine ⟨113843024538767641086341291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75895349692511760724227527 113843024538767641086341291)
        ·
          refine ⟨170764536808151461629511937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113843024538767641086341291 170764536808151461629511937)
          ·
            refine ⟨128073402606113596222133953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170764536808151461629511937 128073402606113596222133953)
            ·
              refine ⟨96055051954585197166600465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128073402606113596222133953 96055051954585197166600465)
              ·
                refine ⟨72041288965938897874950349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96055051954585197166600465 72041288965938897874950349)
                ·
                  refine ⟨27015483362227086703106381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72041288965938897874950349 27015483362227086703106381)
                  ·
                    refine ⟨10130806260835157513664893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27015483362227086703106381 10130806260835157513664893)
                    ·
                      refine ⟨3799052347813184067624335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10130806260835157513664893 3799052347813184067624335)
                      ·
                        rfl

theorem cell23_7398628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_7398628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398628 prefixEnd_7398628 := by exact prefixLift 7398628
  have htrace : WordTrace (prefixWord ++ tailWord_7398628) baseStart_7398628 baseEnd_7398628 := by
    simpa [prefixWord, tailWord_7398628, baseEnd_7398628] using wordTrace_append hprefix tailTrace_7398628
  have hstable : (prefixWord ++ tailWord_7398628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398628).length < 2 ^ (prefixWord ++ tailWord_7398628).sum := by decide
  have hdescent : baseEnd_7398628 < baseStart_7398628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398629 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 3, 2, 2]
def baseStart_7398629 : Nat := 118140960795 + 7398629 * 2 ^ 59
def prefixEnd_7398629 : Nat := 4983230072969 + 3 ^ 40 * 7398629 * 2
def baseEnd_7398629 : Nat := 3799052861293838563711831

theorem tailTrace_7398629 : CollatzResearch.WordTrace tailWord_7398629 prefixEnd_7398629 3799052861293838563711831 := by
  unfold tailWord_7398629
  simp only [CollatzResearch.WordTrace]
  refine ⟨269850168713038193079150941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179900112475358795386100627 269850168713038193079150941)
  ·
    refine ⟨101193813267389322404681603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269850168713038193079150941 101193813267389322404681603)
    ·
      refine ⟨151790719901083983607022405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101193813267389322404681603 151790719901083983607022405)
      ·
        refine ⟨28460759981453246926316701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151790719901083983607022405 28460759981453246926316701)
        ·
          refine ⟨10672784993044967597368763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28460759981453246926316701 10672784993044967597368763)
          ·
            refine ⟨16009177489567451396053145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10672784993044967597368763 16009177489567451396053145)
            ·
              refine ⟨12006883117175588547039859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16009177489567451396053145 12006883117175588547039859)
              ·
                refine ⟨18010324675763382820559789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12006883117175588547039859 18010324675763382820559789)
                ·
                  refine ⟨6753871753411268557709921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18010324675763382820559789 6753871753411268557709921)
                  ·
                    refine ⟨5065403815058451418282441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6753871753411268557709921 5065403815058451418282441)
                    ·
                      refine ⟨3799052861293838563711831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065403815058451418282441 3799052861293838563711831)
                      ·
                        rfl

theorem cell23_7398629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_7398629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398629 prefixEnd_7398629 := by exact prefixLift 7398629
  have htrace : WordTrace (prefixWord ++ tailWord_7398629) baseStart_7398629 baseEnd_7398629 := by
    simpa [prefixWord, tailWord_7398629, baseEnd_7398629] using wordTrace_append hprefix tailTrace_7398629
  have hstable : (prefixWord ++ tailWord_7398629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398629).length < 2 ^ (prefixWord ++ tailWord_7398629).sum := by decide
  have hdescent : baseEnd_7398629 < baseStart_7398629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398642 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_7398642 : Nat := 118140960795 + 7398642 * 2 ^ 59
def prefixEnd_7398642 : Nat := 4983230072969 + 3 ^ 40 * 7398642 * 2
def baseEnd_7398642 : Nat := 3799059536542347012849271

theorem tailTrace_7398642 : CollatzResearch.WordTrace tailWord_7398642 prefixEnd_7398642 3799059536542347012849271 := by
  unfold tailWord_7398642
  simp only [CollatzResearch.WordTrace]
  refine ⟨67462660715497774074843545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179900428574660730866249453 67462660715497774074843545)
  ·
    refine ⟨50596995536623330556132659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67462660715497774074843545 50596995536623330556132659)
    ·
      refine ⟨75895493304934995834198989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50596995536623330556132659 75895493304934995834198989)
      ·
        refine ⟨28460809989350623437824621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75895493304934995834198989 28460809989350623437824621)
        ·
          refine ⟨10672803746006483789184233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28460809989350623437824621 10672803746006483789184233)
          ·
            refine ⟨8004602809504862841888175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10672803746006483789184233 8004602809504862841888175)
            ·
              refine ⟨12006904214257294262832263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8004602809504862841888175 12006904214257294262832263)
              ·
                refine ⟨18010356321385941394248395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12006904214257294262832263 18010356321385941394248395)
                ·
                  refine ⟨27015534482078912091372593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18010356321385941394248395 27015534482078912091372593)
                  ·
                    refine ⟨20261650861559184068529445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27015534482078912091372593 20261650861559184068529445)
                    ·
                      refine ⟨3799059536542347012849271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20261650861559184068529445 3799059536542347012849271)
                      ·
                        rfl

theorem cell23_7398642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_7398642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398642 prefixEnd_7398642 := by exact prefixLift 7398642
  have htrace : WordTrace (prefixWord ++ tailWord_7398642) baseStart_7398642 baseEnd_7398642 := by
    simpa [prefixWord, tailWord_7398642, baseEnd_7398642] using wordTrace_append hprefix tailTrace_7398642
  have hstable : (prefixWord ++ tailWord_7398642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398642).length < 2 ^ (prefixWord ++ tailWord_7398642).sum := by decide
  have hdescent : baseEnd_7398642 < baseStart_7398642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398652 : List Nat := [2, 2, 2, 1, 6, 1, 2, 7]
def baseStart_7398652 : Nat := 118140960795 + 7398652 * 2 ^ 59
def prefixEnd_7398652 : Nat := 4983230072969 + 3 ^ 40 * 7398652 * 2
def baseEnd_7398652 : Nat := 140706098938847850878675

theorem tailTrace_7398652 : CollatzResearch.WordTrace tailWord_7398652 prefixEnd_7398652 140706098938847850878675 := by
  unfold tailWord_7398652
  simp only [CollatzResearch.WordTrace]
  refine ⟨134925503795977434003619105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179900671727969912004825473 134925503795977434003619105)
  ·
    refine ⟨101194127846983075502714329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134925503795977434003619105 101194127846983075502714329)
    ·
      refine ⟨75895595885237306627035747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101194127846983075502714329 75895595885237306627035747)
      ·
        refine ⟨113843393827855959940553621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75895595885237306627035747 113843393827855959940553621)
        ·
          refine ⟨5336409085680748122213451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113843393827855959940553621 5336409085680748122213451)
          ·
            refine ⟨8004613628521122183320177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5336409085680748122213451 8004613628521122183320177)
            ·
              refine ⟨6003460221390841637490133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8004613628521122183320177 6003460221390841637490133)
              ·
                refine ⟨140706098938847850878675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6003460221390841637490133 140706098938847850878675)
                ·
                  rfl

theorem cell23_7398652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 7].length) (baseStart_7398652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398652 prefixEnd_7398652 := by exact prefixLift 7398652
  have htrace : WordTrace (prefixWord ++ tailWord_7398652) baseStart_7398652 baseEnd_7398652 := by
    simpa [prefixWord, tailWord_7398652, baseEnd_7398652] using wordTrace_append hprefix tailTrace_7398652
  have hstable : (prefixWord ++ tailWord_7398652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398652).length < 2 ^ (prefixWord ++ tailWord_7398652).sum := by decide
  have hdescent : baseEnd_7398652 < baseStart_7398652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398696 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_7398696 : Nat := 118140960795 + 7398696 * 2 ^ 59
def prefixEnd_7398696 : Nat := 4983230072969 + 3 ^ 40 * 7398696 * 2
def baseEnd_7398696 : Nat := 3799087264497689801574023

theorem tailTrace_7398696 : CollatzResearch.WordTrace tailWord_7398696 prefixEnd_7398696 3799087264497689801574023 := by
  unfold tailWord_7398696
  simp only [CollatzResearch.WordTrace]
  refine ⟨134926306201897731760919971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179901741602530309014559961 134926306201897731760919971)
  ·
    refine ⟨202389459302846597641379957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134926306201897731760919971 202389459302846597641379957)
    ·
      refine ⟨18974011809641868528879371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202389459302846597641379957 18974011809641868528879371)
      ·
        refine ⟨28461017714462802793319057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18974011809641868528879371 28461017714462802793319057)
        ·
          refine ⟨21345763285847102094989293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28461017714462802793319057 21345763285847102094989293)
          ·
            refine ⟨8004661232192663285620985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21345763285847102094989293 8004661232192663285620985)
            ·
              refine ⟨6003495924144497464215739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8004661232192663285620985 6003495924144497464215739)
              ·
                refine ⟨9005243886216746196323609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6003495924144497464215739 9005243886216746196323609)
                ·
                  refine ⟨6753932914662559647242707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9005243886216746196323609 6753932914662559647242707)
                  ·
                    refine ⟨10130899371993839470864061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6753932914662559647242707 10130899371993839470864061)
                    ·
                      refine ⟨3799087264497689801574023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10130899371993839470864061 3799087264497689801574023)
                      ·
                        rfl

theorem cell23_7398696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_7398696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398696 prefixEnd_7398696 := by exact prefixLift 7398696
  have htrace : WordTrace (prefixWord ++ tailWord_7398696) baseStart_7398696 baseEnd_7398696 := by
    simpa [prefixWord, tailWord_7398696, baseEnd_7398696] using wordTrace_append hprefix tailTrace_7398696
  have hstable : (prefixWord ++ tailWord_7398696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398696).length < 2 ^ (prefixWord ++ tailWord_7398696).sum := by decide
  have hdescent : baseEnd_7398696 < baseStart_7398696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398738 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_7398738 : Nat := 118140960795 + 7398738 * 2 ^ 59
def prefixEnd_7398738 : Nat := 4983230072969 + 3 ^ 40 * 7398738 * 2
def baseEnd_7398738 : Nat := 1266369610228392879082943

theorem tailTrace_7398738 : CollatzResearch.WordTrace tailWord_7398738 prefixEnd_7398738 1266369610228392879082943 := by
  unfold tailWord_7398738
  simp only [CollatzResearch.WordTrace]
  refine ⟨67463536067410826173717217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179902762846428869796579245 67463536067410826173717217)
  ·
    refine ⟨50597652050558119630287913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67463536067410826173717217 50597652050558119630287913)
    ·
      refine ⟨37948239037918589722715935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50597652050558119630287913 37948239037918589722715935)
      ·
        refine ⟨56922358556877884584073903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37948239037918589722715935 56922358556877884584073903)
        ·
          refine ⟨85383537835316826876110855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56922358556877884584073903 85383537835316826876110855)
          ·
            refine ⟨128075306752975240314166283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85383537835316826876110855 128075306752975240314166283)
            ·
              refine ⟨192112960129462860471249425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128075306752975240314166283 192112960129462860471249425)
              ·
                refine ⟨144084720097097145353437069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192112960129462860471249425 144084720097097145353437069)
                ·
                  refine ⟨54031770036411429507538901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144084720097097145353437069 54031770036411429507538901)
                  ·
                    refine ⟨1266369610228392879082943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54031770036411429507538901 1266369610228392879082943)
                    ·
                      rfl

theorem cell23_7398738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_7398738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398738 prefixEnd_7398738 := by exact prefixLift 7398738
  have htrace : WordTrace (prefixWord ++ tailWord_7398738) baseStart_7398738 baseEnd_7398738 := by
    simpa [prefixWord, tailWord_7398738, baseEnd_7398738] using wordTrace_append hprefix tailTrace_7398738
  have hstable : (prefixWord ++ tailWord_7398738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398738).length < 2 ^ (prefixWord ++ tailWord_7398738).sum := by decide
  have hdescent : baseEnd_7398738 < baseStart_7398738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398745 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 2, 5, 2]
def baseStart_7398745 : Nat := 118140960795 + 7398745 * 2 ^ 59
def prefixEnd_7398745 : Nat := 4983230072969 + 3 ^ 40 * 7398745 * 2
def baseEnd_7398745 : Nat := 3799112425049760109861297

theorem tailTrace_7398745 : CollatzResearch.WordTrace tailWord_7398745 prefixEnd_7398745 3799112425049760109861297 := by
  unfold tailWord_7398745
  simp only [CollatzResearch.WordTrace]
  refine ⟨269854399580617944890373689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179902933053745296593582459 269854399580617944890373689)
  ·
    refine ⟨202390799685463458667780267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269854399580617944890373689 202390799685463458667780267)
    ·
      refine ⟨303586199528195188001670401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202390799685463458667780267 303586199528195188001670401)
      ·
        refine ⟨227689649646146391001252801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303586199528195188001670401 227689649646146391001252801)
        ·
          refine ⟨170767237234609793250939601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227689649646146391001252801 170767237234609793250939601)
          ·
            refine ⟨128075427925957344938204701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170767237234609793250939601 128075427925957344938204701)
            ·
              refine ⟨48028285472234004351826763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128075427925957344938204701 48028285472234004351826763)
              ·
                refine ⟨72042428208351006527740145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48028285472234004351826763 72042428208351006527740145)
                ·
                  refine ⟨54031821156263254895805109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72042428208351006527740145 54031821156263254895805109)
                  ·
                    refine ⟨5065483233399680146481729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54031821156263254895805109 5065483233399680146481729)
                    ·
                      refine ⟨3799112425049760109861297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065483233399680146481729 3799112425049760109861297)
                      ·
                        rfl

theorem cell23_7398745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 5, 2].length) (baseStart_7398745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398745 prefixEnd_7398745 := by exact prefixLift 7398745
  have htrace : WordTrace (prefixWord ++ tailWord_7398745) baseStart_7398745 baseEnd_7398745 := by
    simpa [prefixWord, tailWord_7398745, baseEnd_7398745] using wordTrace_append hprefix tailTrace_7398745
  have hstable : (prefixWord ++ tailWord_7398745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398745).length < 2 ^ (prefixWord ++ tailWord_7398745).sum := by decide
  have hdescent : baseEnd_7398745 < baseStart_7398745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398775 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 1, 6, 2]
def baseStart_7398775 : Nat := 118140960795 + 7398775 * 2 ^ 59
def prefixEnd_7398775 : Nat := 4983230072969 + 3 ^ 40 * 7398775 * 2
def baseEnd_7398775 : Nat := 3799127829469394992486159

theorem tailTrace_7398775 : CollatzResearch.WordTrace tailWord_7398775 prefixEnd_7398775 3799127829469394992486159 := by
  unfold tailWord_7398775
  simp only [CollatzResearch.WordTrace]
  refine ⟨269855493770509260013965779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179903662513672840009310519 269855493770509260013965779)
  ·
    refine ⟨404783240655763890020948669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269855493770509260013965779 404783240655763890020948669)
    ·
      refine ⟨151793715245911458757855751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404783240655763890020948669 151793715245911458757855751)
      ·
        refine ⟨227690572868867188136783627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151793715245911458757855751 227690572868867188136783627)
        ·
          refine ⟨341535859303300782205175441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227690572868867188136783627 341535859303300782205175441)
          ·
            refine ⟨256151894477475586653881581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341535859303300782205175441 256151894477475586653881581)
            ·
              refine ⟨96056960429053344995205593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256151894477475586653881581 96056960429053344995205593)
              ·
                refine ⟨72042720321790008746404195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96056960429053344995205593 72042720321790008746404195)
                ·
                  refine ⟨108064080482685013119606293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72042720321790008746404195 108064080482685013119606293)
                  ·
                    refine ⟨5065503772625859989981545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108064080482685013119606293 5065503772625859989981545)
                    ·
                      refine ⟨3799127829469394992486159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065503772625859989981545 3799127829469394992486159)
                      ·
                        rfl

theorem cell23_7398775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 6, 2].length) (baseStart_7398775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398775 prefixEnd_7398775 := by exact prefixLift 7398775
  have htrace : WordTrace (prefixWord ++ tailWord_7398775) baseStart_7398775 baseEnd_7398775 := by
    simpa [prefixWord, tailWord_7398775, baseEnd_7398775] using wordTrace_append hprefix tailTrace_7398775
  have hstable : (prefixWord ++ tailWord_7398775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398775).length < 2 ^ (prefixWord ++ tailWord_7398775).sum := by decide
  have hdescent : baseEnd_7398775 < baseStart_7398775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398792 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 2, 4, 2]
def baseStart_7398792 : Nat := 118140960795 + 7398792 * 2 ^ 59
def prefixEnd_7398792 : Nat := 4983230072969 + 3 ^ 40 * 7398792 * 2
def baseEnd_7398792 : Nat := 3799136558640521425973581

theorem tailTrace_7398792 : CollatzResearch.WordTrace tailWord_7398792 prefixEnd_7398792 3799136558640521425973581 := by
  unfold tailWord_7398792
  simp only [CollatzResearch.WordTrace]
  refine ⟨134928056905723835958667315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179904075874298447944889753 134928056905723835958667315)
  ·
    refine ⟨202392085358585753938000973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134928056905723835958667315 202392085358585753938000973)
    ·
      refine ⟨75897032009469657726750365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202392085358585753938000973 75897032009469657726750365)
      ·
        refine ⟨28461387003551121647531387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75897032009469657726750365 28461387003551121647531387)
        ·
          refine ⟨42692080505326682471297081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28461387003551121647531387 42692080505326682471297081)
          ·
            refine ⟨32019060378995011853472811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42692080505326682471297081 32019060378995011853472811)
            ·
              refine ⟨48028590568492517780209217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32019060378995011853472811 48028590568492517780209217)
              ·
                refine ⟨36021442926369388335156913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48028590568492517780209217 36021442926369388335156913)
                ·
                  refine ⟨27016082194777041251367685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36021442926369388335156913 27016082194777041251367685)
                  ·
                    refine ⟨5065515411520695234631441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27016082194777041251367685 5065515411520695234631441)
                    ·
                      refine ⟨3799136558640521425973581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065515411520695234631441 3799136558640521425973581)
                      ·
                        rfl

theorem cell23_7398792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_7398792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398792 prefixEnd_7398792 := by exact prefixLift 7398792
  have htrace : WordTrace (prefixWord ++ tailWord_7398792) baseStart_7398792 baseEnd_7398792 := by
    simpa [prefixWord, tailWord_7398792, baseEnd_7398792] using wordTrace_append hprefix tailTrace_7398792
  have hstable : (prefixWord ++ tailWord_7398792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398792).length < 2 ^ (prefixWord ++ tailWord_7398792).sum := by decide
  have hdescent : baseEnd_7398792 < baseStart_7398792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398795 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 3]
def baseStart_7398795 : Nat := 118140960795 + 7398795 * 2 ^ 59
def prefixEnd_7398795 : Nat := 4983230072969 + 3 ^ 40 * 7398795 * 2
def baseEnd_7398795 : Nat := 3799138099082484914236067

theorem tailTrace_7398795 : CollatzResearch.WordTrace tailWord_7398795 prefixEnd_7398795 3799138099082484914236067 := by
  unfold tailWord_7398795
  simp only [CollatzResearch.WordTrace]
  refine ⟨269856223230436803429693839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179904148820291202286462559 269856223230436803429693839)
  ·
    refine ⟨404784334845655205144540759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269856223230436803429693839 404784334845655205144540759)
    ·
      refine ⟨607176502268482807716811139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404784334845655205144540759 607176502268482807716811139)
      ·
        refine ⟨910764753402724211575216709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607176502268482807716811139 910764753402724211575216709)
        ·
          refine ⟨170768391263010789670353133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 910764753402724211575216709 170768391263010789670353133)
          ·
            refine ⟨64038146723629046126382425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170768391263010789670353133 64038146723629046126382425)
            ·
              refine ⟨48028610042721784594786819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64038146723629046126382425 48028610042721784594786819)
              ·
                refine ⟨72042915064082676892180229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48028610042721784594786819 72042915064082676892180229)
                ·
                  refine ⟨13508046574515501917283793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72042915064082676892180229 13508046574515501917283793)
                  ·
                    refine ⟨10131034930886626437962845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13508046574515501917283793 10131034930886626437962845)
                    ·
                      refine ⟨3799138099082484914236067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10131034930886626437962845 3799138099082484914236067)
                      ·
                        rfl

theorem cell23_7398795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 3].length) (baseStart_7398795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398795 prefixEnd_7398795 := by exact prefixLift 7398795
  have htrace : WordTrace (prefixWord ++ tailWord_7398795) baseStart_7398795 baseEnd_7398795 := by
    simpa [prefixWord, tailWord_7398795, baseEnd_7398795] using wordTrace_append hprefix tailTrace_7398795
  have hstable : (prefixWord ++ tailWord_7398795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398795).length < 2 ^ (prefixWord ++ tailWord_7398795).sum := by decide
  have hdescent : baseEnd_7398795 < baseStart_7398795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398859 : List Nat := [1, 1, 1, 1, 3, 3, 2, 6, 1, 1, 3]
def baseStart_7398859 : Nat := 118140960795 + 7398859 * 2 ^ 59
def prefixEnd_7398859 : Nat := 4983230072969 + 3 ^ 40 * 7398859 * 2
def baseEnd_7398859 : Nat := 3799170961844372663835773

theorem tailTrace_7398859 : CollatzResearch.WordTrace tailWord_7398859 prefixEnd_7398859 3799170961844372663835773 := by
  unfold tailWord_7398859
  simp only [CollatzResearch.WordTrace]
  refine ⟨269858557502204942360023631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179905705001469961573349087 269858557502204942360023631)
  ·
    refine ⟨404787836253307413540035447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269858557502204942360023631 404787836253307413540035447)
    ·
      refine ⟨607181754379961120310053171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404787836253307413540035447 607181754379961120310053171)
      ·
        refine ⟨910772631569941680465079757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607181754379961120310053171 910772631569941680465079757)
        ·
          refine ⟨341539736838728130174404909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 910772631569941680465079757 341539736838728130174404909)
          ·
            refine ⟨128077401314523048815401841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341539736838728130174404909 128077401314523048815401841)
            ·
              refine ⟨96058050985892286611551381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128077401314523048815401841 96058050985892286611551381)
              ·
                refine ⟨4502721139963700934916471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96058050985892286611551381 4502721139963700934916471)
                ·
                  refine ⟨6754081709945551402374707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4502721139963700934916471 6754081709945551402374707)
                  ·
                    refine ⟨10131122564918327103562061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6754081709945551402374707 10131122564918327103562061)
                    ·
                      refine ⟨3799170961844372663835773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10131122564918327103562061 3799170961844372663835773)
                      ·
                        rfl

theorem cell23_7398859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 1, 1, 3].length) (baseStart_7398859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398859 prefixEnd_7398859 := by exact prefixLift 7398859
  have htrace : WordTrace (prefixWord ++ tailWord_7398859) baseStart_7398859 baseEnd_7398859 := by
    simpa [prefixWord, tailWord_7398859, baseEnd_7398859] using wordTrace_append hprefix tailTrace_7398859
  have hstable : (prefixWord ++ tailWord_7398859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398859).length < 2 ^ (prefixWord ++ tailWord_7398859).sum := by decide
  have hdescent : baseEnd_7398859 < baseStart_7398859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398895 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 4]
def baseStart_7398895 : Nat := 118140960795 + 7398895 * 2 ^ 59
def prefixEnd_7398895 : Nat := 4983230072969 + 3 ^ 40 * 7398895 * 2
def baseEnd_7398895 : Nat := 3799189447147934522985607

theorem tailTrace_7398895 : CollatzResearch.WordTrace tailWord_7398895 prefixEnd_7398895 3799189447147934522985607 := by
  unfold tailWord_7398895
  simp only [CollatzResearch.WordTrace]
  refine ⟨269859870530074520508334139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179906580353383013672222759 269859870530074520508334139)
  ·
    refine ⟨404789805795111780762501209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269859870530074520508334139 404789805795111780762501209)
    ·
      refine ⟨303592354346333835571875907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404789805795111780762501209 303592354346333835571875907)
      ·
        refine ⟨455388531519500753357813861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303592354346333835571875907 455388531519500753357813861)
        ·
          refine ⟨85385349659906391254590099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 455388531519500753357813861 85385349659906391254590099)
          ·
            refine ⟨128078024489859586881885149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85385349659906391254590099 128078024489859586881885149)
            ·
              refine ⟨48029259183697345080706931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128078024489859586881885149 48029259183697345080706931)
              ·
                refine ⟨72043888775546017621060397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48029259183697345080706931 72043888775546017621060397)
                ·
                  refine ⟨27016458290829756607897649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72043888775546017621060397 27016458290829756607897649)
                  ·
                    refine ⟨20262343718122317455923237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27016458290829756607897649 20262343718122317455923237)
                    ·
                      refine ⟨3799189447147934522985607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20262343718122317455923237 3799189447147934522985607)
                      ·
                        rfl

theorem cell23_7398895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_7398895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398895 prefixEnd_7398895 := by exact prefixLift 7398895
  have htrace : WordTrace (prefixWord ++ tailWord_7398895) baseStart_7398895 baseEnd_7398895 := by
    simpa [prefixWord, tailWord_7398895, baseEnd_7398895] using wordTrace_append hprefix tailTrace_7398895
  have hstable : (prefixWord ++ tailWord_7398895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398895).length < 2 ^ (prefixWord ++ tailWord_7398895).sum := by decide
  have hdescent : baseEnd_7398895 < baseStart_7398895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398909 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_7398909 : Nat := 118140960795 + 7398909 * 2 ^ 59
def prefixEnd_7398909 : Nat := 4983230072969 + 3 ^ 40 * 7398909 * 2
def baseEnd_7398909 : Nat := 1266398878625699156070181

theorem tailTrace_7398909 : CollatzResearch.WordTrace tailWord_7398909 prefixEnd_7398909 1266398878625699156070181 := by
  unfold tailWord_7398909
  simp only [CollatzResearch.WordTrace]
  refine ⟨269860381152023800899343781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179906920768015867266229187 269860381152023800899343781)
  ·
    refine ⟨50598821466004462668626959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269860381152023800899343781 50598821466004462668626959)
    ·
      refine ⟨75898232199006694002940439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50598821466004462668626959 75898232199006694002940439)
      ·
        refine ⟨113847348298510041004410659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75898232199006694002940439 113847348298510041004410659)
        ·
          refine ⟨170771022447765061506615989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113847348298510041004410659 170771022447765061506615989)
          ·
            refine ⟨16009783354477974516245249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170771022447765061506615989 16009783354477974516245249)
            ·
              refine ⟨12007337515858480887183937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16009783354477974516245249 12007337515858480887183937)
              ·
                refine ⟨9005503136893860665387953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12007337515858480887183937 9005503136893860665387953)
                ·
                  refine ⟨6754127352670395499040965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9005503136893860665387953 6754127352670395499040965)
                  ·
                    refine ⟨1266398878625699156070181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6754127352670395499040965 1266398878625699156070181)
                    ·
                      rfl

theorem cell23_7398909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_7398909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398909 prefixEnd_7398909 := by exact prefixLift 7398909
  have htrace : WordTrace (prefixWord ++ tailWord_7398909) baseStart_7398909 baseEnd_7398909 := by
    simpa [prefixWord, tailWord_7398909, baseEnd_7398909] using wordTrace_append hprefix tailTrace_7398909
  have hstable : (prefixWord ++ tailWord_7398909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398909).length < 2 ^ (prefixWord ++ tailWord_7398909).sum := by decide
  have hdescent : baseEnd_7398909 < baseStart_7398909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398910 : List Nat := [4, 2, 2, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7398910 : Nat := 118140960795 + 7398910 * 2 ^ 59
def prefixEnd_7398910 : Nat := 4983230072969 + 3 ^ 40 * 7398910 * 2
def baseEnd_7398910 : Nat := 3799197149357751964298039

theorem tailTrace_7398910 : CollatzResearch.WordTrace tailWord_7398910 prefixEnd_7398910 3799197149357751964298039 := by
  unfold tailWord_7398910
  simp only [CollatzResearch.WordTrace]
  refine ⟨33732552203127522258766273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179906945083346785380086789 33732552203127522258766273)
  ·
    refine ⟨25299414152345641694074705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33732552203127522258766273 25299414152345641694074705)
    ·
      refine ⟨18974560614259231270556029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25299414152345641694074705 18974560614259231270556029)
      ·
        refine ⟨7115460230347211726458511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18974560614259231270556029 7115460230347211726458511)
        ·
          refine ⟨10673190345520817589687767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7115460230347211726458511 10673190345520817589687767)
          ·
            refine ⟨16009785518281226384531651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10673190345520817589687767 16009785518281226384531651)
            ·
              refine ⟨24014678277421839576797477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16009785518281226384531651 24014678277421839576797477)
              ·
                refine ⟨4502752177016594920649527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24014678277421839576797477 4502752177016594920649527)
                ·
                  refine ⟨6754128265524892380974291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4502752177016594920649527 6754128265524892380974291)
                  ·
                    refine ⟨10131192398287338571461437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6754128265524892380974291 10131192398287338571461437)
                    ·
                      refine ⟨3799197149357751964298039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10131192398287338571461437 3799197149357751964298039)
                      ·
                        rfl

theorem cell23_7398910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7398910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398910 prefixEnd_7398910 := by exact prefixLift 7398910
  have htrace : WordTrace (prefixWord ++ tailWord_7398910) baseStart_7398910 baseEnd_7398910 := by
    simpa [prefixWord, tailWord_7398910, baseEnd_7398910] using wordTrace_append hprefix tailTrace_7398910
  have hstable : (prefixWord ++ tailWord_7398910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398910).length < 2 ^ (prefixWord ++ tailWord_7398910).sum := by decide
  have hdescent : baseEnd_7398910 < baseStart_7398910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398922 : List Nat := [3, 1, 2, 2, 2, 4, 1, 8]
def baseStart_7398922 : Nat := 118140960795 + 7398922 * 2 ^ 59
def prefixEnd_7398922 : Nat := 4983230072969 + 3 ^ 40 * 7398922 * 2
def baseEnd_7398922 : Nat := 140711233745392811753629

theorem tailTrace_7398922 : CollatzResearch.WordTrace tailWord_7398922 prefixEnd_7398922 140711233745392811753629 := by
  unfold tailWord_7398922
  simp only [CollatzResearch.WordTrace]
  refine ⟨67465213825244176029891755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179907236867317802746378013 67465213825244176029891755)
  ·
    refine ⟨101197820737866264044837633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67465213825244176029891755 101197820737866264044837633)
    ·
      refine ⟨75898365553399698033628225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101197820737866264044837633 75898365553399698033628225)
      ·
        refine ⟨56923774165049773525221169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75898365553399698033628225 56923774165049773525221169)
        ·
          refine ⟨42692830623787330143915877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56923774165049773525221169 42692830623787330143915877)
          ·
            refine ⟨8004905741960124401984227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42692830623787330143915877 8004905741960124401984227)
            ·
              refine ⟨12007358612940186602976341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8004905741960124401984227 12007358612940186602976341)
              ·
                refine ⟨140711233745392811753629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12007358612940186602976341 140711233745392811753629)
                ·
                  rfl

theorem cell23_7398922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 8].length) (baseStart_7398922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398922 prefixEnd_7398922 := by exact prefixLift 7398922
  have htrace : WordTrace (prefixWord ++ tailWord_7398922) baseStart_7398922 baseEnd_7398922 := by
    simpa [prefixWord, tailWord_7398922, baseEnd_7398922] using wordTrace_append hprefix tailTrace_7398922
  have hstable : (prefixWord ++ tailWord_7398922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398922).length < 2 ^ (prefixWord ++ tailWord_7398922).sum := by decide
  have hdescent : baseEnd_7398922 < baseStart_7398922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7398983 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 2, 1, 3]
def baseStart_7398983 : Nat := 118140960795 + 7398983 * 2 ^ 59
def prefixEnd_7398983 : Nat := 4983230072969 + 3 ^ 40 * 7398983 * 2
def baseEnd_7398983 : Nat := 3799234633445530178685203

theorem tailTrace_7398983 : CollatzResearch.WordTrace tailWord_7398983 prefixEnd_7398983 3799234633445530178685203 := by
  unfold tailWord_7398983
  simp only [CollatzResearch.WordTrace]
  refine ⟨269863080153755711537537603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179908720102503807691691735 269863080153755711537537603)
  ·
    refine ⟨404794620230633567306306405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269863080153755711537537603 404794620230633567306306405)
    ·
      refine ⟨75898991293243793869932451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404794620230633567306306405 75898991293243793869932451)
      ·
        refine ⟨113848486939865690804898677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75898991293243793869932451 113848486939865690804898677)
        ·
          refine ⟨10673295650612408512959251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113848486939865690804898677 10673295650612408512959251)
          ·
            refine ⟨16009943475918612769438877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10673295650612408512959251 16009943475918612769438877)
            ·
              refine ⟨6003728803469479788539579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16009943475918612769438877 6003728803469479788539579)
              ·
                refine ⟨9005593205204219682809369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6003728803469479788539579 9005593205204219682809369)
                ·
                  refine ⟨6754194903903164762107027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9005593205204219682809369 6754194903903164762107027)
                  ·
                    refine ⟨10131292355854747143160541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6754194903903164762107027 10131292355854747143160541)
                    ·
                      refine ⟨3799234633445530178685203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10131292355854747143160541 3799234633445530178685203)
                      ·
                        rfl

theorem cell23_7398983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_7398983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7398983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7398983 prefixEnd_7398983 := by exact prefixLift 7398983
  have htrace : WordTrace (prefixWord ++ tailWord_7398983) baseStart_7398983 baseEnd_7398983 := by
    simpa [prefixWord, tailWord_7398983, baseEnd_7398983] using wordTrace_append hprefix tailTrace_7398983
  have hstable : (prefixWord ++ tailWord_7398983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7398983).length < 2 ^ (prefixWord ++ tailWord_7398983).sum := by decide
  have hdescent : baseEnd_7398983 < baseStart_7398983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7398983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399029 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 7]
def baseStart_7399029 : Nat := 118140960795 + 7399029 * 2 ^ 59
def prefixEnd_7399029 : Nat := 4983230072969 + 3 ^ 40 * 7399029 * 2
def baseEnd_7399029 : Nat := 422139805950626333189999

theorem tailTrace_7399029 : CollatzResearch.WordTrace tailWord_7399029 prefixEnd_7399029 422139805950626333189999 := by
  unfold tailWord_7399029
  simp only [CollatzResearch.WordTrace]
  refine ⟨269864757911589061393712141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179909838607726040929141427 269864757911589061393712141)
  ·
    refine ⟨101199284216845898022642053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269864757911589061393712141 101199284216845898022642053)
    ·
      refine ⟨18974865790658605879245385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101199284216845898022642053 18974865790658605879245385)
      ·
        refine ⟨14231149342993954409434039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18974865790658605879245385 14231149342993954409434039)
        ·
          refine ⟨21346724014490931614151059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14231149342993954409434039 21346724014490931614151059)
          ·
            refine ⟨32020086021736397421226589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21346724014490931614151059 32020086021736397421226589)
            ·
              refine ⟨12007532258151149032959971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32020086021736397421226589 12007532258151149032959971)
              ·
                refine ⟨18011298387226723549439957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12007532258151149032959971 18011298387226723549439957)
                ·
                  refine ⟨422139805950626333189999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18011298387226723549439957 422139805950626333189999)
                  ·
                    rfl

theorem cell23_7399029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_7399029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399029 prefixEnd_7399029 := by exact prefixLift 7399029
  have htrace : WordTrace (prefixWord ++ tailWord_7399029) baseStart_7399029 baseEnd_7399029 := by
    simpa [prefixWord, tailWord_7399029, baseEnd_7399029] using wordTrace_append hprefix tailTrace_7399029
  have hstable : (prefixWord ++ tailWord_7399029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399029).length < 2 ^ (prefixWord ++ tailWord_7399029).sum := by decide
  have hdescent : baseEnd_7399029 < baseStart_7399029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399080 : List Nat := [2, 1, 7, 1, 1, 1, 1, 4, 5]
def baseStart_7399080 : Nat := 118140960795 + 7399080 * 2 ^ 59
def prefixEnd_7399080 : Nat := 4983230072969 + 3 ^ 40 * 7399080 * 2
def baseEnd_7399080 : Nat := 422142715674335144352473

theorem tailTrace_7399080 : CollatzResearch.WordTrace tailWord_7399080 prefixEnd_7399080 422142715674335144352473 := by
  unfold tailWord_7399080
  simp only [CollatzResearch.WordTrace]
  refine ⟨134933309017202148551909347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179911078689602864735879129 134933309017202148551909347)
  ·
    refine ⟨202399963525803222827864021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134933309017202148551909347 202399963525803222827864021)
    ·
      refine ⟨4743749145136013035028063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 202399963525803222827864021 4743749145136013035028063)
      ·
        refine ⟨7115623717704019552542095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4743749145136013035028063 7115623717704019552542095)
        ·
          refine ⟨10673435576556029328813143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7115623717704019552542095 10673435576556029328813143)
          ·
            refine ⟨16010153364834043993219715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10673435576556029328813143 16010153364834043993219715)
            ·
              refine ⟨24015230047251065989829573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16010153364834043993219715 24015230047251065989829573)
              ·
                refine ⟨4502855633859574873093045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24015230047251065989829573 4502855633859574873093045)
                ·
                  refine ⟨422142715674335144352473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4502855633859574873093045 422142715674335144352473)
                  ·
                    rfl

theorem cell23_7399080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 5].length) (baseStart_7399080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399080 prefixEnd_7399080 := by exact prefixLift 7399080
  have htrace : WordTrace (prefixWord ++ tailWord_7399080) baseStart_7399080 baseEnd_7399080 := by
    simpa [prefixWord, tailWord_7399080, baseEnd_7399080] using wordTrace_append hprefix tailTrace_7399080
  have hstable : (prefixWord ++ tailWord_7399080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399080).length < 2 ^ (prefixWord ++ tailWord_7399080).sum := by decide
  have hdescent : baseEnd_7399080 < baseStart_7399080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399110 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_7399110 : Nat := 118140960795 + 7399110 * 2 ^ 59
def prefixEnd_7399110 : Nat := 4983230072969 + 3 ^ 40 * 7399110 * 2
def baseEnd_7399110 : Nat := 1266433281829550393932373

theorem tailTrace_7399110 : CollatzResearch.WordTrace tailWord_7399110 prefixEnd_7399110 1266433281829550393932373 := by
  unfold tailWord_7399110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8433366007009237882106587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179911808149530408151607189 8433366007009237882106587)
  ·
    refine ⟨12650049010513856823159881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8433366007009237882106587 12650049010513856823159881)
    ·
      refine ⟨9487536757885392617369911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12650049010513856823159881 9487536757885392617369911)
      ·
        refine ⟨14231305136828088926054867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9487536757885392617369911 14231305136828088926054867)
        ·
          refine ⟨21346957705242133389082301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14231305136828088926054867 21346957705242133389082301)
          ·
            refine ⟨8005109139465800020905863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21346957705242133389082301 8005109139465800020905863)
            ·
              refine ⟨12007663709198700031358795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8005109139465800020905863 12007663709198700031358795)
              ·
                refine ⟨18011495563798050047038193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12007663709198700031358795 18011495563798050047038193)
                ·
                  refine ⟨13508621672848537535278645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18011495563798050047038193 13508621672848537535278645)
                  ·
                    refine ⟨1266433281829550393932373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13508621672848537535278645 1266433281829550393932373)
                    ·
                      rfl

theorem cell23_7399110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_7399110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399110 prefixEnd_7399110 := by exact prefixLift 7399110
  have htrace : WordTrace (prefixWord ++ tailWord_7399110) baseStart_7399110 baseEnd_7399110 := by
    simpa [prefixWord, tailWord_7399110, baseEnd_7399110] using wordTrace_append hprefix tailTrace_7399110
  have hstable : (prefixWord ++ tailWord_7399110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399110).length < 2 ^ (prefixWord ++ tailWord_7399110).sum := by decide
  have hdescent : baseEnd_7399110 < baseStart_7399110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399116 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 1, 4, 3]
def baseStart_7399116 : Nat := 118140960795 + 7399116 * 2 ^ 59
def prefixEnd_7399116 : Nat := 4983230072969 + 3 ^ 40 * 7399116 * 2
def baseEnd_7399116 : Nat := 3799302926372578158322091

theorem tailTrace_7399116 : CollatzResearch.WordTrace tailWord_7399116 prefixEnd_7399116 3799302926372578158322091 := by
  unfold tailWord_7399116
  simp only [CollatzResearch.WordTrace]
  refine ⟨134933965531136937626064601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179911954041515916834752801 134933965531136937626064601)
  ·
    refine ⟨101200474148352703219548451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134933965531136937626064601 101200474148352703219548451)
    ·
      refine ⟨151800711222529054829322677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101200474148352703219548451 151800711222529054829322677)
      ·
        refine ⟨14231316677112098890249001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151800711222529054829322677 14231316677112098890249001)
        ·
          refine ⟨10673487507834074167686751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14231316677112098890249001 10673487507834074167686751)
          ·
            refine ⟨16010231261751111251530127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10673487507834074167686751 16010231261751111251530127)
            ·
              refine ⟨24015346892626666877295191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16010231261751111251530127 24015346892626666877295191)
              ·
                refine ⟨36023020338940000315942787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24015346892626666877295191 36023020338940000315942787)
                ·
                  refine ⟨54034530508410000473914181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36023020338940000315942787 54034530508410000473914181)
                  ·
                    refine ⟨10131474470326875088858909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54034530508410000473914181 10131474470326875088858909)
                    ·
                      refine ⟨3799302926372578158322091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10131474470326875088858909 3799302926372578158322091)
                      ·
                        rfl

theorem cell23_7399116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_7399116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399116 prefixEnd_7399116 := by exact prefixLift 7399116
  have htrace : WordTrace (prefixWord ++ tailWord_7399116) baseStart_7399116 baseEnd_7399116 := by
    simpa [prefixWord, tailWord_7399116, baseEnd_7399116] using wordTrace_append hprefix tailTrace_7399116
  have hstable : (prefixWord ++ tailWord_7399116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399116).length < 2 ^ (prefixWord ++ tailWord_7399116).sum := by decide
  have hdescent : baseEnd_7399116 < baseStart_7399116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399146 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_7399146 : Nat := 118140960795 + 7399146 * 2 ^ 59
def prefixEnd_7399146 : Nat := 4983230072969 + 3 ^ 40 * 7399146 * 2
def baseEnd_7399146 : Nat := 3799318330792213040946953

theorem tailTrace_7399146 : CollatzResearch.WordTrace tailWord_7399146 prefixEnd_7399146 3799318330792213040946953 := by
  unfold tailWord_7399146
  simp only [CollatzResearch.WordTrace]
  refine ⟨67467256313041297593930323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179912683501443460250480861 67467256313041297593930323)
  ·
    refine ⟨101200884469561946390895485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67467256313041297593930323 101200884469561946390895485)
    ·
      refine ⟨37950331676085729896585807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101200884469561946390895485 37950331676085729896585807)
      ·
        refine ⟨56925497514128594844878711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37950331676085729896585807 56925497514128594844878711)
        ·
          refine ⟨85388246271192892267318067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56925497514128594844878711 85388246271192892267318067)
          ·
            refine ⟨128082369406789338400977101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85388246271192892267318067 128082369406789338400977101)
            ·
              refine ⟨48030888527546001900366413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128082369406789338400977101 48030888527546001900366413)
              ·
                refine ⟨18011583197829750712637405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48030888527546001900366413 18011583197829750712637405)
                ·
                  refine ⟨6754343699186156517239027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18011583197829750712637405 6754343699186156517239027)
                  ·
                    refine ⟨10131515548779234775858541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6754343699186156517239027 10131515548779234775858541)
                    ·
                      refine ⟨3799318330792213040946953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10131515548779234775858541 3799318330792213040946953)
                      ·
                        rfl

theorem cell23_7399146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_7399146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399146 prefixEnd_7399146 := by exact prefixLift 7399146
  have htrace : WordTrace (prefixWord ++ tailWord_7399146) baseStart_7399146 baseEnd_7399146 := by
    simpa [prefixWord, tailWord_7399146, baseEnd_7399146] using wordTrace_append hprefix tailTrace_7399146
  have hstable : (prefixWord ++ tailWord_7399146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399146).length < 2 ^ (prefixWord ++ tailWord_7399146).sum := by decide
  have hdescent : baseEnd_7399146 < baseStart_7399146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399152 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 4]
def baseStart_7399152 : Nat := 118140960795 + 7399152 * 2 ^ 59
def prefixEnd_7399152 : Nat := 4983230072969 + 3 ^ 40 * 7399152 * 2
def baseEnd_7399152 : Nat := 3799321411676140017471925

theorem tailTrace_7399152 : CollatzResearch.WordTrace tailWord_7399152 prefixEnd_7399152 3799321411676140017471925 := by
  unfold tailWord_7399152
  simp only [CollatzResearch.WordTrace]
  refine ⟨134934622045071726700219855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179912829393428968933626473 134934622045071726700219855)
  ·
    refine ⟨202401933067607590050329783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134934622045071726700219855 202401933067607590050329783)
    ·
      refine ⟨303602899601411385075494675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202401933067607590050329783 303602899601411385075494675)
      ·
        refine ⟨455404349402117077613242013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303602899601411385075494675 455404349402117077613242013)
        ·
          refine ⟨170776631025793904104965755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455404349402117077613242013 170776631025793904104965755)
          ·
            refine ⟨256164946538690856157448633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170776631025793904104965755 256164946538690856157448633)
            ·
              refine ⟨192123709904018142118086475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256164946538690856157448633 192123709904018142118086475)
              ·
                refine ⟨288185564856027213177129713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192123709904018142118086475 288185564856027213177129713)
                ·
                  refine ⟨216139173642020409882847285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288185564856027213177129713 216139173642020409882847285)
                  ·
                    refine ⟨20263047528939413426516933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 216139173642020409882847285 20263047528939413426516933)
                    ·
                      refine ⟨3799321411676140017471925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20263047528939413426516933 3799321411676140017471925)
                      ·
                        rfl

theorem cell23_7399152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_7399152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399152 prefixEnd_7399152 := by exact prefixLift 7399152
  have htrace : WordTrace (prefixWord ++ tailWord_7399152) baseStart_7399152 baseEnd_7399152 := by
    simpa [prefixWord, tailWord_7399152, baseEnd_7399152] using wordTrace_append hprefix tailTrace_7399152
  have hstable : (prefixWord ++ tailWord_7399152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399152).length < 2 ^ (prefixWord ++ tailWord_7399152).sum := by decide
  have hdescent : baseEnd_7399152 < baseStart_7399152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399169 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_7399169 : Nat := 118140960795 + 7399169 * 2 ^ 59
def prefixEnd_7399169 : Nat := 4983230072969 + 3 ^ 40 * 7399169 * 2
def baseEnd_7399169 : Nat := 3799330140847266450959347

theorem tailTrace_7399169 : CollatzResearch.WordTrace tailWord_7399169 prefixEnd_7399169 3799330140847266450959347 := by
  unfold tailWord_7399169
  simp only [CollatzResearch.WordTrace]
  refine ⟨269869864131081865303808561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179913242754054576869205707 269869864131081865303808561)
  ·
    refine ⟨202402398098311398977856421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269869864131081865303808561 202402398098311398977856421)
    ·
      refine ⟨37950449643433387308348079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202402398098311398977856421 37950449643433387308348079)
      ·
        refine ⟨56925674465150080962522119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37950449643433387308348079 56925674465150080962522119)
        ·
          refine ⟨85388511697725121443783179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56925674465150080962522119 85388511697725121443783179)
          ·
            refine ⟨128082767546587682165674769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85388511697725121443783179 128082767546587682165674769)
            ·
              refine ⟨96062075659940761624256077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128082767546587682165674769 96062075659940761624256077)
              ·
                refine ⟨36023278372477785609096029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96062075659940761624256077 36023278372477785609096029)
                ·
                  refine ⟨13508729389679169603411011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36023278372477785609096029 13508729389679169603411011)
                  ·
                    refine ⟨20263094084518754405116517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13508729389679169603411011 20263094084518754405116517)
                    ·
                      refine ⟨3799330140847266450959347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20263094084518754405116517 3799330140847266450959347)
                      ·
                        rfl

theorem cell23_7399169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_7399169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399169 prefixEnd_7399169 := by exact prefixLift 7399169
  have htrace : WordTrace (prefixWord ++ tailWord_7399169) baseStart_7399169 baseEnd_7399169 := by
    simpa [prefixWord, tailWord_7399169, baseEnd_7399169] using wordTrace_append hprefix tailTrace_7399169
  have hstable : (prefixWord ++ tailWord_7399169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399169).length < 2 ^ (prefixWord ++ tailWord_7399169).sum := by decide
  have hdescent : baseEnd_7399169 < baseStart_7399169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399179 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 4, 4]
def baseStart_7399179 : Nat := 118140960795 + 7399179 * 2 ^ 59
def prefixEnd_7399179 : Nat := 4983230072969 + 3 ^ 40 * 7399179 * 2
def baseEnd_7399179 : Nat := 1266445091884603803944767

theorem tailTrace_7399179 : CollatzResearch.WordTrace tailWord_7399179 prefixEnd_7399179 1266445091884603803944767 := by
  unfold tailWord_7399179
  simp only [CollatzResearch.WordTrace]
  refine ⟨269870228861045637011672591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179913485907363758007781727 269870228861045637011672591)
  ·
    refine ⟨404805343291568455517508887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269870228861045637011672591 404805343291568455517508887)
    ·
      refine ⟨607208014937352683276263331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404805343291568455517508887 607208014937352683276263331)
      ·
        refine ⟨910812022406029024914394997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607208014937352683276263331 910812022406029024914394997)
        ·
          refine ⟨85388627100565221085724531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 910812022406029024914394997 85388627100565221085724531)
          ·
            refine ⟨128082940650847831628586797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85388627100565221085724531 128082940650847831628586797)
            ·
              refine ⟨48031102744067936860720049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128082940650847831628586797 48031102744067936860720049)
              ·
                refine ⟨36023327058050952645540037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48031102744067936860720049 36023327058050952645540037)
                ·
                  refine ⟨6754373823384553621038757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36023327058050952645540037 6754373823384553621038757)
                  ·
                    refine ⟨1266445091884603803944767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6754373823384553621038757 1266445091884603803944767)
                    ·
                      rfl

theorem cell23_7399179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 4].length) (baseStart_7399179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399179 prefixEnd_7399179 := by exact prefixLift 7399179
  have htrace : WordTrace (prefixWord ++ tailWord_7399179) baseStart_7399179 baseEnd_7399179 := by
    simpa [prefixWord, tailWord_7399179, baseEnd_7399179] using wordTrace_append hprefix tailTrace_7399179
  have hstable : (prefixWord ++ tailWord_7399179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399179).length < 2 ^ (prefixWord ++ tailWord_7399179).sum := by decide
  have hdescent : baseEnd_7399179 < baseStart_7399179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399189 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_7399189 : Nat := 118140960795 + 7399189 * 2 ^ 59
def prefixEnd_7399189 : Nat := 4983230072969 + 3 ^ 40 * 7399189 * 2
def baseEnd_7399189 : Nat := 3799340410460356372709255

theorem tailTrace_7399189 : CollatzResearch.WordTrace tailWord_7399189 prefixEnd_7399189 3799340410460356372709255 := by
  unfold tailWord_7399189
  simp only [CollatzResearch.WordTrace]
  refine ⟨269870593591009408719536621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179913729060672939146357747 269870593591009408719536621)
  ·
    refine ⟨101201472596628528269826233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269870593591009408719536621 101201472596628528269826233)
    ·
      refine ⟨75901104447471396202369675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101201472596628528269826233 75901104447471396202369675)
      ·
        refine ⟨113851656671207094303554513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75901104447471396202369675 113851656671207094303554513)
        ·
          refine ⟨85388742503405320727665885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113851656671207094303554513 85388742503405320727665885)
          ·
            refine ⟨32020778438776995272874707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85388742503405320727665885 32020778438776995272874707)
            ·
              refine ⟨48031167658165492909312061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32020778438776995272874707 48031167658165492909312061)
              ·
                refine ⟨18011687871812059840992023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48031167658165492909312061 18011687871812059840992023)
                ·
                  refine ⟨27017531807718089761488035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18011687871812059840992023 27017531807718089761488035)
                  ·
                    refine ⟨40526297711577134642232053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27017531807718089761488035 40526297711577134642232053)
                    ·
                      refine ⟨3799340410460356372709255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40526297711577134642232053 3799340410460356372709255)
                      ·
                        rfl

theorem cell23_7399189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_7399189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399189 prefixEnd_7399189 := by exact prefixLift 7399189
  have htrace : WordTrace (prefixWord ++ tailWord_7399189) baseStart_7399189 baseEnd_7399189 := by
    simpa [prefixWord, tailWord_7399189, baseEnd_7399189] using wordTrace_append hprefix tailTrace_7399189
  have hstable : (prefixWord ++ tailWord_7399189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399189).length < 2 ^ (prefixWord ++ tailWord_7399189).sum := by decide
  have hdescent : baseEnd_7399189 < baseStart_7399189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399192 : List Nat := [2, 1, 2, 3, 1, 1, 13]
def baseStart_7399192 : Nat := 118140960795 + 7399192 * 2 ^ 59
def prefixEnd_7399192 : Nat := 4983230072969 + 3 ^ 40 * 7399192 * 2
def baseEnd_7399192 : Nat := 46905456183979257542861

theorem tailTrace_7399192 : CollatzResearch.WordTrace tailWord_7399192 prefixEnd_7399192 46905456183979257542861 := by
  unfold tailWord_7399192
  simp only [CollatzResearch.WordTrace]
  refine ⟨134935351504999270115947915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179913802006665693487930553 134935351504999270115947915)
  ·
    refine ⟨202403027257498905173921873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134935351504999270115947915 202403027257498905173921873)
    ·
      refine ⟨151802270443124178880441405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202403027257498905173921873 151802270443124178880441405)
      ·
        refine ⟨56925851416171567080165527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151802270443124178880441405 56925851416171567080165527)
        ·
          refine ⟨85388777124257350620248291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56925851416171567080165527 85388777124257350620248291)
          ·
            refine ⟨128083165686386025930372437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85388777124257350620248291 128083165686386025930372437)
            ·
              refine ⟨46905456183979257542861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 128083165686386025930372437 46905456183979257542861)
              ·
                rfl

theorem cell23_7399192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 13].length) (baseStart_7399192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399192 prefixEnd_7399192 := by exact prefixLift 7399192
  have htrace : WordTrace (prefixWord ++ tailWord_7399192) baseStart_7399192 baseEnd_7399192 := by
    simpa [prefixWord, tailWord_7399192, baseEnd_7399192] using wordTrace_append hprefix tailTrace_7399192
  have hstable : (prefixWord ++ tailWord_7399192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399192).length < 2 ^ (prefixWord ++ tailWord_7399192).sum := by decide
  have hdescent : baseEnd_7399192 < baseStart_7399192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399196 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 2, 4]
def baseStart_7399196 : Nat := 118140960795 + 7399196 * 2 ^ 59
def prefixEnd_7399196 : Nat := 4983230072969 + 3 ^ 40 * 7399196 * 2
def baseEnd_7399196 : Nat := 1266448001608312615107241

theorem tailTrace_7399196 : CollatzResearch.WordTrace tailWord_7399196 prefixEnd_7399196 1266448001608312615107241 := by
  unfold tailWord_7399196
  simp only [CollatzResearch.WordTrace]
  refine ⟨134935424450992024457520721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179913899267989365943360961 134935424450992024457520721)
  ·
    refine ⟨101201568338244018343140541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134935424450992024457520721 101201568338244018343140541)
    ·
      refine ⟨37950588126841506878677703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101201568338244018343140541 37950588126841506878677703)
      ·
        refine ⟨56925882190262260318016555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37950588126841506878677703 56925882190262260318016555)
        ·
          refine ⟨85388823285393390477024833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56925882190262260318016555 85388823285393390477024833)
          ·
            refine ⟨64041617464045042857768625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85388823285393390477024833 64041617464045042857768625)
            ·
              refine ⟨48031213098033782143326469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64041617464045042857768625 48031213098033782143326469)
              ·
                refine ⟨9005852455881334151873713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48031213098033782143326469 9005852455881334151873713)
                ·
                  refine ⟨6754389341911000613905285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9005852455881334151873713 6754389341911000613905285)
                  ·
                    refine ⟨1266448001608312615107241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6754389341911000613905285 1266448001608312615107241)
                    ·
                      rfl

theorem cell23_7399196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_7399196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399196 prefixEnd_7399196 := by exact prefixLift 7399196
  have htrace : WordTrace (prefixWord ++ tailWord_7399196) baseStart_7399196 baseEnd_7399196 := by
    simpa [prefixWord, tailWord_7399196, baseEnd_7399196] using wordTrace_append hprefix tailTrace_7399196
  have hstable : (prefixWord ++ tailWord_7399196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399196).length < 2 ^ (prefixWord ++ tailWord_7399196).sum := by decide
  have hdescent : baseEnd_7399196 < baseStart_7399196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399203 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 3, 2, 2]
def baseStart_7399203 : Nat := 118140960795 + 7399203 * 2 ^ 59
def prefixEnd_7399203 : Nat := 4983230072969 + 3 ^ 40 * 7399203 * 2
def baseEnd_7399203 : Nat := 3799347599189519317934191

theorem tailTrace_7399203 : CollatzResearch.WordTrace tailWord_7399203 prefixEnd_7399203 3799347599189519317934191 := by
  unfold tailWord_7399203
  simp only [CollatzResearch.WordTrace]
  refine ⟨269871104212958689110546263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179914069475305792740364175 269871104212958689110546263)
  ·
    refine ⟨404806656319438033665819395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269871104212958689110546263 404806656319438033665819395)
    ·
      refine ⟨607209984479157050498729093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404806656319438033665819395 607209984479157050498729093)
      ·
        refine ⟨113851872089841946968511705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 607209984479157050498729093 113851872089841946968511705)
        ·
          refine ⟨85388904067381460226383779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113851872089841946968511705 85388904067381460226383779)
          ·
            refine ⟨128083356101072190339575669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85388904067381460226383779 128083356101072190339575669)
            ·
              refine ⟨12007814634475517844335219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128083356101072190339575669 12007814634475517844335219)
              ·
                refine ⟨18011721951713276766502829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12007814634475517844335219 18011721951713276766502829)
                ·
                  refine ⟨6754395731892478787438561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18011721951713276766502829 6754395731892478787438561)
                  ·
                    refine ⟨5065796798919359090578921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6754395731892478787438561 5065796798919359090578921)
                    ·
                      refine ⟨3799347599189519317934191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065796798919359090578921 3799347599189519317934191)
                      ·
                        rfl

theorem cell23_7399203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_7399203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399203 prefixEnd_7399203 := by exact prefixLift 7399203
  have htrace : WordTrace (prefixWord ++ tailWord_7399203) baseStart_7399203 baseEnd_7399203 := by
    simpa [prefixWord, tailWord_7399203, baseEnd_7399203] using wordTrace_append hprefix tailTrace_7399203
  have hstable : (prefixWord ++ tailWord_7399203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399203).length < 2 ^ (prefixWord ++ tailWord_7399203).sum := by decide
  have hdescent : baseEnd_7399203 < baseStart_7399203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399220 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_7399220 : Nat := 118140960795 + 7399220 * 2 ^ 59
def prefixEnd_7399220 : Nat := 4983230072969 + 3 ^ 40 * 7399220 * 2
def baseEnd_7399220 : Nat := 3799356328360645751421613

theorem tailTrace_7399220 : CollatzResearch.WordTrace tailWord_7399220 prefixEnd_7399220 3799356328360645751421613 := by
  unfold tailWord_7399220
  simp only [CollatzResearch.WordTrace]
  refine ⟨134935862126948550506957557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179914482835931400675943409 134935862126948550506957557)
  ·
    refine ⟨12650237074401426610027271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134935862126948550506957557 12650237074401426610027271)
    ·
      refine ⟨18975355611602139915040907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12650237074401426610027271 18975355611602139915040907)
      ·
        refine ⟨28463033417403209872561361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18975355611602139915040907 28463033417403209872561361)
        ·
          refine ⟨21347275063052407404421021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28463033417403209872561361 21347275063052407404421021)
          ·
            refine ⟨8005228148644652776657883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21347275063052407404421021 8005228148644652776657883)
            ·
              refine ⟨12007842222966979164986825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8005228148644652776657883 12007842222966979164986825)
              ·
                refine ⟨9005881667225234373740119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12007842222966979164986825 9005881667225234373740119)
                ·
                  refine ⟨13508822500837851560610179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9005881667225234373740119 13508822500837851560610179)
                  ·
                    refine ⟨20263233751256777340915269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13508822500837851560610179 20263233751256777340915269)
                    ·
                      refine ⟨3799356328360645751421613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20263233751256777340915269 3799356328360645751421613)
                      ·
                        rfl

theorem cell23_7399220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_7399220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399220 prefixEnd_7399220 := by exact prefixLift 7399220
  have htrace : WordTrace (prefixWord ++ tailWord_7399220) baseStart_7399220 baseEnd_7399220 := by
    simpa [prefixWord, tailWord_7399220, baseEnd_7399220] using wordTrace_append hprefix tailTrace_7399220
  have hstable : (prefixWord ++ tailWord_7399220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399220).length < 2 ^ (prefixWord ++ tailWord_7399220).sum := by decide
  have hdescent : baseEnd_7399220 < baseStart_7399220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399253 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_7399253 : Nat := 118140960795 + 7399253 * 2 ^ 59
def prefixEnd_7399253 : Nat := 4983230072969 + 3 ^ 40 * 7399253 * 2
def baseEnd_7399253 : Nat := 3799373273222244122308961

theorem tailTrace_7399253 : CollatzResearch.WordTrace tailWord_7399253 prefixEnd_7399253 3799373273222244122308961 := by
  unfold tailWord_7399253
  simp only [CollatzResearch.WordTrace]
  refine ⟨269872927862777547649866413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179915285241851698433244275 269872927862777547649866413)
  ·
    refine ⟨101202347948541580368699905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269872927862777547649866413 101202347948541580368699905)
    ·
      refine ⟨75901760961406185276524929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101202347948541580368699905 75901760961406185276524929)
      ·
        refine ⟨56926320721054638957393697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75901760961406185276524929 56926320721054638957393697)
        ·
          refine ⟨42694740540790979218045273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56926320721054638957393697 42694740540790979218045273)
          ·
            refine ⟨32021055405593234413533955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42694740540790979218045273 32021055405593234413533955)
            ·
              refine ⟨48031583108389851620300933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32021055405593234413533955 48031583108389851620300933)
              ·
                refine ⟨9005921832823097178806425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48031583108389851620300933 9005921832823097178806425)
                ·
                  refine ⟨6754441374617322884104819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9005921832823097178806425 6754441374617322884104819)
                  ·
                    refine ⟨10131662061925984326157229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6754441374617322884104819 10131662061925984326157229)
                    ·
                      refine ⟨3799373273222244122308961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10131662061925984326157229 3799373273222244122308961)
                      ·
                        rfl

theorem cell23_7399253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_7399253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399253 prefixEnd_7399253 := by exact prefixLift 7399253
  have htrace : WordTrace (prefixWord ++ tailWord_7399253) baseStart_7399253 baseEnd_7399253 := by
    simpa [prefixWord, tailWord_7399253, baseEnd_7399253] using wordTrace_append hprefix tailTrace_7399253
  have hstable : (prefixWord ++ tailWord_7399253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399253).length < 2 ^ (prefixWord ++ tailWord_7399253).sum := by decide
  have hdescent : baseEnd_7399253 < baseStart_7399253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399289 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 4]
def baseStart_7399289 : Nat := 118140960795 + 7399289 * 2 ^ 59
def prefixEnd_7399289 : Nat := 4983230072969 + 3 ^ 40 * 7399289 * 2
def baseEnd_7399289 : Nat := 3799391758525805981458795

theorem tailTrace_7399289 : CollatzResearch.WordTrace tailWord_7399289 prefixEnd_7399289 3799391758525805981458795 := by
  unfold tailWord_7399289
  simp only [CollatzResearch.WordTrace]
  refine ⟨269874240890647125798176921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179916160593764750532117947 269874240890647125798176921)
  ·
    refine ⟨202405680667985344348632691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269874240890647125798176921 202405680667985344348632691)
    ·
      refine ⟨303608521001978016522949037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202405680667985344348632691 303608521001978016522949037)
      ·
        refine ⟨113853195375741756196105889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303608521001978016522949037 113853195375741756196105889)
        ·
          refine ⟨85389896531806317147079417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113853195375741756196105889 85389896531806317147079417)
          ·
            refine ⟨64042422398854737860309563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85389896531806317147079417 64042422398854737860309563)
            ·
              refine ⟨96063633598282106790464345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64042422398854737860309563 96063633598282106790464345)
              ·
                refine ⟨72047725198711580092848259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96063633598282106790464345 72047725198711580092848259)
                ·
                  refine ⟨108071587798067370139272389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72047725198711580092848259 108071587798067370139272389)
                  ·
                    refine ⟨20263422712137631901113573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108071587798067370139272389 20263422712137631901113573)
                    ·
                      refine ⟨3799391758525805981458795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20263422712137631901113573 3799391758525805981458795)
                      ·
                        rfl

theorem cell23_7399289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_7399289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399289 prefixEnd_7399289 := by exact prefixLift 7399289
  have htrace : WordTrace (prefixWord ++ tailWord_7399289) baseStart_7399289 baseEnd_7399289 := by
    simpa [prefixWord, tailWord_7399289, baseEnd_7399289] using wordTrace_append hprefix tailTrace_7399289
  have hstable : (prefixWord ++ tailWord_7399289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399289).length < 2 ^ (prefixWord ++ tailWord_7399289).sum := by decide
  have hdescent : baseEnd_7399289 < baseStart_7399289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399293 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 4, 2, 2]
def baseStart_7399293 : Nat := 118140960795 + 7399293 * 2 ^ 59
def prefixEnd_7399293 : Nat := 4983230072969 + 3 ^ 40 * 7399293 * 2
def baseEnd_7399293 : Nat := 3799393812448423965808777

theorem tailTrace_7399293 : CollatzResearch.WordTrace tailWord_7399293 prefixEnd_7399293 3799393812448423965808777 := by
  unfold tailWord_7399293
  simp only [CollatzResearch.WordTrace]
  refine ⟨269874386782632634481322533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179916257855088422987548355 269874386782632634481322533)
  ·
    refine ⟨50601447521743618965247975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269874386782632634481322533 50601447521743618965247975)
    ·
      refine ⟨75902171282615428447871963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50601447521743618965247975 75902171282615428447871963)
      ·
        refine ⟨113853256923923142671807945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75902171282615428447871963 113853256923923142671807945)
        ·
          refine ⟨85389942692942357003855959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113853256923923142671807945 85389942692942357003855959)
          ·
            refine ⟨128084914039413535505783939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85389942692942357003855959 128084914039413535505783939)
            ·
              refine ⟨192127371059120303258675909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128084914039413535505783939 192127371059120303258675909)
              ·
                refine ⟨36023882073585056861001733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192127371059120303258675909 36023882073585056861001733)
                ·
                  refine ⟨6754477888797198161437825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36023882073585056861001733 6754477888797198161437825)
                  ·
                    refine ⟨5065858416597898621078369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6754477888797198161437825 5065858416597898621078369)
                    ·
                      refine ⟨3799393812448423965808777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065858416597898621078369 3799393812448423965808777)
                      ·
                        rfl

theorem cell23_7399293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_7399293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399293 prefixEnd_7399293 := by exact prefixLift 7399293
  have htrace : WordTrace (prefixWord ++ tailWord_7399293) baseStart_7399293 baseEnd_7399293 := by
    simpa [prefixWord, tailWord_7399293, baseEnd_7399293] using wordTrace_append hprefix tailTrace_7399293
  have hstable : (prefixWord ++ tailWord_7399293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399293).length < 2 ^ (prefixWord ++ tailWord_7399293).sum := by decide
  have hdescent : baseEnd_7399293 < baseStart_7399293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399297 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_7399297 : Nat := 118140960795 + 7399297 * 2 ^ 59
def prefixEnd_7399297 : Nat := 4983230072969 + 3 ^ 40 * 7399297 * 2
def baseEnd_7399297 : Nat := 3799395866371041950158759

theorem tailTrace_7399297 : CollatzResearch.WordTrace tailWord_7399297 prefixEnd_7399297 3799395866371041950158759 := by
  unfold tailWord_7399297
  simp only [CollatzResearch.WordTrace]
  refine ⟨269874532674618143164468145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179916355116412095442978763 269874532674618143164468145)
  ·
    refine ⟨202405899505963607373351109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269874532674618143164468145 202405899505963607373351109)
    ·
      refine ⟨37951106157368176382503333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202405899505963607373351109 37951106157368176382503333)
      ·
        refine ⟨7115832404506533071719375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37951106157368176382503333 7115832404506533071719375)
        ·
          refine ⟨10673748606759799607579063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7115832404506533071719375 10673748606759799607579063)
          ·
            refine ⟨16010622910139699411368595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10673748606759799607579063 16010622910139699411368595)
            ·
              refine ⟨24015934365209549117052893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16010622910139699411368595 24015934365209549117052893)
              ·
                refine ⟨9005975386953580918894835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24015934365209549117052893 9005975386953580918894835)
                ·
                  refine ⟨13508963080430371378342253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9005975386953580918894835 13508963080430371378342253)
                  ·
                    refine ⟨5065861155161389266878345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13508963080430371378342253 5065861155161389266878345)
                    ·
                      refine ⟨3799395866371041950158759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065861155161389266878345 3799395866371041950158759)
                      ·
                        rfl

theorem cell23_7399297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_7399297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399297 prefixEnd_7399297 := by exact prefixLift 7399297
  have htrace : WordTrace (prefixWord ++ tailWord_7399297) baseStart_7399297 baseEnd_7399297 := by
    simpa [prefixWord, tailWord_7399297, baseEnd_7399297] using wordTrace_append hprefix tailTrace_7399297
  have hstable : (prefixWord ++ tailWord_7399297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399297).length < 2 ^ (prefixWord ++ tailWord_7399297).sum := by decide
  have hdescent : baseEnd_7399297 < baseStart_7399297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399316 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 7]
def baseStart_7399316 : Nat := 118140960795 + 7399316 * 2 ^ 59
def prefixEnd_7399316 : Nat := 4983230072969 + 3 ^ 40 * 7399316 * 2
def baseEnd_7399316 : Nat := 422156180278164152869019

theorem tailTrace_7399316 : CollatzResearch.WordTrace tailWord_7399316 prefixEnd_7399316 422156180278164152869019 := by
  unfold tailWord_7399316
  simp only [CollatzResearch.WordTrace]
  refine ⟨134937612830774654704704901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179916817107699539606273201 134937612830774654704704901)
  ·
    refine ⟨25300802405770247757132169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134937612830774654704704901 25300802405770247757132169)
    ·
      refine ⟨18975601804327685817849127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25300802405770247757132169 18975601804327685817849127)
      ·
        refine ⟨28463402706491528726773691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18975601804327685817849127 28463402706491528726773691)
        ·
          refine ⟨42695104059737293090160537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28463402706491528726773691 42695104059737293090160537)
          ·
            refine ⟨32021328044802969817620403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42695104059737293090160537 32021328044802969817620403)
            ·
              refine ⟨48031992067204454726430605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32021328044802969817620403 48031992067204454726430605)
              ·
                refine ⟨18011997025201670522411477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48031992067204454726430605 18011997025201670522411477)
                ·
                  refine ⟨422156180278164152869019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18011997025201670522411477 422156180278164152869019)
                  ·
                    rfl

theorem cell23_7399316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_7399316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399316 prefixEnd_7399316 := by exact prefixLift 7399316
  have htrace : WordTrace (prefixWord ++ tailWord_7399316) baseStart_7399316 baseEnd_7399316 := by
    simpa [prefixWord, tailWord_7399316, baseEnd_7399316] using wordTrace_append hprefix tailTrace_7399316
  have hstable : (prefixWord ++ tailWord_7399316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399316).length < 2 ^ (prefixWord ++ tailWord_7399316).sum := by decide
  have hdescent : baseEnd_7399316 < baseStart_7399316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399327 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 1, 4, 2]
def baseStart_7399327 : Nat := 118140960795 + 7399327 * 2 ^ 59
def prefixEnd_7399327 : Nat := 4983230072969 + 3 ^ 40 * 7399327 * 2
def baseEnd_7399327 : Nat := 3799411270790676832783621

theorem tailTrace_7399327 : CollatzResearch.WordTrace tailWord_7399327 prefixEnd_7399327 3799411270790676832783621 := by
  unfold tailWord_7399327
  simp only [CollatzResearch.WordTrace]
  refine ⟨269875626864509458288060235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179917084576339638858706823 269875626864509458288060235)
  ·
    refine ⟨404813440296764187432090353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269875626864509458288060235 404813440296764187432090353)
    ·
      refine ⟨303610080222573140574067765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404813440296764187432090353 303610080222573140574067765)
      ·
        refine ⟨28463445020866231928818853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 303610080222573140574067765 28463445020866231928818853)
        ·
          refine ⟨5336895941412418486653535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28463445020866231928818853 5336895941412418486653535)
          ·
            refine ⟨8005343912118627729980303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5336895941412418486653535 8005343912118627729980303)
            ·
              refine ⟨12008015868177941594970455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8005343912118627729980303 12008015868177941594970455)
              ·
                refine ⟨18012023802266912392455683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12008015868177941594970455 18012023802266912392455683)
                ·
                  refine ⟨27018035703400368588683525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18012023802266912392455683 27018035703400368588683525)
                  ·
                    refine ⟨5065881694387569110378161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27018035703400368588683525 5065881694387569110378161)
                    ·
                      refine ⟨3799411270790676832783621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065881694387569110378161 3799411270790676832783621)
                      ·
                        rfl

theorem cell23_7399327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_7399327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399327 prefixEnd_7399327 := by exact prefixLift 7399327
  have htrace : WordTrace (prefixWord ++ tailWord_7399327) baseStart_7399327 baseEnd_7399327 := by
    simpa [prefixWord, tailWord_7399327, baseEnd_7399327] using wordTrace_append hprefix tailTrace_7399327
  have hstable : (prefixWord ++ tailWord_7399327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399327).length < 2 ^ (prefixWord ++ tailWord_7399327).sum := by decide
  have hdescent : baseEnd_7399327 < baseStart_7399327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399369 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_7399369 : Nat := 118140960795 + 7399369 * 2 ^ 59
def prefixEnd_7399369 : Nat := 4983230072969 + 3 ^ 40 * 7399369 * 2
def baseEnd_7399369 : Nat := 3799432836978165668458427

theorem tailTrace_7399369 : CollatzResearch.WordTrace tailWord_7399369 prefixEnd_7399369 3799432836978165668458427 := by
  unfold tailWord_7399369
  simp only [CollatzResearch.WordTrace]
  refine ⟨269877158730357299461089161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179918105820238199640726107 269877158730357299461089161)
  ·
    refine ⟨202407869047767974595816871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269877158730357299461089161 202407869047767974595816871)
    ·
      refine ⟨303611803571651961893725307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202407869047767974595816871 303611803571651961893725307)
      ·
        refine ⟨455417705357477942840587961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303611803571651961893725307 455417705357477942840587961)
        ·
          refine ⟨341563279018108457130440971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455417705357477942840587961 341563279018108457130440971)
          ·
            refine ⟨512344918527162685695661457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341563279018108457130440971 512344918527162685695661457)
            ·
              refine ⟨384258688895372014271746093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512344918527162685695661457 384258688895372014271746093)
              ·
                refine ⟨144097008335764505351904785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384258688895372014271746093 144097008335764505351904785)
                ·
                  refine ⟨108072756251823379013928589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144097008335764505351904785 108072756251823379013928589)
                  ·
                    refine ⟨40527283594433767130223221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108072756251823379013928589 40527283594433767130223221)
                    ·
                      refine ⟨3799432836978165668458427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40527283594433767130223221 3799432836978165668458427)
                      ·
                        rfl

theorem cell23_7399369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_7399369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399369 prefixEnd_7399369 := by exact prefixLift 7399369
  have htrace : WordTrace (prefixWord ++ tailWord_7399369) baseStart_7399369 baseEnd_7399369 := by
    simpa [prefixWord, tailWord_7399369, baseEnd_7399369] using wordTrace_append hprefix tailTrace_7399369
  have hstable : (prefixWord ++ tailWord_7399369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399369).length < 2 ^ (prefixWord ++ tailWord_7399369).sum := by decide
  have hdescent : baseEnd_7399369 < baseStart_7399369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399436 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_7399436 : Nat := 118140960795 + 7399436 * 2 ^ 59
def prefixEnd_7399436 : Nat := 4983230072969 + 3 ^ 40 * 7399436 * 2
def baseEnd_7399436 : Nat := 1266489080060672302106873

theorem tailTrace_7399436 : CollatzResearch.WordTrace tailWord_7399436 prefixEnd_7399436 1266489080060672302106873 := by
  unfold tailWord_7399436
  simp only [CollatzResearch.WordTrace]
  refine ⟨134939801210557284951889081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179919734947409713269185441 134939801210557284951889081)
  ·
    refine ⟨101204850907917963713916811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134939801210557284951889081 101204850907917963713916811)
    ·
      refine ⟨151807276361876945570875217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101204850907917963713916811 151807276361876945570875217)
      ·
        refine ⟨113855457271407709178156413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151807276361876945570875217 113855457271407709178156413)
        ·
          refine ⟨42695796476777890941808655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113855457271407709178156413 42695796476777890941808655)
          ·
            refine ⟨64043694715166836412712983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42695796476777890941808655 64043694715166836412712983)
            ·
              refine ⟨96065542072750254619069475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64043694715166836412712983 96065542072750254619069475)
              ·
                refine ⟨144098313109125381928604213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96065542072750254619069475 144098313109125381928604213)
                ·
                  refine ⟨13509216853980504555806645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144098313109125381928604213 13509216853980504555806645)
                  ·
                    refine ⟨1266489080060672302106873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13509216853980504555806645 1266489080060672302106873)
                    ·
                      rfl

theorem cell23_7399436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_7399436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399436 prefixEnd_7399436 := by exact prefixLift 7399436
  have htrace : WordTrace (prefixWord ++ tailWord_7399436) baseStart_7399436 baseEnd_7399436 := by
    simpa [prefixWord, tailWord_7399436, baseEnd_7399436] using wordTrace_append hprefix tailTrace_7399436
  have hstable : (prefixWord ++ tailWord_7399436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399436).length < 2 ^ (prefixWord ++ tailWord_7399436).sum := by decide
  have hdescent : baseEnd_7399436 < baseStart_7399436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399443 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 4, 3, 2]
def baseStart_7399443 : Nat := 118140960795 + 7399443 * 2 ^ 59
def prefixEnd_7399443 : Nat := 4983230072969 + 3 ^ 40 * 7399443 * 2
def baseEnd_7399443 : Nat := 3799470834546598378933087

theorem tailTrace_7399443 : CollatzResearch.WordTrace tailWord_7399443 prefixEnd_7399443 3799470834546598378933087 := by
  unfold tailWord_7399443
  simp only [CollatzResearch.WordTrace]
  refine ⟨269879857732089210099282983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179919905154726140066188655 269879857732089210099282983)
  ·
    refine ⟨404819786598133815148924475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269879857732089210099282983 404819786598133815148924475)
    ·
      refine ⟨607229679897200722723386713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404819786598133815148924475 607229679897200722723386713)
      ·
        refine ⟨455422259922900542042540035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607229679897200722723386713 455422259922900542042540035)
        ·
          refine ⟨683133389884350813063810053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455422259922900542042540035 683133389884350813063810053)
          ·
            refine ⟨128087510603315777449464385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 683133389884350813063810053 128087510603315777449464385)
            ·
              refine ⟨96065632952486833087098289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128087510603315777449464385 96065632952486833087098289)
              ·
                refine ⟨72049224714365124815323717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96065632952486833087098289 72049224714365124815323717)
                ·
                  refine ⟨13509229633943460902873197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72049224714365124815323717 13509229633943460902873197)
                  ·
                    refine ⟨5065961112728797838577449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13509229633943460902873197 5065961112728797838577449)
                    ·
                      refine ⟨3799470834546598378933087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5065961112728797838577449 3799470834546598378933087)
                      ·
                        rfl

theorem cell23_7399443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 3, 2].length) (baseStart_7399443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399443 prefixEnd_7399443 := by exact prefixLift 7399443
  have htrace : WordTrace (prefixWord ++ tailWord_7399443) baseStart_7399443 baseEnd_7399443 := by
    simpa [prefixWord, tailWord_7399443, baseEnd_7399443] using wordTrace_append hprefix tailTrace_7399443
  have hstable : (prefixWord ++ tailWord_7399443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399443).length < 2 ^ (prefixWord ++ tailWord_7399443).sum := by decide
  have hdescent : baseEnd_7399443 < baseStart_7399443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399450 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3]
def baseStart_7399450 : Nat := 118140960795 + 7399450 * 2 ^ 59
def prefixEnd_7399450 : Nat := 4983230072969 + 3 ^ 40 * 7399450 * 2
def baseEnd_7399450 : Nat := 3799474428911179851545555

theorem tailTrace_7399450 : CollatzResearch.WordTrace tailWord_7399450 prefixEnd_7399450 3799474428911179851545555 := by
  unfold tailWord_7399450
  simp only [CollatzResearch.WordTrace]
  refine ⟨67470028260765962573696951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179920075362042566863191869 67470028260765962573696951)
  ·
    refine ⟨101205042391148943860545427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67470028260765962573696951 101205042391148943860545427)
    ·
      refine ⟨151807563586723415790818141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101205042391148943860545427 151807563586723415790818141)
      ·
        refine ⟨56927836345021280921556803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151807563586723415790818141 56927836345021280921556803)
        ·
          refine ⟨85391754517531921382335205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56927836345021280921556803 85391754517531921382335205)
          ·
            refine ⟨16010953972037235259187851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85391754517531921382335205 16010953972037235259187851)
            ·
              refine ⟨24016430958055852888781777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16010953972037235259187851 24016430958055852888781777)
              ·
                refine ⟨18012323218541889666586333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24016430958055852888781777 18012323218541889666586333)
                ·
                  refine ⟨6754621206953208624969875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18012323218541889666586333 6754621206953208624969875)
                  ·
                    refine ⟨10131931810429812937454813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6754621206953208624969875 10131931810429812937454813)
                    ·
                      refine ⟨3799474428911179851545555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10131931810429812937454813 3799474428911179851545555)
                      ·
                        rfl

theorem cell23_7399450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_7399450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399450 prefixEnd_7399450 := by exact prefixLift 7399450
  have htrace : WordTrace (prefixWord ++ tailWord_7399450) baseStart_7399450 baseEnd_7399450 := by
    simpa [prefixWord, tailWord_7399450, baseEnd_7399450] using wordTrace_append hprefix tailTrace_7399450
  have hstable : (prefixWord ++ tailWord_7399450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399450).length < 2 ^ (prefixWord ++ tailWord_7399450).sum := by decide
  have hdescent : baseEnd_7399450 < baseStart_7399450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399453 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_7399453 : Nat := 118140960795 + 7399453 * 2 ^ 59
def prefixEnd_7399453 : Nat := 4983230072969 + 3 ^ 40 * 7399453 * 2
def baseEnd_7399453 : Nat := 1266491989784381113269347

theorem tailTrace_7399453 : CollatzResearch.WordTrace tailWord_7399453 prefixEnd_7399453 1266491989784381113269347 := by
  unfold tailWord_7399453
  simp only [CollatzResearch.WordTrace]
  refine ⟨269880222462052981807147013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179920148308035321204764675 269880222462052981807147013)
  ·
    refine ⟨50602541711634934088840065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269880222462052981807147013 50602541711634934088840065)
    ·
      refine ⟨37951906283726200566630049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50602541711634934088840065 37951906283726200566630049)
      ·
        refine ⟨28463929712794650424972537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37951906283726200566630049 28463929712794650424972537)
        ·
          refine ⟨21347947284595987818729403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28463929712794650424972537 21347947284595987818729403)
          ·
            refine ⟨32021920926893981728094105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21347947284595987818729403 32021920926893981728094105)
            ·
              refine ⟨24016440695170486296070579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32021920926893981728094105 24016440695170486296070579)
              ·
                refine ⟨36024661042755729444105869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24016440695170486296070579 36024661042755729444105869)
                ·
                  refine ⟨13509247891033398541539701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36024661042755729444105869 13509247891033398541539701)
                  ·
                    refine ⟨1266491989784381113269347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13509247891033398541539701 1266491989784381113269347)
                    ·
                      rfl

theorem cell23_7399453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_7399453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399453 prefixEnd_7399453 := by exact prefixLift 7399453
  have htrace : WordTrace (prefixWord ++ tailWord_7399453) baseStart_7399453 baseEnd_7399453 := by
    simpa [prefixWord, tailWord_7399453, baseEnd_7399453] using wordTrace_append hprefix tailTrace_7399453
  have hstable : (prefixWord ++ tailWord_7399453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399453).length < 2 ^ (prefixWord ++ tailWord_7399453).sum := by decide
  have hdescent : baseEnd_7399453 < baseStart_7399453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399470 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_7399470 : Nat := 118140960795 + 7399470 * 2 ^ 59
def prefixEnd_7399470 : Nat := 4983230072969 + 3 ^ 40 * 7399470 * 2
def baseEnd_7399470 : Nat := 1266494899508089924431821

theorem tailTrace_7399470 : CollatzResearch.WordTrace tailWord_7399470 prefixEnd_7399470 1266494899508089924431821 := by
  unfold tailWord_7399470
  simp only [CollatzResearch.WordTrace]
  refine ⟨33735105312873924213814483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179920561668660929140343909 33735105312873924213814483)
  ·
    refine ⟨50602657969310886320721725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33735105312873924213814483 50602657969310886320721725)
    ·
      refine ⟨18975996738491582370270647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50602657969310886320721725 18975996738491582370270647)
      ·
        refine ⟨28463995107737373555405971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18975996738491582370270647 28463995107737373555405971)
        ·
          refine ⟨42695992661606060333108957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28463995107737373555405971 42695992661606060333108957)
          ·
            refine ⟨16010997248102272624915859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42695992661606060333108957 16010997248102272624915859)
            ·
              refine ⟨24016495872153408937373789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16010997248102272624915859 24016495872153408937373789)
              ·
                refine ⟨9006185952057528351515171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24016495872153408937373789 9006185952057528351515171)
                ·
                  refine ⟨13509278928086292527272757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9006185952057528351515171 13509278928086292527272757)
                  ·
                    refine ⟨1266494899508089924431821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13509278928086292527272757 1266494899508089924431821)
                    ·
                      rfl

theorem cell23_7399470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_7399470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399470 prefixEnd_7399470 := by exact prefixLift 7399470
  have htrace : WordTrace (prefixWord ++ tailWord_7399470) baseStart_7399470 baseEnd_7399470 := by
    simpa [prefixWord, tailWord_7399470, baseEnd_7399470] using wordTrace_append hprefix tailTrace_7399470
  have hstable : (prefixWord ++ tailWord_7399470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399470).length < 2 ^ (prefixWord ++ tailWord_7399470).sum := by decide
  have hdescent : baseEnd_7399470 < baseStart_7399470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399523 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 3]
def baseStart_7399523 : Nat := 118140960795 + 7399523 * 2 ^ 59
def prefixEnd_7399523 : Nat := 4983230072969 + 3 ^ 40 * 7399523 * 2
def baseEnd_7399523 : Nat := 3799511912998958065932719

theorem tailTrace_7399523 : CollatzResearch.WordTrace tailWord_7399523 prefixEnd_7399523 3799511912998958065932719 := by
  unfold tailWord_7399523
  simp only [CollatzResearch.WordTrace]
  refine ⟨269882775571799383762195223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179921850381199589174796815 269882775571799383762195223)
  ·
    refine ⟨404824163357699075643292835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269882775571799383762195223 404824163357699075643292835)
    ·
      refine ⟨607236245036548613464939253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404824163357699075643292835 607236245036548613464939253)
      ·
        refine ⟨56928397972176432512338055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 607236245036548613464939253 56928397972176432512338055)
        ·
          refine ⟨85392596958264648768507083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56928397972176432512338055 85392596958264648768507083)
          ·
            refine ⟨128088895437396973152760625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85392596958264648768507083 128088895437396973152760625)
            ·
              refine ⟨96066671578047729864570469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128088895437396973152760625 96066671578047729864570469)
              ·
                refine ⟨18012500920883949349606963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96066671578047729864570469 18012500920883949349606963)
                ·
                  refine ⟨27018751381325924024410445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18012500920883949349606963 27018751381325924024410445)
                  ·
                    refine ⟨10132031767997221509153917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27018751381325924024410445 10132031767997221509153917)
                    ·
                      refine ⟨3799511912998958065932719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10132031767997221509153917 3799511912998958065932719)
                      ·
                        rfl

theorem cell23_7399523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_7399523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399523 prefixEnd_7399523 := by exact prefixLift 7399523
  have htrace : WordTrace (prefixWord ++ tailWord_7399523) baseStart_7399523 baseEnd_7399523 := by
    simpa [prefixWord, tailWord_7399523, baseEnd_7399523] using wordTrace_append hprefix tailTrace_7399523
  have hstable : (prefixWord ++ tailWord_7399523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399523).length < 2 ^ (prefixWord ++ tailWord_7399523).sum := by decide
  have hdescent : baseEnd_7399523 < baseStart_7399523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399524 : List Nat := [2, 3, 1, 1, 2, 1, 5, 3, 1, 2, 2]
def baseStart_7399524 : Nat := 118140960795 + 7399524 * 2 ^ 59
def prefixEnd_7399524 : Nat := 4983230072969 + 3 ^ 40 * 7399524 * 2
def baseEnd_7399524 : Nat := 3799512426479612562020215

theorem tailTrace_7399524 : CollatzResearch.WordTrace tailWord_7399524 prefixEnd_7399524 3799512426479612562020215 := by
  unfold tailWord_7399524
  simp only [CollatzResearch.WordTrace]
  refine ⟨134941406022397880466490813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179921874696530507288654417 134941406022397880466490813)
  ·
    refine ⟨50603027258399205174934055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134941406022397880466490813 50603027258399205174934055)
    ·
      refine ⟨75904540887598807762401083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50603027258399205174934055 75904540887598807762401083)
      ·
        refine ⟨113856811331398211643601625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75904540887598807762401083 113856811331398211643601625)
        ·
          refine ⟨85392608498548658732701219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113856811331398211643601625 85392608498548658732701219)
          ·
            refine ⟨128088912747822988099051829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85392608498548658732701219 128088912747822988099051829)
            ·
              refine ⟨12008335570108405134286109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128088912747822988099051829 12008335570108405134286109)
              ·
                refine ⟨4503125838790651925357291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12008335570108405134286109 4503125838790651925357291)
                ·
                  refine ⟨6754688758185977888035937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503125838790651925357291 6754688758185977888035937)
                  ·
                    refine ⟨5066016568639483416026953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6754688758185977888035937 5066016568639483416026953)
                    ·
                      refine ⟨3799512426479612562020215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066016568639483416026953 3799512426479612562020215)
                      ·
                        rfl

theorem cell23_7399524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_7399524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399524 prefixEnd_7399524 := by exact prefixLift 7399524
  have htrace : WordTrace (prefixWord ++ tailWord_7399524) baseStart_7399524 baseEnd_7399524 := by
    simpa [prefixWord, tailWord_7399524, baseEnd_7399524] using wordTrace_append hprefix tailTrace_7399524
  have hstable : (prefixWord ++ tailWord_7399524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399524).length < 2 ^ (prefixWord ++ tailWord_7399524).sum := by decide
  have hdescent : baseEnd_7399524 < baseStart_7399524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399530 : List Nat := [3, 1, 3, 2, 4, 1, 9]
def baseStart_7399530 : Nat := 118140960795 + 7399530 * 2 ^ 59
def prefixEnd_7399530 : Nat := 4983230072969 + 3 ^ 40 * 7399530 * 2
def baseEnd_7399530 : Nat := 46907598856339994303027

theorem tailTrace_7399530 : CollatzResearch.WordTrace tailWord_7399530 prefixEnd_7399530 46907598856339994303027 := by
  unfold tailWord_7399530
  simp only [CollatzResearch.WordTrace]
  refine ⟨67470757720693505989425011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179922020588516015971800029 67470757720693505989425011)
  ·
    refine ⟨101206136581040258984137517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67470757720693505989425011 101206136581040258984137517)
    ·
      refine ⟨37952301217890097119051569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101206136581040258984137517 37952301217890097119051569)
      ·
        refine ⟨28464225913417572839288677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37952301217890097119051569 28464225913417572839288677)
        ·
          refine ⟨5337042358765794907366627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28464225913417572839288677 5337042358765794907366627)
          ·
            refine ⟨8005563538148692361049941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5337042358765794907366627 8005563538148692361049941)
            ·
              refine ⟨46907598856339994303027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8005563538148692361049941 46907598856339994303027)
              ·
                rfl

theorem cell23_7399530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 9].length) (baseStart_7399530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399530 prefixEnd_7399530 := by exact prefixLift 7399530
  have htrace : WordTrace (prefixWord ++ tailWord_7399530) baseStart_7399530 baseEnd_7399530 := by
    simpa [prefixWord, tailWord_7399530, baseEnd_7399530] using wordTrace_append hprefix tailTrace_7399530
  have hstable : (prefixWord ++ tailWord_7399530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399530).length < 2 ^ (prefixWord ++ tailWord_7399530).sum := by decide
  have hdescent : baseEnd_7399530 < baseStart_7399530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399557 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 2, 1, 3]
def baseStart_7399557 : Nat := 118140960795 + 7399557 * 2 ^ 59
def prefixEnd_7399557 : Nat := 4983230072969 + 3 ^ 40 * 7399557 * 2
def baseEnd_7399557 : Nat := 3799529371341210932907563

theorem tailTrace_7399557 : CollatzResearch.WordTrace tailWord_7399557 prefixEnd_7399557 3799529371341210932907563 := by
  unfold tailWord_7399557
  simp only [CollatzResearch.WordTrace]
  refine ⟨269884015653676207568932925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179922677102450805045955283 269884015653676207568932925)
  ·
    refine ⟨101206505870128577838349847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269884015653676207568932925 101206505870128577838349847)
    ·
      refine ⟨151809758805192866757524771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101206505870128577838349847 151809758805192866757524771)
      ·
        refine ⟨227714638207789300136287157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151809758805192866757524771 227714638207789300136287157)
        ·
          refine ⟨21348247331980246887776921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227714638207789300136287157 21348247331980246887776921)
          ·
            refine ⟨16011185498985185165832691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21348247331980246887776921 16011185498985185165832691)
            ·
              refine ⟨24016778248477777748749037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16011185498985185165832691 24016778248477777748749037)
              ·
                refine ⟨9006291843179166655780889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24016778248477777748749037 9006291843179166655780889)
                ·
                  refine ⟨6754718882384374991835667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9006291843179166655780889 6754718882384374991835667)
                  ·
                    refine ⟨10132078323576562487753501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6754718882384374991835667 10132078323576562487753501)
                    ·
                      refine ⟨3799529371341210932907563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10132078323576562487753501 3799529371341210932907563)
                      ·
                        rfl

theorem cell23_7399557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_7399557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399557 prefixEnd_7399557 := by exact prefixLift 7399557
  have htrace : WordTrace (prefixWord ++ tailWord_7399557) baseStart_7399557 baseEnd_7399557 := by
    simpa [prefixWord, tailWord_7399557, baseEnd_7399557] using wordTrace_append hprefix tailTrace_7399557
  have hstable : (prefixWord ++ tailWord_7399557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399557).length < 2 ^ (prefixWord ++ tailWord_7399557).sum := by decide
  have hdescent : baseEnd_7399557 < baseStart_7399557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399584 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 1, 3, 2]
def baseStart_7399584 : Nat := 118140960795 + 7399584 * 2 ^ 59
def prefixEnd_7399584 : Nat := 4983230072969 + 3 ^ 40 * 7399584 * 2
def baseEnd_7399584 : Nat := 3799543235318882327269939

theorem tailTrace_7399584 : CollatzResearch.WordTrace tailWord_7399584 prefixEnd_7399584 3799543235318882327269939 := by
  unfold tailWord_7399584
  simp only [CollatzResearch.WordTrace]
  refine ⟨134942500212289195590082903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179923333616385594120110537 134942500212289195590082903)
  ·
    refine ⟨202413750318433793385124355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134942500212289195590082903 202413750318433793385124355)
    ·
      refine ⟨303620625477650690077686533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202413750318433793385124355 303620625477650690077686533)
      ·
        refine ⟨56928867277059504389566225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303620625477650690077686533 56928867277059504389566225)
        ·
          refine ⟨42696650457794628292174669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56928867277059504389566225 42696650457794628292174669)
          ·
            refine ⟨16011243921672985609565501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42696650457794628292174669 16011243921672985609565501)
            ·
              refine ⟨6004216470627369603587063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16011243921672985609565501 6004216470627369603587063)
              ·
                refine ⟨9006324705941054405380595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6004216470627369603587063 9006324705941054405380595)
                ·
                  refine ⟨13509487058911581608070893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9006324705941054405380595 13509487058911581608070893)
                  ·
                    refine ⟨5066057647091843103026585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13509487058911581608070893 5066057647091843103026585)
                    ·
                      refine ⟨3799543235318882327269939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066057647091843103026585 3799543235318882327269939)
                      ·
                        rfl

theorem cell23_7399584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_7399584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399584 prefixEnd_7399584 := by exact prefixLift 7399584
  have htrace : WordTrace (prefixWord ++ tailWord_7399584) baseStart_7399584 baseEnd_7399584 := by
    simpa [prefixWord, tailWord_7399584, baseEnd_7399584] using wordTrace_append hprefix tailTrace_7399584
  have hstable : (prefixWord ++ tailWord_7399584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399584).length < 2 ^ (prefixWord ++ tailWord_7399584).sum := by decide
  have hdescent : baseEnd_7399584 < baseStart_7399584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399614 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_7399614 : Nat := 118140960795 + 7399614 * 2 ^ 59
def prefixEnd_7399614 : Nat := 4983230072969 + 3 ^ 40 * 7399614 * 2
def baseEnd_7399614 : Nat := 3799558639738517209894801

theorem tailTrace_7399614 : CollatzResearch.WordTrace tailWord_7399614 prefixEnd_7399614 3799558639738517209894801 := by
  unfold tailWord_7399614
  simp only [CollatzResearch.WordTrace]
  refine ⟨33735761826808713287969737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179924063076313137535838597 33735761826808713287969737)
  ·
    refine ⟨25301821370106534965977303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33735761826808713287969737 25301821370106534965977303)
    ·
      refine ⟨37952732055159802448965955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25301821370106534965977303 37952732055159802448965955)
      ·
        refine ⟨56929098082739703673448933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37952732055159802448965955 56929098082739703673448933)
        ·
          refine ⟨10674205890513694438771675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56929098082739703673448933 10674205890513694438771675)
          ·
            refine ⟨16011308835770541658157513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10674205890513694438771675 16011308835770541658157513)
            ·
              refine ⟨12008481626827906243618135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16011308835770541658157513 12008481626827906243618135)
              ·
                refine ⟨18012722440241859365427203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12008481626827906243618135 18012722440241859365427203)
                ·
                  refine ⟨27019083660362789048140805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18012722440241859365427203 27019083660362789048140805)
                  ·
                    refine ⟨5066078186318022946526401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27019083660362789048140805 5066078186318022946526401)
                    ·
                      refine ⟨3799558639738517209894801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066078186318022946526401 3799558639738517209894801)
                      ·
                        rfl

theorem cell23_7399614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_7399614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399614 prefixEnd_7399614 := by exact prefixLift 7399614
  have htrace : WordTrace (prefixWord ++ tailWord_7399614) baseStart_7399614 baseEnd_7399614 := by
    simpa [prefixWord, tailWord_7399614, baseEnd_7399614] using wordTrace_append hprefix tailTrace_7399614
  have hstable : (prefixWord ++ tailWord_7399614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399614).length < 2 ^ (prefixWord ++ tailWord_7399614).sum := by decide
  have hdescent : baseEnd_7399614 < baseStart_7399614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399620 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 7]
def baseStart_7399620 : Nat := 118140960795 + 7399620 * 2 ^ 59
def prefixEnd_7399620 : Nat := 4983230072969 + 3 ^ 40 * 7399620 * 2
def baseEnd_7399620 : Nat := 422173524513604909602197

theorem tailTrace_7399620 : CollatzResearch.WordTrace tailWord_7399620 prefixEnd_7399620 422173524513604909602197 := by
  unfold tailWord_7399620
  simp only [CollatzResearch.WordTrace]
  refine ⟨134943156726223984664238157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179924208968298646218984209 134943156726223984664238157)
  ·
    refine ⟨50603683772333994249089309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134943156726223984664238157 50603683772333994249089309)
    ·
      refine ⟨18976381414625247843408491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50603683772333994249089309 18976381414625247843408491)
      ·
        refine ⟨28464572121937871765112737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18976381414625247843408491 28464572121937871765112737)
        ·
          refine ⟨21348429091453403823834553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28464572121937871765112737 21348429091453403823834553)
          ·
            refine ⟨16011321818590052867875915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21348429091453403823834553 16011321818590052867875915)
            ·
              refine ⟨24016982727885079301813873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16011321818590052867875915 24016982727885079301813873)
              ·
                refine ⟨18012737045913809476360405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24016982727885079301813873 18012737045913809476360405)
                ·
                  refine ⟨422173524513604909602197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18012737045913809476360405 422173524513604909602197)
                  ·
                    rfl

theorem cell23_7399620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_7399620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399620 prefixEnd_7399620 := by exact prefixLift 7399620
  have htrace : WordTrace (prefixWord ++ tailWord_7399620) baseStart_7399620 baseEnd_7399620 := by
    simpa [prefixWord, tailWord_7399620, baseEnd_7399620] using wordTrace_append hprefix tailTrace_7399620
  have hstable : (prefixWord ++ tailWord_7399620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399620).length < 2 ^ (prefixWord ++ tailWord_7399620).sum := by decide
  have hdescent : baseEnd_7399620 < baseStart_7399620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399670 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7399670 : Nat := 118140960795 + 7399670 * 2 ^ 59
def prefixEnd_7399670 : Nat := 4983230072969 + 3 ^ 40 * 7399670 * 2
def baseEnd_7399670 : Nat := 3799587394655168990794543

theorem tailTrace_7399670 : CollatzResearch.WordTrace tailWord_7399670 prefixEnd_7399670 3799587394655168990794543 := by
  unfold tailWord_7399670
  simp only [CollatzResearch.WordTrace]
  refine ⟨16868008568891676741737279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179925424734844551911864309 16868008568891676741737279)
  ·
    refine ⟨25302012853337515112605919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16868008568891676741737279 25302012853337515112605919)
    ·
      refine ⟨37953019280006272668908879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25302012853337515112605919 37953019280006272668908879)
      ·
        refine ⟨56929528920009409003363319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37953019280006272668908879 56929528920009409003363319)
        ·
          refine ⟨85394293380014113505044979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56929528920009409003363319 85394293380014113505044979)
          ·
            refine ⟨128091440070021170257567469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85394293380014113505044979 128091440070021170257567469)
            ·
              refine ⟨48034290026257938846587801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128091440070021170257567469 48034290026257938846587801)
              ·
                refine ⟨36025717519693454134940851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48034290026257938846587801 36025717519693454134940851)
                ·
                  refine ⟨54038576279540181202411277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36025717519693454134940851 54038576279540181202411277)
                  ·
                    refine ⟨20264466104827567950904229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54038576279540181202411277 20264466104827567950904229)
                    ·
                      refine ⟨3799587394655168990794543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20264466104827567950904229 3799587394655168990794543)
                      ·
                        rfl

theorem cell23_7399670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7399670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399670 prefixEnd_7399670 := by exact prefixLift 7399670
  have htrace : WordTrace (prefixWord ++ tailWord_7399670) baseStart_7399670 baseEnd_7399670 := by
    simpa [prefixWord, tailWord_7399670, baseEnd_7399670] using wordTrace_append hprefix tailTrace_7399670
  have hstable : (prefixWord ++ tailWord_7399670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399670).length < 2 ^ (prefixWord ++ tailWord_7399670).sum := by decide
  have hdescent : baseEnd_7399670 < baseStart_7399670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399680 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 3, 4]
def baseStart_7399680 : Nat := 118140960795 + 7399680 * 2 ^ 59
def prefixEnd_7399680 : Nat := 4983230072969 + 3 ^ 40 * 7399680 * 2
def baseEnd_7399680 : Nat := 1266530843153904650556499

theorem tailTrace_7399680 : CollatzResearch.WordTrace tailWord_7399680 prefixEnd_7399680 1266530843153904650556499 := by
  unfold tailWord_7399680
  simp only [CollatzResearch.WordTrace]
  refine ⟨134944250916115299787830247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179925667888153733050440329 134944250916115299787830247)
  ·
    refine ⟨202416376374172949681745371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134944250916115299787830247 202416376374172949681745371)
    ·
      refine ⟨303624564561259424522618057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202416376374172949681745371 303624564561259424522618057)
      ·
        refine ⟨227718423420944568391963543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303624564561259424522618057 227718423420944568391963543)
        ·
          refine ⟨341577635131416852587945315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227718423420944568391963543 341577635131416852587945315)
          ·
            refine ⟨512366452697125278881917973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341577635131416852587945315 512366452697125278881917973)
            ·
              refine ⟨24017177470177747447589905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 512366452697125278881917973 24017177470177747447589905)
              ·
                refine ⟨18012883102633310585692429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24017177470177747447589905 18012883102633310585692429)
                ·
                  refine ⟨6754831163487491469634661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18012883102633310585692429 6754831163487491469634661)
                  ·
                    refine ⟨1266530843153904650556499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6754831163487491469634661 1266530843153904650556499)
                    ·
                      rfl

theorem cell23_7399680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3, 4].length) (baseStart_7399680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399680 prefixEnd_7399680 := by exact prefixLift 7399680
  have htrace : WordTrace (prefixWord ++ tailWord_7399680) baseStart_7399680 baseEnd_7399680 := by
    simpa [prefixWord, tailWord_7399680, baseEnd_7399680] using wordTrace_append hprefix tailTrace_7399680
  have hstable : (prefixWord ++ tailWord_7399680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399680).length < 2 ^ (prefixWord ++ tailWord_7399680).sum := by decide
  have hdescent : baseEnd_7399680 < baseStart_7399680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399683 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 4]
def baseStart_7399683 : Nat := 118140960795 + 7399683 * 2 ^ 59
def prefixEnd_7399683 : Nat := 4983230072969 + 3 ^ 40 * 7399683 * 2
def baseEnd_7399683 : Nat := 3799594069903677439931983

theorem tailTrace_7399683 : CollatzResearch.WordTrace tailWord_7399683 prefixEnd_7399683 3799594069903677439931983 := by
  unfold tailWord_7399683
  simp only [CollatzResearch.WordTrace]
  refine ⟨269888611251219731088019703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179925740834146487392013135 269888611251219731088019703)
  ·
    refine ⟨404832916876829596632029555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269888611251219731088019703 404832916876829596632029555)
    ·
      refine ⟨607249375315244394948044333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404832916876829596632029555 607249375315244394948044333)
      ·
        refine ⟨227718515743216648105516625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607249375315244394948044333 227718515743216648105516625)
        ·
          refine ⟨170788886807412486079137469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227718515743216648105516625 170788886807412486079137469)
          ·
            refine ⟨64045832552779682279676551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170788886807412486079137469 64045832552779682279676551)
            ·
              refine ⟨96068748829169523419514827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64045832552779682279676551 96068748829169523419514827)
              ·
                refine ⟨144103123243754285129272241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96068748829169523419514827 144103123243754285129272241)
                ·
                  refine ⟨108077342432815713846954181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144103123243754285129272241 108077342432815713846954181)
                  ·
                    refine ⟨20264501706152946346303909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108077342432815713846954181 20264501706152946346303909)
                    ·
                      refine ⟨3799594069903677439931983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20264501706152946346303909 3799594069903677439931983)
                      ·
                        rfl

theorem cell23_7399683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_7399683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399683 prefixEnd_7399683 := by exact prefixLift 7399683
  have htrace : WordTrace (prefixWord ++ tailWord_7399683) baseStart_7399683 baseEnd_7399683 := by
    simpa [prefixWord, tailWord_7399683, baseEnd_7399683] using wordTrace_append hprefix tailTrace_7399683
  have hstable : (prefixWord ++ tailWord_7399683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399683).length < 2 ^ (prefixWord ++ tailWord_7399683).sum := by decide
  have hdescent : baseEnd_7399683 < baseStart_7399683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399690 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_7399690 : Nat := 118140960795 + 7399690 * 2 ^ 59
def prefixEnd_7399690 : Nat := 4983230072969 + 3 ^ 40 * 7399690 * 2
def baseEnd_7399690 : Nat := 3799597664268258912544451

theorem tailTrace_7399690 : CollatzResearch.WordTrace tailWord_7399690 prefixEnd_7399690 3799597664268258912544451 := by
  unfold tailWord_7399690
  simp only [CollatzResearch.WordTrace]
  refine ⟨67472216640548592820881131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179925911041462914189016349 67472216640548592820881131)
  ·
    refine ⟨101208324960822889231321697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67472216640548592820881131 101208324960822889231321697)
    ·
      refine ⟨75906243720617166923491273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101208324960822889231321697 75906243720617166923491273)
      ·
        refine ⟨56929682790462875192618455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75906243720617166923491273 56929682790462875192618455)
        ·
          refine ⟨85394524185694312788927683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56929682790462875192618455 85394524185694312788927683)
          ·
            refine ⟨128091786278541469183391525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85394524185694312788927683 128091786278541469183391525)
            ·
              refine ⟨24017209927226525471885911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128091786278541469183391525 24017209927226525471885911)
              ·
                refine ⟨36025814890839788207828867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24017209927226525471885911 36025814890839788207828867)
                ·
                  refine ⟨54038722336259682311743301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36025814890839788207828867 54038722336259682311743301)
                  ·
                    refine ⟨10132260438048690433451869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54038722336259682311743301 10132260438048690433451869)
                    ·
                      refine ⟨3799597664268258912544451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10132260438048690433451869 3799597664268258912544451)
                      ·
                        rfl

theorem cell23_7399690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_7399690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399690 prefixEnd_7399690 := by exact prefixLift 7399690
  have htrace : WordTrace (prefixWord ++ tailWord_7399690) baseStart_7399690 baseEnd_7399690 := by
    simpa [prefixWord, tailWord_7399690, baseEnd_7399690] using wordTrace_append hprefix tailTrace_7399690
  have hstable : (prefixWord ++ tailWord_7399690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399690).length < 2 ^ (prefixWord ++ tailWord_7399690).sum := by decide
  have hdescent : baseEnd_7399690 < baseStart_7399690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399713 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_7399713 : Nat := 118140960795 + 7399713 * 2 ^ 59
def prefixEnd_7399713 : Nat := 4983230072969 + 3 ^ 40 * 7399713 * 2
def baseEnd_7399713 : Nat := 3799609474323312322556845

theorem tailTrace_7399713 : CollatzResearch.WordTrace tailWord_7399713 prefixEnd_7399713 3799609474323312322556845 := by
  unfold tailWord_7399713
  simp only [CollatzResearch.WordTrace]
  refine ⟨269889705441111046211611793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179926470294074030807741195 269889705441111046211611793)
  ·
    refine ⟨202417279080833284658708845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269889705441111046211611793 202417279080833284658708845)
    ·
      refine ⟨75906479655312481747015817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202417279080833284658708845 75906479655312481747015817)
      ·
        refine ⟨56929859741484361310261863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75906479655312481747015817 56929859741484361310261863)
        ·
          refine ⟨85394789612226541965392795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56929859741484361310261863 85394789612226541965392795)
          ·
            refine ⟨128092184418339812948089193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85394789612226541965392795 128092184418339812948089193)
            ·
              refine ⟨96069138313754859711066895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128092184418339812948089193 96069138313754859711066895)
              ·
                refine ⟨144103707470632289566600343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96069138313754859711066895 144103707470632289566600343)
                ·
                  refine ⟨216155561205948434349900515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144103707470632289566600343 216155561205948434349900515)
                  ·
                    refine ⟨324233341808922651524850773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216155561205948434349900515 324233341808922651524850773)
                    ·
                      refine ⟨3799609474323312322556845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 324233341808922651524850773 3799609474323312322556845)
                      ·
                        rfl

theorem cell23_7399713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_7399713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399713 prefixEnd_7399713 := by exact prefixLift 7399713
  have htrace : WordTrace (prefixWord ++ tailWord_7399713) baseStart_7399713 baseEnd_7399713 := by
    simpa [prefixWord, tailWord_7399713, baseEnd_7399713] using wordTrace_append hprefix tailTrace_7399713
  have hstable : (prefixWord ++ tailWord_7399713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399713).length < 2 ^ (prefixWord ++ tailWord_7399713).sum := by decide
  have hdescent : baseEnd_7399713 < baseStart_7399713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399714 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_7399714 : Nat := 118140960795 + 7399714 * 2 ^ 59
def prefixEnd_7399714 : Nat := 4983230072969 + 3 ^ 40 * 7399714 * 2
def baseEnd_7399714 : Nat := 1266536662601322272881447

theorem tailTrace_7399714 : CollatzResearch.WordTrace tailWord_7399714 prefixEnd_7399714 1266536662601322272881447 := by
  unfold tailWord_7399714
  simp only [CollatzResearch.WordTrace]
  refine ⟨67472435478526855845599549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179926494609404948921598797 67472435478526855845599549)
  ·
    refine ⟨25302163304447570942099831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67472435478526855845599549 25302163304447570942099831)
    ·
      refine ⟨37953244956671356413149747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25302163304447570942099831 37953244956671356413149747)
      ·
        refine ⟨56929867435007034619724621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37953244956671356413149747 56929867435007034619724621)
        ·
          refine ⟨21348700288127637982396733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56929867435007034619724621 21348700288127637982396733)
          ·
            refine ⟨8005762608047864243398775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21348700288127637982396733 8005762608047864243398775)
            ·
              refine ⟨12008643912071796365098163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8005762608047864243398775 12008643912071796365098163)
              ·
                refine ⟨18012965868107694547647245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12008643912071796365098163 18012965868107694547647245)
                ·
                  refine ⟨6754862200540385455367717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18012965868107694547647245 6754862200540385455367717)
                  ·
                    refine ⟨1266536662601322272881447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6754862200540385455367717 1266536662601322272881447)
                    ·
                      rfl

theorem cell23_7399714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_7399714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399714 prefixEnd_7399714 := by exact prefixLift 7399714
  have htrace : WordTrace (prefixWord ++ tailWord_7399714) baseStart_7399714 baseEnd_7399714 := by
    simpa [prefixWord, tailWord_7399714, baseEnd_7399714] using wordTrace_append hprefix tailTrace_7399714
  have hstable : (prefixWord ++ tailWord_7399714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399714).length < 2 ^ (prefixWord ++ tailWord_7399714).sum := by decide
  have hdescent : baseEnd_7399714 < baseStart_7399714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399740 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_7399740 : Nat := 118140960795 + 7399740 * 2 ^ 59
def prefixEnd_7399740 : Nat := 4983230072969 + 3 ^ 40 * 7399740 * 2
def baseEnd_7399740 : Nat := 1266541112766994572306407

theorem tailTrace_7399740 : CollatzResearch.WordTrace tailWord_7399740 prefixEnd_7399740 1266541112766994572306407 := by
  unfold tailWord_7399740
  simp only [CollatzResearch.WordTrace]
  refine ⟨134945345106006614911422337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179927126808008819881896449 134945345106006614911422337)
  ·
    refine ⟨101209008829504961183566753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134945345106006614911422337 101209008829504961183566753)
    ·
      refine ⟨75906756622128720887675065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101209008829504961183566753 75906756622128720887675065)
      ·
        refine ⟨56930067466596540665756299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75906756622128720887675065 56930067466596540665756299)
        ·
          refine ⟨85395101199894810998634449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56930067466596540665756299 85395101199894810998634449)
          ·
            refine ⟨64046325899921108248975837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85395101199894810998634449 64046325899921108248975837)
            ·
              refine ⟨24017372212470415593365939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64046325899921108248975837 24017372212470415593365939)
              ·
                refine ⟨36026058318705623390048909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24017372212470415593365939 36026058318705623390048909)
                ·
                  refine ⟨13509771869514608771268341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36026058318705623390048909 13509771869514608771268341)
                  ·
                    refine ⟨1266541112766994572306407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13509771869514608771268341 1266541112766994572306407)
                    ·
                      rfl

theorem cell23_7399740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_7399740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399740 prefixEnd_7399740 := by exact prefixLift 7399740
  have htrace : WordTrace (prefixWord ++ tailWord_7399740) baseStart_7399740 baseEnd_7399740 := by
    simpa [prefixWord, tailWord_7399740, baseEnd_7399740] using wordTrace_append hprefix tailTrace_7399740
  have hstable : (prefixWord ++ tailWord_7399740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399740).length < 2 ^ (prefixWord ++ tailWord_7399740).sum := by decide
  have hdescent : baseEnd_7399740 < baseStart_7399740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399747 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 2, 3, 2]
def baseStart_7399747 : Nat := 118140960795 + 7399747 * 2 ^ 59
def prefixEnd_7399747 : Nat := 4983230072969 + 3 ^ 40 * 7399747 * 2
def baseEnd_7399747 : Nat := 3799626932665565189531689

theorem tailTrace_7399747 : CollatzResearch.WordTrace tailWord_7399747 prefixEnd_7399747 3799626932665565189531689 := by
  unfold tailWord_7399747
  simp only [CollatzResearch.WordTrace]
  refine ⟨269890945522987870018349495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179927297015325246678899663 269890945522987870018349495)
  ·
    refine ⟨404836418284481805027524243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269890945522987870018349495 404836418284481805027524243)
    ·
      refine ⟨607254627426722707541286365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404836418284481805027524243 607254627426722707541286365)
      ·
        refine ⟨227720485285021015327982387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607254627426722707541286365 227720485285021015327982387)
        ·
          refine ⟨341580727927531522991973581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227720485285021015327982387 341580727927531522991973581)
          ·
            refine ⟨128092772972824321121990093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341580727927531522991973581 128092772972824321121990093)
            ·
              refine ⟨48034789864809120420746285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128092772972824321121990093 48034789864809120420746285)
              ·
                refine ⟨18013046199303420157779857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48034789864809120420746285 18013046199303420157779857)
                ·
                  refine ⟨13509784649477565118334893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18013046199303420157779857 13509784649477565118334893)
                  ·
                    refine ⟨5066169243554086919375585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13509784649477565118334893 5066169243554086919375585)
                    ·
                      refine ⟨3799626932665565189531689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066169243554086919375585 3799626932665565189531689)
                      ·
                        rfl

theorem cell23_7399747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 3, 2].length) (baseStart_7399747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399747 prefixEnd_7399747 := by exact prefixLift 7399747
  have htrace : WordTrace (prefixWord ++ tailWord_7399747) baseStart_7399747 baseEnd_7399747 := by
    simpa [prefixWord, tailWord_7399747, baseEnd_7399747] using wordTrace_append hprefix tailTrace_7399747
  have hstable : (prefixWord ++ tailWord_7399747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399747).length < 2 ^ (prefixWord ++ tailWord_7399747).sum := by decide
  have hdescent : baseEnd_7399747 < baseStart_7399747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399764 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_7399764 : Nat := 118140960795 + 7399764 * 2 ^ 59
def prefixEnd_7399764 : Nat := 4983230072969 + 3 ^ 40 * 7399764 * 2
def baseEnd_7399764 : Nat := 3799635661836691623019111

theorem tailTrace_7399764 : CollatzResearch.WordTrace tailWord_7399764 prefixEnd_7399764 3799635661836691623019111 := by
  unfold tailWord_7399764
  simp only [CollatzResearch.WordTrace]
  refine ⟨134945782781963140960859173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179927710375950854614478897 134945782781963140960859173)
  ·
    refine ⟨25302334271618088930161095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134945782781963140960859173 25302334271618088930161095)
    ·
      refine ⟨37953501407427133395241643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25302334271618088930161095 37953501407427133395241643)
      ·
        refine ⟨56930252111140700092862465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37953501407427133395241643 56930252111140700092862465)
        ·
          refine ⟨42697689083355525069646849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56930252111140700092862465 42697689083355525069646849)
          ·
            refine ⟨32023266812516643802235137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42697689083355525069646849 32023266812516643802235137)
            ·
              refine ⟨24017450109387482851676353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32023266812516643802235137 24017450109387482851676353)
              ·
                refine ⟨18013087582040612138757265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24017450109387482851676353 18013087582040612138757265)
                ·
                  refine ⟨13509815686530459104067949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18013087582040612138757265 13509815686530459104067949)
                  ·
                    refine ⟨5066180882448922164025481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13509815686530459104067949 5066180882448922164025481)
                    ·
                      refine ⟨3799635661836691623019111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066180882448922164025481 3799635661836691623019111)
                      ·
                        rfl

theorem cell23_7399764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_7399764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399764 prefixEnd_7399764 := by exact prefixLift 7399764
  have htrace : WordTrace (prefixWord ++ tailWord_7399764) baseStart_7399764 baseEnd_7399764 := by
    simpa [prefixWord, tailWord_7399764, baseEnd_7399764] using wordTrace_append hprefix tailTrace_7399764
  have hstable : (prefixWord ++ tailWord_7399764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399764).length < 2 ^ (prefixWord ++ tailWord_7399764).sum := by decide
  have hdescent : baseEnd_7399764 < baseStart_7399764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399780 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_7399780 : Nat := 118140960795 + 7399780 * 2 ^ 59
def prefixEnd_7399780 : Nat := 4983230072969 + 3 ^ 40 * 7399780 * 2
def baseEnd_7399780 : Nat := 3799643877527163560419037

theorem tailTrace_7399780 : CollatzResearch.WordTrace tailWord_7399780 prefixEnd_7399780 3799643877527163560419037 := by
  unfold tailWord_7399780
  simp only [CollatzResearch.WordTrace]
  refine ⟨134946074565934158327150397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179928099421245544436200529 134946074565934158327150397)
  ·
    refine ⟨50604777962225309372681399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134946074565934158327150397 50604777962225309372681399)
    ·
      refine ⟨75907166943337964059022099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50604777962225309372681399 75907166943337964059022099)
      ·
        refine ⟨113860750415006946088533149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75907166943337964059022099 113860750415006946088533149)
        ·
          refine ⟨42697781405627604783199931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113860750415006946088533149 42697781405627604783199931)
          ·
            refine ⟨64046672108441407174799897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42697781405627604783199931 64046672108441407174799897)
            ·
              refine ⟨48035004081331055381099923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64046672108441407174799897 48035004081331055381099923)
              ·
                refine ⟨72052506121996583071649885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48035004081331055381099923 72052506121996583071649885)
                ·
                  refine ⟨27019689795748718651868707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72052506121996583071649885 27019689795748718651868707)
                  ·
                    refine ⟨40529534693623077977803061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27019689795748718651868707 40529534693623077977803061)
                    ·
                      refine ⟨3799643877527163560419037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40529534693623077977803061 3799643877527163560419037)
                      ·
                        rfl

theorem cell23_7399780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_7399780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399780 prefixEnd_7399780 := by exact prefixLift 7399780
  have htrace : WordTrace (prefixWord ++ tailWord_7399780) baseStart_7399780 baseEnd_7399780 := by
    simpa [prefixWord, tailWord_7399780, baseEnd_7399780] using wordTrace_append hprefix tailTrace_7399780
  have hstable : (prefixWord ++ tailWord_7399780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399780).length < 2 ^ (prefixWord ++ tailWord_7399780).sum := by decide
  have hdescent : baseEnd_7399780 < baseStart_7399780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399794 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 5, 2, 2]
def baseStart_7399794 : Nat := 118140960795 + 7399794 * 2 ^ 59
def prefixEnd_7399794 : Nat := 4983230072969 + 3 ^ 40 * 7399794 * 2
def baseEnd_7399794 : Nat := 3799651066256326505643973

theorem tailTrace_7399794 : CollatzResearch.WordTrace tailWord_7399794 prefixEnd_7399794 3799651066256326505643973 := by
  unfold tailWord_7399794
  simp only [CollatzResearch.WordTrace]
  refine ⟨67473164938454399261327609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179928439835878398030206957 67473164938454399261327609)
  ·
    refine ⟨50604873703840799445995707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67473164938454399261327609 50604873703840799445995707)
    ·
      refine ⟨75907310555761199168993561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50604873703840799445995707 75907310555761199168993561)
      ·
        refine ⟨56930482916820899376745171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75907310555761199168993561 56930482916820899376745171)
        ·
          refine ⟨85395724375231349065117757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56930482916820899376745171 85395724375231349065117757)
          ·
            refine ⟨32023396640711755899419159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85395724375231349065117757 32023396640711755899419159)
            ·
              refine ⟨48035094961067633849128739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32023396640711755899419159 48035094961067633849128739)
              ·
                refine ⟨72052642441601450773693109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48035094961067633849128739 72052642441601450773693109)
                ·
                  refine ⟨6754935228900136010033729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72052642441601450773693109 6754935228900136010033729)
                  ·
                    refine ⟨5066201421675102007525297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6754935228900136010033729 5066201421675102007525297)
                    ·
                      refine ⟨3799651066256326505643973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066201421675102007525297 3799651066256326505643973)
                      ·
                        rfl

theorem cell23_7399794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_7399794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399794 prefixEnd_7399794 := by exact prefixLift 7399794
  have htrace : WordTrace (prefixWord ++ tailWord_7399794) baseStart_7399794 baseEnd_7399794 := by
    simpa [prefixWord, tailWord_7399794, baseEnd_7399794] using wordTrace_append hprefix tailTrace_7399794
  have hstable : (prefixWord ++ tailWord_7399794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399794).length < 2 ^ (prefixWord ++ tailWord_7399794).sum := by decide
  have hdescent : baseEnd_7399794 < baseStart_7399794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399811 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 1, 1, 4]
def baseStart_7399811 : Nat := 118140960795 + 7399811 * 2 ^ 59
def prefixEnd_7399811 : Nat := 4983230072969 + 3 ^ 40 * 7399811 * 2
def baseEnd_7399811 : Nat := 3799659795427452939131395

theorem tailTrace_7399811 : CollatzResearch.WordTrace tailWord_7399811 prefixEnd_7399811 3799659795427452939131395 := by
  unfold tailWord_7399811
  simp only [CollatzResearch.WordTrace]
  refine ⟨269893279794756008948679287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179928853196504005965786191 269893279794756008948679287)
  ·
    refine ⟨404839919692134013423018931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269893279794756008948679287 404839919692134013423018931)
    ·
      refine ⟨607259879538201020134528397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404839919692134013423018931 607259879538201020134528397)
      ·
        refine ⟨227722454826825382550448149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607259879538201020134528397 227722454826825382550448149)
        ·
          refine ⟨10674490070007439807052257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 227722454826825382550448149 10674490070007439807052257)
          ·
            refine ⟨8005867552505579855289193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10674490070007439807052257 8005867552505579855289193)
            ·
              refine ⟨6004400664379184891466895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8005867552505579855289193 6004400664379184891466895)
              ·
                refine ⟨9006600996568777337200343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6004400664379184891466895 9006600996568777337200343)
                ·
                  refine ⟨13509901494853166005800515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9006600996568777337200343 13509901494853166005800515)
                  ·
                    refine ⟨20264852242279749008700773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13509901494853166005800515 20264852242279749008700773)
                    ·
                      refine ⟨3799659795427452939131395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20264852242279749008700773 3799659795427452939131395)
                      ·
                        rfl

theorem cell23_7399811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 1, 4].length) (baseStart_7399811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399811 prefixEnd_7399811 := by exact prefixLift 7399811
  have htrace : WordTrace (prefixWord ++ tailWord_7399811) baseStart_7399811 baseEnd_7399811 := by
    simpa [prefixWord, tailWord_7399811, baseEnd_7399811] using wordTrace_append hprefix tailTrace_7399811
  have hstable : (prefixWord ++ tailWord_7399811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399811).length < 2 ^ (prefixWord ++ tailWord_7399811).sum := by decide
  have hdescent : baseEnd_7399811 < baseStart_7399811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399828 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_7399828 : Nat := 118140960795 + 7399828 * 2 ^ 59
def prefixEnd_7399828 : Nat := 4983230072969 + 3 ^ 40 * 7399828 * 2
def baseEnd_7399828 : Nat := 3799668524598579372618817

theorem tailTrace_7399828 : CollatzResearch.WordTrace tailWord_7399828 prefixEnd_7399828 3799668524598579372618817 := by
  unfold tailWord_7399828
  simp only [CollatzResearch.WordTrace]
  refine ⟨134946949917847210426024069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179929266557129613901365425 134946949917847210426024069)
  ·
    refine ⟨25302553109596351954879513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134946949917847210426024069 25302553109596351954879513)
    ·
      refine ⟨18976914832197263966159635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25302553109596351954879513 18976914832197263966159635)
      ·
        refine ⟨28465372248295895949239453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18976914832197263966159635 28465372248295895949239453)
        ·
          refine ⟨10674514593110960980964795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28465372248295895949239453 10674514593110960980964795)
          ·
            refine ⟨16011771889666441471447193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10674514593110960980964795 16011771889666441471447193)
            ·
              refine ⟨12008828917249831103585395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16011771889666441471447193 12008828917249831103585395)
              ·
                refine ⟨18013243375874746655378093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12008828917249831103585395 18013243375874746655378093)
                ·
                  refine ⟨6754966265953029995766785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18013243375874746655378093 6754966265953029995766785)
                  ·
                    refine ⟨5066224699464772496825089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6754966265953029995766785 5066224699464772496825089)
                    ·
                      refine ⟨3799668524598579372618817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066224699464772496825089 3799668524598579372618817)
                      ·
                        rfl

theorem cell23_7399828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_7399828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399828 prefixEnd_7399828 := by exact prefixLift 7399828
  have htrace : WordTrace (prefixWord ++ tailWord_7399828) baseStart_7399828 baseEnd_7399828 := by
    simpa [prefixWord, tailWord_7399828, baseEnd_7399828] using wordTrace_append hprefix tailTrace_7399828
  have hstable : (prefixWord ++ tailWord_7399828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399828).length < 2 ^ (prefixWord ++ tailWord_7399828).sum := by decide
  have hdescent : baseEnd_7399828 < baseStart_7399828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399838 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_7399838 : Nat := 118140960795 + 7399838 * 2 ^ 59
def prefixEnd_7399838 : Nat := 4983230072969 + 3 ^ 40 * 7399838 * 2
def baseEnd_7399838 : Nat := 1266557886468374777831257

theorem tailTrace_7399838 : CollatzResearch.WordTrace tailWord_7399838 prefixEnd_7399838 1266557886468374777831257 := by
  unfold tailWord_7399838
  simp only [CollatzResearch.WordTrace]
  refine ⟨33736783070707274069989021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179929509710438795039941445 33736783070707274069989021)
  ·
    refine ⟨12651293651515227776245883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33736783070707274069989021 12651293651515227776245883)
    ·
      refine ⟨18976940477272841664368825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12651293651515227776245883 18976940477272841664368825)
      ·
        refine ⟨14232705357954631248276619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18976940477272841664368825 14232705357954631248276619)
        ·
          refine ⟨21349058036931946872414929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14232705357954631248276619 21349058036931946872414929)
          ·
            refine ⟨16011793527698960154311197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21349058036931946872414929 16011793527698960154311197)
            ·
              refine ⟨6004422572887110057866699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16011793527698960154311197 6004422572887110057866699)
              ·
                refine ⟨9006633859330665086800049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6004422572887110057866699 9006633859330665086800049)
                ·
                  refine ⟨6754975394497998815100037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9006633859330665086800049 6754975394497998815100037)
                  ·
                    refine ⟨1266557886468374777831257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6754975394497998815100037 1266557886468374777831257)
                    ·
                      rfl

theorem cell23_7399838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_7399838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399838 prefixEnd_7399838 := by exact prefixLift 7399838
  have htrace : WordTrace (prefixWord ++ tailWord_7399838) baseStart_7399838 baseEnd_7399838 := by
    simpa [prefixWord, tailWord_7399838, baseEnd_7399838] using wordTrace_append hprefix tailTrace_7399838
  have hstable : (prefixWord ++ tailWord_7399838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399838).length < 2 ^ (prefixWord ++ tailWord_7399838).sum := by decide
  have hdescent : baseEnd_7399838 < baseStart_7399838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399841 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7399841 : Nat := 118140960795 + 7399841 * 2 ^ 59
def prefixEnd_7399841 : Nat := 4983230072969 + 3 ^ 40 * 7399841 * 2
def baseEnd_7399841 : Nat := 3799675199847087821756257

theorem tailTrace_7399841 : CollatzResearch.WordTrace tailWord_7399841 prefixEnd_7399841 3799675199847087821756257 := by
  unfold tailWord_7399841
  simp only [CollatzResearch.WordTrace]
  refine ⟨269894373984647324072271377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179929582656431549381514251 269894373984647324072271377)
  ·
    refine ⟨202420780488485493054203533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269894373984647324072271377 202420780488485493054203533)
    ·
      refine ⟨75907792683182059895326325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202420780488485493054203533 75907792683182059895326325)
      ·
        refine ⟨7116355564048318115186843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75907792683182059895326325 7116355564048318115186843)
        ·
          refine ⟨10674533346072477172780265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7116355564048318115186843 10674533346072477172780265)
          ·
            refine ⟨8005900009554357879585199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10674533346072477172780265 8005900009554357879585199)
            ·
              refine ⟨12008850014331536819377799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8005900009554357879585199 12008850014331536819377799)
              ·
                refine ⟨18013275021497305229066699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12008850014331536819377799 18013275021497305229066699)
                ·
                  refine ⟨27019912532245957843600049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18013275021497305229066699 27019912532245957843600049)
                  ·
                    refine ⟨20264934399184468382700037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27019912532245957843600049 20264934399184468382700037)
                    ·
                      refine ⟨3799675199847087821756257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20264934399184468382700037 3799675199847087821756257)
                      ·
                        rfl

theorem cell23_7399841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7399841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399841 prefixEnd_7399841 := by exact prefixLift 7399841
  have htrace : WordTrace (prefixWord ++ tailWord_7399841) baseStart_7399841 baseEnd_7399841 := by
    simpa [prefixWord, tailWord_7399841, baseEnd_7399841] using wordTrace_append hprefix tailTrace_7399841
  have hstable : (prefixWord ++ tailWord_7399841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399841).length < 2 ^ (prefixWord ++ tailWord_7399841).sum := by decide
  have hdescent : baseEnd_7399841 < baseStart_7399841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399844 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_7399844 : Nat := 118140960795 + 7399844 * 2 ^ 59
def prefixEnd_7399844 : Nat := 4983230072969 + 3 ^ 40 * 7399844 * 2
def baseEnd_7399844 : Nat := 3799676740289051310018743

theorem tailTrace_7399844 : CollatzResearch.WordTrace tailWord_7399844 prefixEnd_7399844 3799676740289051310018743 := by
  unfold tailWord_7399844
  simp only [CollatzResearch.WordTrace]
  refine ⟨134947241701818227792315293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179929655602424303723087057 134947241701818227792315293)
  ·
    refine ⟨50605215638181835422118235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134947241701818227792315293 50605215638181835422118235)
    ·
      refine ⟨75907823457272753133177353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50605215638181835422118235 75907823457272753133177353)
      ·
        refine ⟨56930867592954564849883015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75907823457272753133177353 56930867592954564849883015)
        ·
          refine ⟨85396301389431847274824523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56930867592954564849883015 85396301389431847274824523)
          ·
            refine ⟨128094452084147770912236785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85396301389431847274824523 128094452084147770912236785)
            ·
              refine ⟨96070839063110828184177589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128094452084147770912236785 96070839063110828184177589)
              ·
                refine ⟨9006641162166640142266649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96070839063110828184177589 9006641162166640142266649)
                ·
                  refine ⟨6754980871624980106699987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9006641162166640142266649 6754980871624980106699987)
                  ·
                    refine ⟨10132471307437470160049981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6754980871624980106699987 10132471307437470160049981)
                    ·
                      refine ⟨3799676740289051310018743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10132471307437470160049981 3799676740289051310018743)
                      ·
                        rfl

theorem cell23_7399844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_7399844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399844 prefixEnd_7399844 := by exact prefixLift 7399844
  have htrace : WordTrace (prefixWord ++ tailWord_7399844) baseStart_7399844 baseEnd_7399844 := by
    simpa [prefixWord, tailWord_7399844, baseEnd_7399844] using wordTrace_append hprefix tailTrace_7399844
  have hstable : (prefixWord ++ tailWord_7399844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399844).length < 2 ^ (prefixWord ++ tailWord_7399844).sum := by decide
  have hdescent : baseEnd_7399844 < baseStart_7399844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399947 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 5]
def baseStart_7399947 : Nat := 118140960795 + 7399947 * 2 ^ 59
def prefixEnd_7399947 : Nat := 4983230072969 + 3 ^ 40 * 7399947 * 2
def baseEnd_7399947 : Nat := 3799729628796464407030769

theorem tailTrace_7399947 : CollatzResearch.WordTrace tailWord_7399947 prefixEnd_7399947 3799729628796464407030769 := by
  unfold tailWord_7399947
  simp only [CollatzResearch.WordTrace]
  refine ⟨269898240122263304175630095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179932160081508869450420063 269898240122263304175630095)
  ·
    refine ⟨404847360183394956263445143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269898240122263304175630095 404847360183394956263445143)
    ·
      refine ⟨607271040275092434395167715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404847360183394956263445143 607271040275092434395167715)
      ·
        refine ⟨910906560412638651592751573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607271040275092434395167715 910906560412638651592751573)
        ·
          refine ⟨21349372509671218396705115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 910906560412638651592751573 21349372509671218396705115)
          ·
            refine ⟨32024058764506827595057673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21349372509671218396705115 32024058764506827595057673)
            ·
              refine ⟨24018044073380120696293255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32024058764506827595057673 24018044073380120696293255)
              ·
                refine ⟨36027066110070181044439883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24018044073380120696293255 36027066110070181044439883)
                ·
                  refine ⟨54040599165105271566659825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36027066110070181044439883 54040599165105271566659825)
                  ·
                    refine ⟨40530449373828953674994869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54040599165105271566659825 40530449373828953674994869)
                    ·
                      refine ⟨3799729628796464407030769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40530449373828953674994869 3799729628796464407030769)
                      ·
                        rfl

theorem cell23_7399947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 5].length) (baseStart_7399947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399947 prefixEnd_7399947 := by exact prefixLift 7399947
  have htrace : WordTrace (prefixWord ++ tailWord_7399947) baseStart_7399947 baseEnd_7399947 := by
    simpa [prefixWord, tailWord_7399947, baseEnd_7399947] using wordTrace_append hprefix tailTrace_7399947
  have hstable : (prefixWord ++ tailWord_7399947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399947).length < 2 ^ (prefixWord ++ tailWord_7399947).sum := by decide
  have hdescent : baseEnd_7399947 < baseStart_7399947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7399957 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_7399957 : Nat := 118140960795 + 7399957 * 2 ^ 59
def prefixEnd_7399957 : Nat := 4983230072969 + 3 ^ 40 * 7399957 * 2
def baseEnd_7399957 : Nat := 3799734763603009367905723

theorem tailTrace_7399957 : CollatzResearch.WordTrace tailWord_7399957 prefixEnd_7399957 3799734763603009367905723 := by
  unfold tailWord_7399957
  simp only [CollatzResearch.WordTrace]
  refine ⟨269898604852227075883494125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179932403234818050588996083 269898604852227075883494125)
  ·
    refine ⟨101211976819585153456310297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269898604852227075883494125 101211976819585153456310297)
    ·
      refine ⟨75908982614688865092232723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101211976819585153456310297 75908982614688865092232723)
      ·
        refine ⟨113863473922033297638349085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75908982614688865092232723 113863473922033297638349085)
        ·
          refine ⟨42698802720762486614380907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113863473922033297638349085 42698802720762486614380907)
          ·
            refine ⟨64048204081143729921571361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42698802720762486614380907 64048204081143729921571361)
            ·
              refine ⟨48036153060857797441178521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64048204081143729921571361 48036153060857797441178521)
              ·
                refine ⟨36027114795643348080883891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48036153060857797441178521 36027114795643348080883891)
                ·
                  refine ⟨54040672193465022121325837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36027114795643348080883891 54040672193465022121325837)
                  ·
                    refine ⟨20265252072549383295497189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54040672193465022121325837 20265252072549383295497189)
                    ·
                      refine ⟨3799734763603009367905723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20265252072549383295497189 3799734763603009367905723)
                      ·
                        rfl

theorem cell23_7399957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_7399957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7399957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7399957 prefixEnd_7399957 := by exact prefixLift 7399957
  have htrace : WordTrace (prefixWord ++ tailWord_7399957) baseStart_7399957 baseEnd_7399957 := by
    simpa [prefixWord, tailWord_7399957, baseEnd_7399957] using wordTrace_append hprefix tailTrace_7399957
  have hstable : (prefixWord ++ tailWord_7399957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7399957).length < 2 ^ (prefixWord ++ tailWord_7399957).sum := by decide
  have hdescent : baseEnd_7399957 < baseStart_7399957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7399957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400001 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7400001 : Nat := 118140960795 + 7400001 * 2 ^ 59
def prefixEnd_7400001 : Nat := 4983230072969 + 3 ^ 40 * 7400001 * 2
def baseEnd_7400001 : Nat := 1266585785583935731918507

theorem tailTrace_7400001 : CollatzResearch.WordTrace tailWord_7400001 prefixEnd_7400001 1266585785583935731918507 := by
  unfold tailWord_7400001
  simp only [CollatzResearch.WordTrace]
  refine ⟨269900209664067671398095857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179933473109378447598730571 269900209664067671398095857)
  ·
    refine ⟨202425157248050753548571893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269900209664067671398095857 202425157248050753548571893)
    ·
      refine ⟨18977358492004758145178615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202425157248050753548571893 18977358492004758145178615)
      ·
        refine ⟨28466037738007137217767923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18977358492004758145178615 28466037738007137217767923)
        ·
          refine ⟨42699056607010705826651885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28466037738007137217767923 42699056607010705826651885)
          ·
            refine ⟨16012146227629014684994457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42699056607010705826651885 16012146227629014684994457)
            ·
              refine ⟨12009109670721761013745843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16012146227629014684994457 12009109670721761013745843)
              ·
                refine ⟨18013664506082641520618765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12009109670721761013745843 18013664506082641520618765)
                ·
                  refine ⟨6755124189780990570232037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18013664506082641520618765 6755124189780990570232037)
                  ·
                    refine ⟨1266585785583935731918507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6755124189780990570232037 1266585785583935731918507)
                    ·
                      rfl

theorem cell23_7400001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7400001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400001 prefixEnd_7400001 := by exact prefixLift 7400001
  have htrace : WordTrace (prefixWord ++ tailWord_7400001) baseStart_7400001 baseEnd_7400001 := by
    simpa [prefixWord, tailWord_7400001, baseEnd_7400001] using wordTrace_append hprefix tailTrace_7400001
  have hstable : (prefixWord ++ tailWord_7400001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400001).length < 2 ^ (prefixWord ++ tailWord_7400001).sum := by decide
  have hdescent : baseEnd_7400001 < baseStart_7400001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400044 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 1, 5]
def baseStart_7400044 : Nat := 118140960795 + 7400044 * 2 ^ 59
def prefixEnd_7400044 : Nat := 4983230072969 + 3 ^ 40 * 7400044 * 2
def baseEnd_7400044 : Nat := 1266593145473316842505941

theorem tailTrace_7400044 : CollatzResearch.WordTrace tailWord_7400044 prefixEnd_7400044 1266593145473316842505941 := by
  unfold tailWord_7400044
  simp only [CollatzResearch.WordTrace]
  refine ⟨134950889001455944870955593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179934518668607926494607457 134950889001455944870955593)
  ·
    refine ⟨101213166751091958653216695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134950889001455944870955593 101213166751091958653216695)
    ·
      refine ⟨151819750126637937979825043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101213166751091958653216695 151819750126637937979825043)
      ·
        refine ⟨227729625189956906969737565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151819750126637937979825043 227729625189956906969737565)
        ·
          refine ⟨85398609446233840113651587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227729625189956906969737565 85398609446233840113651587)
          ·
            refine ⟨128097914169350760170477381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85398609446233840113651587 128097914169350760170477381)
            ·
              refine ⟨24018358906753267531964509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128097914169350760170477381 24018358906753267531964509)
              ·
                refine ⟨9006884590032475324486691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24018358906753267531964509 9006884590032475324486691)
                ·
                  refine ⟨13510326885048712986730037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9006884590032475324486691 13510326885048712986730037)
                  ·
                    refine ⟨1266593145473316842505941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13510326885048712986730037 1266593145473316842505941)
                    ·
                      rfl

theorem cell23_7400044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_7400044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400044 prefixEnd_7400044 := by exact prefixLift 7400044
  have htrace : WordTrace (prefixWord ++ tailWord_7400044) baseStart_7400044 baseEnd_7400044 := by
    simpa [prefixWord, tailWord_7400044, baseEnd_7400044] using wordTrace_append hprefix tailTrace_7400044
  have hstable : (prefixWord ++ tailWord_7400044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400044).length < 2 ^ (prefixWord ++ tailWord_7400044).sum := by decide
  have hdescent : baseEnd_7400044 < baseStart_7400044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400087 : List Nat := [1, 1, 3, 3, 2, 1, 1, 11]
def baseStart_7400087 : Nat := 118140960795 + 7400087 * 2 ^ 59
def prefixEnd_7400087 : Nat := 4983230072969 + 3 ^ 40 * 7400087 * 2
def baseEnd_7400087 : Nat := 140733389484744217010375

theorem tailTrace_7400087 : CollatzResearch.WordTrace tailWord_7400087 prefixEnd_7400087 140733389484744217010375 := by
  unfold tailWord_7400087
  simp only [CollatzResearch.WordTrace]
  refine ⟨269903346341756108085726515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179935564227837405390484343 269903346341756108085726515)
  ·
    refine ⟨404855019512634162128589773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269903346341756108085726515 404855019512634162128589773)
    ·
      refine ⟨151820632317237810798221165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404855019512634162128589773 151820632317237810798221165)
      ·
        refine ⟨56932737118964179049332937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151820632317237810798221165 56932737118964179049332937)
        ·
          refine ⟨42699552839223134286999703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56932737118964179049332937 42699552839223134286999703)
          ·
            refine ⟨64049329258834701430499555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42699552839223134286999703 64049329258834701430499555)
            ·
              refine ⟨96073993888252052145749333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64049329258834701430499555 96073993888252052145749333)
              ·
                refine ⟨140733389484744217010375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 96073993888252052145749333 140733389484744217010375)
                ·
                  rfl

theorem cell23_7400087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 11].length) (baseStart_7400087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400087 prefixEnd_7400087 := by exact prefixLift 7400087
  have htrace : WordTrace (prefixWord ++ tailWord_7400087) baseStart_7400087 baseEnd_7400087 := by
    simpa [prefixWord, tailWord_7400087, baseEnd_7400087] using wordTrace_append hprefix tailTrace_7400087
  have hstable : (prefixWord ++ tailWord_7400087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400087).length < 2 ^ (prefixWord ++ tailWord_7400087).sum := by decide
  have hdescent : baseEnd_7400087 < baseStart_7400087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400104 : List Nat := [2, 1, 7, 13]
def baseStart_7400104 : Nat := 118140960795 + 7400104 * 2 ^ 59
def prefixEnd_7400104 : Nat := 4983230072969 + 3 ^ 40 * 7400104 * 2
def baseEnd_7400104 : Nat := 1737453244288623819281

theorem tailTrace_7400104 : CollatzResearch.WordTrace tailWord_7400104 prefixEnd_7400104 1737453244288623819281 := by
  unfold tailWord_7400104
  simp only [CollatzResearch.WordTrace]
  refine ⟨134951983191347259994547683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179935977588463013326063577 134951983191347259994547683)
  ·
    refine ⟨202427974787020889991821525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134951983191347259994547683 202427974787020889991821525)
    ·
      refine ⟨4744405659070802109183317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 202427974787020889991821525 4744405659070802109183317)
      ·
        refine ⟨1737453244288623819281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4744405659070802109183317 1737453244288623819281)
        ·
          rfl

theorem cell23_7400104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 13].length) (baseStart_7400104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400104 prefixEnd_7400104 := by exact prefixLift 7400104
  have htrace : WordTrace (prefixWord ++ tailWord_7400104) baseStart_7400104 baseEnd_7400104 := by
    simpa [prefixWord, tailWord_7400104, baseEnd_7400104] using wordTrace_append hprefix tailTrace_7400104
  have hstable : (prefixWord ++ tailWord_7400104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400104).length < 2 ^ (prefixWord ++ tailWord_7400104).sum := by decide
  have hdescent : baseEnd_7400104 < baseStart_7400104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400114 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_7400114 : Nat := 118140960795 + 7400114 * 2 ^ 59
def prefixEnd_7400114 : Nat := 4983230072969 + 3 ^ 40 * 7400114 * 2
def baseEnd_7400114 : Nat := 3799815380065765253642501

theorem tailTrace_7400114 : CollatzResearch.WordTrace tailWord_7400114 prefixEnd_7400114 3799815380065765253642501 := by
  unfold tailWord_7400114
  simp only [CollatzResearch.WordTrace]
  refine ⟨67476082778164572924239849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179936220741772194464639597 67476082778164572924239849)
  ·
    refine ⟨50607062083623429693179887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67476082778164572924239849 50607062083623429693179887)
    ·
      refine ⟨75910593125435144539769831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50607062083623429693179887 75910593125435144539769831)
      ·
        refine ⟨113865889688152716809654747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75910593125435144539769831 113865889688152716809654747)
        ·
          refine ⟨170798834532229075214482121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113865889688152716809654747 170798834532229075214482121)
          ·
            refine ⟨128099125899171806410861591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170798834532229075214482121 128099125899171806410861591)
            ·
              refine ⟨192148688848757709616292387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128099125899171806410861591 192148688848757709616292387)
              ·
                refine ⟨288223033273136564424438581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192148688848757709616292387 288223033273136564424438581)
                ·
                  refine ⟨27020909369356552914791117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 288223033273136564424438581 27020909369356552914791117)
                  ·
                    refine ⟨10132841013508707343046669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27020909369356552914791117 10132841013508707343046669)
                    ·
                      refine ⟨3799815380065765253642501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10132841013508707343046669 3799815380065765253642501)
                      ·
                        rfl

theorem cell23_7400114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_7400114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400114 prefixEnd_7400114 := by exact prefixLift 7400114
  have htrace : WordTrace (prefixWord ++ tailWord_7400114) baseStart_7400114 baseEnd_7400114 := by
    simpa [prefixWord, tailWord_7400114, baseEnd_7400114] using wordTrace_append hprefix tailTrace_7400114
  have hstable : (prefixWord ++ tailWord_7400114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400114).length < 2 ^ (prefixWord ++ tailWord_7400114).sum := by decide
  have hdescent : baseEnd_7400114 < baseStart_7400114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400115 : List Nat := [1, 1, 1, 2, 3, 5, 1, 4, 1, 2, 2]
def baseStart_7400115 : Nat := 118140960795 + 7400115 * 2 ^ 59
def prefixEnd_7400115 : Nat := 4983230072969 + 3 ^ 40 * 7400115 * 2
def baseEnd_7400115 : Nat := 3799815893546419749729997

theorem tailTrace_7400115 : CollatzResearch.WordTrace tailWord_7400115 prefixEnd_7400115 3799815893546419749729997 := by
  unfold tailWord_7400115
  simp only [CollatzResearch.WordTrace]
  refine ⟨269904367585654668867745799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179936245057103112578497199 269904367585654668867745799)
  ·
    refine ⟨404856551378482003301618699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269904367585654668867745799 404856551378482003301618699)
    ·
      refine ⟨607284827067723004952428049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404856551378482003301618699 607284827067723004952428049)
      ·
        refine ⟨455463620300792253714321037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607284827067723004952428049 455463620300792253714321037)
        ·
          refine ⟨170798857612797095142870389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455463620300792253714321037 170798857612797095142870389)
          ·
            refine ⟨16012392901199727669644099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170798857612797095142870389 16012392901199727669644099)
            ·
              refine ⟨24018589351799591504466149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16012392901199727669644099 24018589351799591504466149)
              ·
                refine ⟨4503485503462423407087403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24018589351799591504466149 4503485503462423407087403)
                ·
                  refine ⟨6755228255193635110631105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503485503462423407087403 6755228255193635110631105)
                  ·
                    refine ⟨5066421191395226332973329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6755228255193635110631105 5066421191395226332973329)
                    ·
                      refine ⟨3799815893546419749729997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066421191395226332973329 3799815893546419749729997)
                      ·
                        rfl

theorem cell23_7400115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 1, 2, 2].length) (baseStart_7400115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400115 prefixEnd_7400115 := by exact prefixLift 7400115
  have htrace : WordTrace (prefixWord ++ tailWord_7400115) baseStart_7400115 baseEnd_7400115 := by
    simpa [prefixWord, tailWord_7400115, baseEnd_7400115] using wordTrace_append hprefix tailTrace_7400115
  have hstable : (prefixWord ++ tailWord_7400115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400115).length < 2 ^ (prefixWord ++ tailWord_7400115).sum := by decide
  have hdescent : baseEnd_7400115 < baseStart_7400115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400149 : List Nat := [1, 3, 2, 5, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7400149 : Nat := 118140960795 + 7400149 * 2 ^ 59
def prefixEnd_7400149 : Nat := 4983230072969 + 3 ^ 40 * 7400149 * 2
def baseEnd_7400149 : Nat := 3799833351888672616704841

theorem tailTrace_7400149 : CollatzResearch.WordTrace tailWord_7400149 prefixEnd_7400149 3799833351888672616704841 := by
  unfold tailWord_7400149
  simp only [CollatzResearch.WordTrace]
  refine ⟨269905607667531492674483501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179937071778354328449655667 269905607667531492674483501)
  ·
    refine ⟨101214602875324309752931313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269905607667531492674483501 101214602875324309752931313)
    ·
      refine ⟨75910952156493232314698485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101214602875324309752931313 75910952156493232314698485)
      ·
        refine ⟨7116651764671240529502983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75910952156493232314698485 7116651764671240529502983)
        ·
          refine ⟨10674977647006860794254475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7116651764671240529502983 10674977647006860794254475)
          ·
            refine ⟨16012466470510291191381713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10674977647006860794254475 16012466470510291191381713)
            ·
              refine ⟨12009349852882718393536285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16012466470510291191381713 12009349852882718393536285)
              ·
                refine ⟨4503506194831019397576107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12009349852882718393536285 4503506194831019397576107)
                ·
                  refine ⟨6755259292246529096364161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503506194831019397576107 6755259292246529096364161)
                  ·
                    refine ⟨5066444469184896822273121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6755259292246529096364161 5066444469184896822273121)
                    ·
                      refine ⟨3799833351888672616704841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066444469184896822273121 3799833351888672616704841)
                      ·
                        rfl

theorem cell23_7400149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7400149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400149 prefixEnd_7400149 := by exact prefixLift 7400149
  have htrace : WordTrace (prefixWord ++ tailWord_7400149) baseStart_7400149 baseEnd_7400149 := by
    simpa [prefixWord, tailWord_7400149, baseEnd_7400149] using wordTrace_append hprefix tailTrace_7400149
  have hstable : (prefixWord ++ tailWord_7400149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400149).length < 2 ^ (prefixWord ++ tailWord_7400149).sum := by decide
  have hdescent : baseEnd_7400149 < baseStart_7400149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400164 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_7400164 : Nat := 118140960795 + 7400164 * 2 ^ 59
def prefixEnd_7400164 : Nat := 4983230072969 + 3 ^ 40 * 7400164 * 2
def baseEnd_7400164 : Nat := 1266613684699496686005757

theorem tailTrace_7400164 : CollatzResearch.WordTrace tailWord_7400164 prefixEnd_7400164 1266613684699496686005757 := by
  unfold tailWord_7400164
  simp only [CollatzResearch.WordTrace]
  refine ⟨134953077381238575118139773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179937436508318100157519697 134953077381238575118139773)
  ·
    refine ⟨50607404017964465669302415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134953077381238575118139773 50607404017964465669302415)
    ·
      refine ⟨75911106026946698503953623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50607404017964465669302415 75911106026946698503953623)
      ·
        refine ⟨113866659040420047755930435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75911106026946698503953623 113866659040420047755930435)
        ·
          refine ⟨170799988560630071633895653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113866659040420047755930435 170799988560630071633895653)
          ·
            refine ⟨32024997855118138431355435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170799988560630071633895653 32024997855118138431355435)
            ·
              refine ⟨48037496782677207647033153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32024997855118138431355435 48037496782677207647033153)
              ·
                refine ⟨36028122587007905735274865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48037496782677207647033153 36028122587007905735274865)
                ·
                  refine ⟨27021091940255929301456149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36028122587007905735274865 27021091940255929301456149)
                  ·
                    refine ⟨1266613684699496686005757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27021091940255929301456149 1266613684699496686005757)
                    ·
                      rfl

theorem cell23_7400164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_7400164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400164 prefixEnd_7400164 := by exact prefixLift 7400164
  have htrace : WordTrace (prefixWord ++ tailWord_7400164) baseStart_7400164 baseEnd_7400164 := by
    simpa [prefixWord, tailWord_7400164, baseEnd_7400164] using wordTrace_append hprefix tailTrace_7400164
  have hstable : (prefixWord ++ tailWord_7400164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400164).length < 2 ^ (prefixWord ++ tailWord_7400164).sum := by decide
  have hdescent : baseEnd_7400164 < baseStart_7400164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400165 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 2, 1, 3]
def baseStart_7400165 : Nat := 118140960795 + 7400165 * 2 ^ 59
def prefixEnd_7400165 : Nat := 4983230072969 + 3 ^ 40 * 7400165 * 2
def baseEnd_7400165 : Nat := 3799841567579144554104767

theorem tailTrace_7400165 : CollatzResearch.WordTrace tailWord_7400165 prefixEnd_7400165 3799841567579144554104767 := by
  unfold tailWord_7400165
  simp only [CollatzResearch.WordTrace]
  refine ⟨269906191235473527407065949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179937460823649018271377299 269906191235473527407065949)
  ·
    refine ⟨101214821713302572777649731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269906191235473527407065949 101214821713302572777649731)
    ·
      refine ⟨151822232569953859166474597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101214821713302572777649731 151822232569953859166474597)
      ·
        refine ⟨28466668606866348593713987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151822232569953859166474597 28466668606866348593713987)
        ·
          refine ⟨42700002910299522890570981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28466668606866348593713987 42700002910299522890570981)
          ·
            refine ⟨8006250545681160541982059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42700002910299522890570981 8006250545681160541982059)
            ·
              refine ⟨12009375818521740812973089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8006250545681160541982059 12009375818521740812973089)
              ·
                refine ⟨9007031863891305609729817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12009375818521740812973089 9007031863891305609729817)
                ·
                  refine ⟨6755273897918479207297363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9007031863891305609729817 6755273897918479207297363)
                  ·
                    refine ⟨10132910846877718810946045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6755273897918479207297363 10132910846877718810946045)
                    ·
                      refine ⟨3799841567579144554104767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10132910846877718810946045 3799841567579144554104767)
                      ·
                        rfl

theorem cell23_7400165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_7400165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400165 prefixEnd_7400165 := by exact prefixLift 7400165
  have htrace : WordTrace (prefixWord ++ tailWord_7400165) baseStart_7400165 baseEnd_7400165 := by
    simpa [prefixWord, tailWord_7400165, baseEnd_7400165] using wordTrace_append hprefix tailTrace_7400165
  have hstable : (prefixWord ++ tailWord_7400165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400165).length < 2 ^ (prefixWord ++ tailWord_7400165).sum := by decide
  have hdescent : baseEnd_7400165 < baseStart_7400165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400184 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_7400184 : Nat := 118140960795 + 7400184 * 2 ^ 59
def prefixEnd_7400184 : Nat := 4983230072969 + 3 ^ 40 * 7400184 * 2
def baseEnd_7400184 : Nat := 3799851323711579979767179

theorem tailTrace_7400184 : CollatzResearch.WordTrace tailWord_7400184 prefixEnd_7400184 3799851323711579979767179 := by
  unfold tailWord_7400184
  simp only [CollatzResearch.WordTrace]
  refine ⟨134953442111202346826003803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179937922814936462434671737 134953442111202346826003803)
  ·
    refine ⟨202430163166803520239005705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134953442111202346826003803 202430163166803520239005705)
    ·
      refine ⟨151822622375102640179254279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202430163166803520239005705 151822622375102640179254279)
      ·
        refine ⟨227733933562653960268881419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151822622375102640179254279 227733933562653960268881419)
        ·
          refine ⟨341600900343980940403322129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227733933562653960268881419 341600900343980940403322129)
          ·
            refine ⟨256200675257985705302491597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341600900343980940403322129 256200675257985705302491597)
            ·
              refine ⟨96075253221744639488434349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256200675257985705302491597 96075253221744639488434349)
              ·
                refine ⟨36028219958154239808162881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96075253221744639488434349 36028219958154239808162881)
                ·
                  refine ⟨27021164968615679856122161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36028219958154239808162881 27021164968615679856122161)
                  ·
                    refine ⟨20265873726461759892091621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27021164968615679856122161 20265873726461759892091621)
                    ·
                      refine ⟨3799851323711579979767179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20265873726461759892091621 3799851323711579979767179)
                      ·
                        rfl

theorem cell23_7400184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_7400184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400184 prefixEnd_7400184 := by exact prefixLift 7400184
  have htrace : WordTrace (prefixWord ++ tailWord_7400184) baseStart_7400184 baseEnd_7400184 := by
    simpa [prefixWord, tailWord_7400184, baseEnd_7400184] using wordTrace_append hprefix tailTrace_7400184
  have hstable : (prefixWord ++ tailWord_7400184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400184).length < 2 ^ (prefixWord ++ tailWord_7400184).sum := by decide
  have hdescent : baseEnd_7400184 < baseStart_7400184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400188 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 1, 4, 2]
def baseStart_7400188 : Nat := 118140960795 + 7400188 * 2 ^ 59
def prefixEnd_7400188 : Nat := 4983230072969 + 3 ^ 40 * 7400188 * 2
def baseEnd_7400188 : Nat := 3799853377634197964117161

theorem tailTrace_7400188 : CollatzResearch.WordTrace tailWord_7400188 prefixEnd_7400188 3799853377634197964117161 := by
  unfold tailWord_7400188
  simp only [CollatzResearch.WordTrace]
  refine ⟨134953515057195101167576609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179938020076260134890102145 134953515057195101167576609)
  ·
    refine ⟨101215136292896325875682457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134953515057195101167576609 101215136292896325875682457)
    ·
      refine ⟨75911352219672244406761843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101215136292896325875682457 75911352219672244406761843)
      ·
        refine ⟨113867028329508366610142765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75911352219672244406761843 113867028329508366610142765)
        ·
          refine ⟨42700135623565637478803537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113867028329508366610142765 42700135623565637478803537)
          ·
            refine ⟨32025101717674228109102653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42700135623565637478803537 32025101717674228109102653)
            ·
              refine ⟨12009413144127835540913495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32025101717674228109102653 12009413144127835540913495)
              ·
                refine ⟨18014119716191753311370243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12009413144127835540913495 18014119716191753311370243)
                ·
                  refine ⟨27021179574287629967055365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18014119716191753311370243 27021179574287629967055365)
                  ·
                    refine ⟨5066471170178930618822881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27021179574287629967055365 5066471170178930618822881)
                    ·
                      refine ⟨3799853377634197964117161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066471170178930618822881 3799853377634197964117161)
                      ·
                        rfl

theorem cell23_7400188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_7400188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400188 prefixEnd_7400188 := by exact prefixLift 7400188
  have htrace : WordTrace (prefixWord ++ tailWord_7400188) baseStart_7400188 baseEnd_7400188 := by
    simpa [prefixWord, tailWord_7400188, baseEnd_7400188] using wordTrace_append hprefix tailTrace_7400188
  have hstable : (prefixWord ++ tailWord_7400188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400188).length < 2 ^ (prefixWord ++ tailWord_7400188).sum := by decide
  have hdescent : baseEnd_7400188 < baseStart_7400188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400228 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 7]
def baseStart_7400228 : Nat := 118140960795 + 7400228 * 2 ^ 59
def prefixEnd_7400228 : Nat := 4983230072969 + 3 ^ 40 * 7400228 * 2
def baseEnd_7400228 : Nat := 422208212984486423068553

theorem tailTrace_7400228 : CollatzResearch.WordTrace tailWord_7400228 prefixEnd_7400228 422208212984486423068553 := by
  unfold tailWord_7400228
  simp only [CollatzResearch.WordTrace]
  refine ⟨134954244517122644583304669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179938992689496859444406225 134954244517122644583304669)
  ·
    refine ⟨50607841693920991718739251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134954244517122644583304669 50607841693920991718739251)
    ·
      refine ⟨75911762540881487578108877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50607841693920991718739251 75911762540881487578108877)
      ·
        refine ⟨28466910952830557841790829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75911762540881487578108877 28466910952830557841790829)
        ·
          refine ⟨10675091607311459190671561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28466910952830557841790829 10675091607311459190671561)
          ·
            refine ⟨8006318705483594393003671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10675091607311459190671561 8006318705483594393003671)
            ·
              refine ⟨12009478058225391589505507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8006318705483594393003671 12009478058225391589505507)
              ·
                refine ⟨18014217087338087384258261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12009478058225391589505507 18014217087338087384258261)
                ·
                  refine ⟨422208212984486423068553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18014217087338087384258261 422208212984486423068553)
                  ·
                    rfl

theorem cell23_7400228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_7400228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400228 prefixEnd_7400228 := by exact prefixLift 7400228
  have htrace : WordTrace (prefixWord ++ tailWord_7400228) baseStart_7400228 baseEnd_7400228 := by
    simpa [prefixWord, tailWord_7400228, baseEnd_7400228] using wordTrace_append hprefix tailTrace_7400228
  have hstable : (prefixWord ++ tailWord_7400228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400228).length < 2 ^ (prefixWord ++ tailWord_7400228).sum := by decide
  have hdescent : baseEnd_7400228 < baseStart_7400228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400261 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 3, 6, 2]
def baseStart_7400261 : Nat := 118140960795 + 7400261 * 2 ^ 59
def prefixEnd_7400261 : Nat := 4983230072969 + 3 ^ 40 * 7400261 * 2
def baseEnd_7400261 : Nat := 3799890861721976178504325

theorem tailTrace_7400261 : CollatzResearch.WordTrace tailWord_7400261 prefixEnd_7400261 3799890861721976178504325 := by
  unfold tailWord_7400261
  simp only [CollatzResearch.WordTrace]
  refine ⟨269909692643125735802560637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179939795095417157201707091 269909692643125735802560637)
  ·
    refine ⟨101216134741172150925960239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269909692643125735802560637 101216134741172150925960239)
    ·
      refine ⟨151824202111758226388940359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101216134741172150925960239 151824202111758226388940359)
      ·
        refine ⟨227736303167637339583410539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151824202111758226388940359 227736303167637339583410539)
        ·
          refine ⟨341604454751456009375115809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227736303167637339583410539 341604454751456009375115809)
          ·
            refine ⟨256203341063592007031336857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341604454751456009375115809 256203341063592007031336857)
            ·
              refine ⟨192152505797694005273502643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256203341063592007031336857 192152505797694005273502643)
              ·
                refine ⟨288228758696541007910253965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192152505797694005273502643 288228758696541007910253965)
                ·
                  refine ⟨108085784511202877966345237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288228758696541007910253965 108085784511202877966345237)
                  ·
                    refine ⟨5066521148962634904672433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108085784511202877966345237 5066521148962634904672433)
                    ·
                      refine ⟨3799890861721976178504325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066521148962634904672433 3799890861721976178504325)
                      ·
                        rfl

theorem cell23_7400261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 6, 2].length) (baseStart_7400261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400261 prefixEnd_7400261 := by exact prefixLift 7400261
  have htrace : WordTrace (prefixWord ++ tailWord_7400261) baseStart_7400261 baseEnd_7400261 := by
    simpa [prefixWord, tailWord_7400261, baseEnd_7400261] using wordTrace_append hprefix tailTrace_7400261
  have hstable : (prefixWord ++ tailWord_7400261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400261).length < 2 ^ (prefixWord ++ tailWord_7400261).sum := by decide
  have hdescent : baseEnd_7400261 < baseStart_7400261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400372 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_7400372 : Nat := 118140960795 + 7400372 * 2 ^ 59
def prefixEnd_7400372 : Nat := 4983230072969 + 3 ^ 40 * 7400372 * 2
def baseEnd_7400372 : Nat := 3799947858074625244216315

theorem tailTrace_7400372 : CollatzResearch.WordTrace tailWord_7400372 prefixEnd_7400372 3799947858074625244216315 := by
  unfold tailWord_7400372
  simp only [CollatzResearch.WordTrace]
  refine ⟨134956870572861800879925685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179942494097149067839900913 134956870572861800879925685)
  ·
    refine ⟨12652206616205793832493033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134956870572861800879925685 12652206616205793832493033)
    ·
      refine ⟨9489154962154345374369775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12652206616205793832493033 9489154962154345374369775)
      ·
        refine ⟨14233732443231518061554663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9489154962154345374369775 14233732443231518061554663)
        ·
          refine ⟨21350598664847277092331995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14233732443231518061554663 21350598664847277092331995)
          ·
            refine ⟨32025897997270915638497993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21350598664847277092331995 32025897997270915638497993)
            ·
              refine ⟨24019423497953186728873495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32025897997270915638497993 24019423497953186728873495)
              ·
                refine ⟨36029135246929780093310243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24019423497953186728873495 36029135246929780093310243)
                ·
                  refine ⟨54043702870394670139965365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36029135246929780093310243 54043702870394670139965365)
                  ·
                    refine ⟨5066597144099500325621753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54043702870394670139965365 5066597144099500325621753)
                    ·
                      refine ⟨3799947858074625244216315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066597144099500325621753 3799947858074625244216315)
                      ·
                        rfl

theorem cell23_7400372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_7400372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400372 prefixEnd_7400372 := by exact prefixLift 7400372
  have htrace : WordTrace (prefixWord ++ tailWord_7400372) baseStart_7400372 baseEnd_7400372 := by
    simpa [prefixWord, tailWord_7400372, baseEnd_7400372] using wordTrace_append hprefix tailTrace_7400372
  have hstable : (prefixWord ++ tailWord_7400372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400372).length < 2 ^ (prefixWord ++ tailWord_7400372).sum := by decide
  have hdescent : baseEnd_7400372 < baseStart_7400372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400390 : List Nat := [6, 1, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_7400390 : Nat := 118140960795 + 7400390 * 2 ^ 59
def prefixEnd_7400390 : Nat := 4983230072969 + 3 ^ 40 * 7400390 * 2
def baseEnd_7400390 : Nat := 1266652366908802057930411

theorem tailTrace_7400390 : CollatzResearch.WordTrace tailWord_7400390 prefixEnd_7400390 1266652366908802057930411 := by
  unfold tailWord_7400390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8434824926864324713562707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179942931773105593889337749 8434824926864324713562707)
  ·
    refine ⟨12652237390296487070344061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8434824926864324713562707 12652237390296487070344061)
    ·
      refine ⟨4744589021361182651379023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12652237390296487070344061 4744589021361182651379023)
      ·
        refine ⟨7116883532041773977068535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4744589021361182651379023 7116883532041773977068535)
        ·
          refine ⟨10675325298062660965602803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7116883532041773977068535 10675325298062660965602803)
          ·
            refine ⟨16012987947093991448404205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10675325298062660965602803 16012987947093991448404205)
            ·
              refine ⟨6004870480160246793151577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16012987947093991448404205 6004870480160246793151577)
              ·
                refine ⟨4503652860120185094863683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6004870480160246793151577 4503652860120185094863683)
                ·
                  refine ⟨6755479290180277642295525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503652860120185094863683 6755479290180277642295525)
                  ·
                    refine ⟨1266652366908802057930411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6755479290180277642295525 1266652366908802057930411)
                    ·
                      rfl

theorem cell23_7400390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_7400390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400390 prefixEnd_7400390 := by exact prefixLift 7400390
  have htrace : WordTrace (prefixWord ++ tailWord_7400390) baseStart_7400390 baseEnd_7400390 := by
    simpa [prefixWord, tailWord_7400390, baseEnd_7400390] using wordTrace_append hprefix tailTrace_7400390
  have hstable : (prefixWord ++ tailWord_7400390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400390).length < 2 ^ (prefixWord ++ tailWord_7400390).sum := by decide
  have hdescent : baseEnd_7400390 < baseStart_7400390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400458 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_7400458 : Nat := 118140960795 + 7400458 * 2 ^ 59
def prefixEnd_7400458 : Nat := 4983230072969 + 3 ^ 40 * 7400458 * 2
def baseEnd_7400458 : Nat := 3799992017410911907740919

theorem tailTrace_7400458 : CollatzResearch.WordTrace tailWord_7400458 prefixEnd_7400458 3799992017410911907740919 := by
  unfold tailWord_7400458
  simp only [CollatzResearch.WordTrace]
  refine ⟨67479219455853009611870507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179944585215608025631654685 67479219455853009611870507)
  ·
    refine ⟨101218829183779514417805761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67479219455853009611870507 101218829183779514417805761)
    ·
      refine ⟨75914121887834635813354321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101218829183779514417805761 75914121887834635813354321)
      ·
        refine ⟨56935591415875976860015741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75914121887834635813354321 56935591415875976860015741)
        ·
          refine ⟨21350846780953491322505903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56935591415875976860015741 21350846780953491322505903)
          ·
            refine ⟨32026270171430236983758855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21350846780953491322505903 32026270171430236983758855)
            ·
              refine ⟨48039405257145355475638283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32026270171430236983758855 48039405257145355475638283)
              ·
                refine ⟨72059107885718033213457425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48039405257145355475638283 72059107885718033213457425)
                ·
                  refine ⟨54044330914288524910093069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72059107885718033213457425 54044330914288524910093069)
                  ·
                    refine ⟨20266624092858196841284901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54044330914288524910093069 20266624092858196841284901)
                    ·
                      refine ⟨3799992017410911907740919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20266624092858196841284901 3799992017410911907740919)
                      ·
                        rfl

theorem cell23_7400458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_7400458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400458 prefixEnd_7400458 := by exact prefixLift 7400458
  have htrace : WordTrace (prefixWord ++ tailWord_7400458) baseStart_7400458 baseEnd_7400458 := by
    simpa [prefixWord, tailWord_7400458, baseEnd_7400458] using wordTrace_append hprefix tailTrace_7400458
  have hstable : (prefixWord ++ tailWord_7400458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400458).length < 2 ^ (prefixWord ++ tailWord_7400458).sum := by decide
  have hdescent : baseEnd_7400458 < baseStart_7400458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400509 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 2, 2, 2]
def baseStart_7400509 : Nat := 118140960795 + 7400509 * 2 ^ 59
def prefixEnd_7400509 : Nat := 4983230072969 + 3 ^ 40 * 7400509 * 2
def baseEnd_7400509 : Nat := 3800018204924291208203185

theorem tailTrace_7400509 : CollatzResearch.WordTrace tailWord_7400509 prefixEnd_7400509 3800018204924291208203185 := by
  unfold tailWord_7400509
  simp only [CollatzResearch.WordTrace]
  refine ⟨269918737946227274157588581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179945825297484849438392387 269918737946227274157588581)
  ·
    refine ⟨50609763364917613904547859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269918737946227274157588581 50609763364917613904547859)
    ·
      refine ⟨75914645047376420856821789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50609763364917613904547859 75914645047376420856821789)
      ·
        refine ⟨28467991892766157821308171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75914645047376420856821789 28467991892766157821308171)
        ·
          refine ⟨42701987839149236731962257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28467991892766157821308171 42701987839149236731962257)
          ·
            refine ⟨32026490879361927548971693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42701987839149236731962257 32026490879361927548971693)
            ·
              refine ⟨12009934079760722830864385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32026490879361927548971693 12009934079760722830864385)
              ·
                refine ⟨9007450559820542123148289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12009934079760722830864385 9007450559820542123148289)
                ·
                  refine ⟨6755587919865406592361217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9007450559820542123148289 6755587919865406592361217)
                  ·
                    refine ⟨5066690939899054944270913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6755587919865406592361217 5066690939899054944270913)
                    ·
                      refine ⟨3800018204924291208203185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066690939899054944270913 3800018204924291208203185)
                      ·
                        rfl

theorem cell23_7400509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_7400509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400509 prefixEnd_7400509 := by exact prefixLift 7400509
  have htrace : WordTrace (prefixWord ++ tailWord_7400509) baseStart_7400509 baseEnd_7400509 := by
    simpa [prefixWord, tailWord_7400509, baseEnd_7400509] using wordTrace_append hprefix tailTrace_7400509
  have hstable : (prefixWord ++ tailWord_7400509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400509).length < 2 ^ (prefixWord ++ tailWord_7400509).sum := by decide
  have hdescent : baseEnd_7400509 < baseStart_7400509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400602 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3]
def baseStart_7400602 : Nat := 118140960795 + 7400602 * 2 ^ 59
def prefixEnd_7400602 : Nat := 4983230072969 + 3 ^ 40 * 7400602 * 2
def baseEnd_7400602 : Nat := 3800065958625159344340257

theorem tailTrace_7400602 : CollatzResearch.WordTrace tailWord_7400602 prefixEnd_7400602 3800065958625159344340257 := by
  unfold tailWord_7400602
  simp only [CollatzResearch.WordTrace]
  refine ⟨67480532483722587760181015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179948086623260234027149373 67480532483722587760181015)
  ·
    refine ⟨101220798725583881640271523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67480532483722587760181015 101220798725583881640271523)
    ·
      refine ⟨151831198088375822460407285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101220798725583881640271523 151831198088375822460407285)
      ·
        refine ⟨14234174820785233355663183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151831198088375822460407285 14234174820785233355663183)
        ·
          refine ⟨21351262231177850033494775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14234174820785233355663183 21351262231177850033494775)
          ·
            refine ⟨32026893346766775050242163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21351262231177850033494775 32026893346766775050242163)
            ·
              refine ⟨48040340020150162575363245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32026893346766775050242163 48040340020150162575363245)
              ·
                refine ⟨18015127507556310965761217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48040340020150162575363245 18015127507556310965761217)
                ·
                  refine ⟨13511345630667233224320913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18015127507556310965761217 13511345630667233224320913)
                  ·
                    refine ⟨10133509223000424918240685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13511345630667233224320913 10133509223000424918240685)
                    ·
                      refine ⟨3800065958625159344340257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10133509223000424918240685 3800065958625159344340257)
                      ·
                        rfl

theorem cell23_7400602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_7400602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400602 prefixEnd_7400602 := by exact prefixLift 7400602
  have htrace : WordTrace (prefixWord ++ tailWord_7400602) baseStart_7400602 baseEnd_7400602 := by
    simpa [prefixWord, tailWord_7400602, baseEnd_7400602] using wordTrace_append hprefix tailTrace_7400602
  have hstable : (prefixWord ++ tailWord_7400602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400602).length < 2 ^ (prefixWord ++ tailWord_7400602).sum := by decide
  have hdescent : baseEnd_7400602 < baseStart_7400602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400626 : List Nat := [3, 2, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_7400626 : Nat := 118140960795 + 7400626 * 2 ^ 59
def prefixEnd_7400626 : Nat := 4983230072969 + 3 ^ 40 * 7400626 * 2
def baseEnd_7400626 : Nat := 1266692760720289083480049

theorem tailTrace_7400626 : CollatzResearch.WordTrace tailWord_7400626 prefixEnd_7400626 1266692760720289083480049 := by
  unfold tailWord_7400626
  simp only [CollatzResearch.WordTrace]
  refine ⟨67480751321700850784899433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179948670191202268759731821 67480751321700850784899433)
  ·
    refine ⟨50610563491275638088674575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67480751321700850784899433 50610563491275638088674575)
    ·
      refine ⟨75915845236913457133011863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50610563491275638088674575 75915845236913457133011863)
      ·
        refine ⟨113873767855370185699517795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75915845236913457133011863 113873767855370185699517795)
        ·
          refine ⟨170810651783055278549276693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113873767855370185699517795 170810651783055278549276693)
          ·
            refine ⟨8006749302330716181997345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170810651783055278549276693 8006749302330716181997345)
            ·
              refine ⟨6005061976748037136498009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8006749302330716181997345 6005061976748037136498009)
              ·
                refine ⟨4503796482561027852373507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005061976748037136498009 4503796482561027852373507)
                ·
                  refine ⟨6755694723841541778560261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503796482561027852373507 6755694723841541778560261)
                  ·
                    refine ⟨1266692760720289083480049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6755694723841541778560261 1266692760720289083480049)
                    ·
                      rfl

theorem cell23_7400626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_7400626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400626 prefixEnd_7400626 := by exact prefixLift 7400626
  have htrace : WordTrace (prefixWord ++ tailWord_7400626) baseStart_7400626 baseEnd_7400626 := by
    simpa [prefixWord, tailWord_7400626, baseEnd_7400626] using wordTrace_append hprefix tailTrace_7400626
  have hstable : (prefixWord ++ tailWord_7400626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400626).length < 2 ^ (prefixWord ++ tailWord_7400626).sum := by decide
  have hdescent : baseEnd_7400626 < baseStart_7400626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400653 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_7400653 : Nat := 118140960795 + 7400653 * 2 ^ 59
def prefixEnd_7400653 : Nat := 4983230072969 + 3 ^ 40 * 7400653 * 2
def baseEnd_7400653 : Nat := 3800092146138538644802523

theorem tailTrace_7400653 : CollatzResearch.WordTrace tailWord_7400653 prefixEnd_7400653 3800092146138538644802523 := by
  unfold tailWord_7400653
  simp only [CollatzResearch.WordTrace]
  refine ⟨269923990057705586750830613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179949326705137057833887075 269923990057705586750830613)
  ·
    refine ⟨12652687033954949378945185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 269923990057705586750830613 12652687033954949378945185)
    ·
      refine ⟨9489515275466212034208889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12652687033954949378945185 9489515275466212034208889)
      ·
        refine ⟨7117136456599659025656667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9489515275466212034208889 7117136456599659025656667)
        ·
          refine ⟨10675704684899488538485001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7117136456599659025656667 10675704684899488538485001)
          ·
            refine ⟨8006778513674616403863751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10675704684899488538485001 8006778513674616403863751)
            ·
              refine ⟨12010167770511924605795627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8006778513674616403863751 12010167770511924605795627)
              ·
                refine ⟨18015251655767886908693441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12010167770511924605795627 18015251655767886908693441)
                ·
                  refine ⟨13511438741825915181520081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18015251655767886908693441 13511438741825915181520081)
                  ·
                    refine ⟨10133579056369436386140061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13511438741825915181520081 10133579056369436386140061)
                    ·
                      refine ⟨3800092146138538644802523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10133579056369436386140061 3800092146138538644802523)
                      ·
                        rfl

theorem cell23_7400653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_7400653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400653 prefixEnd_7400653 := by exact prefixLift 7400653
  have htrace : WordTrace (prefixWord ++ tailWord_7400653) baseStart_7400653 baseEnd_7400653 := by
    simpa [prefixWord, tailWord_7400653, baseEnd_7400653] using wordTrace_append hprefix tailTrace_7400653
  have hstable : (prefixWord ++ tailWord_7400653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400653).length < 2 ^ (prefixWord ++ tailWord_7400653).sum := by decide
  have hdescent : baseEnd_7400653 < baseStart_7400653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400655 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 1, 8, 2]
def baseStart_7400655 : Nat := 118140960795 + 7400655 * 2 ^ 59
def prefixEnd_7400655 : Nat := 4983230072969 + 3 ^ 40 * 7400655 * 2
def baseEnd_7400655 : Nat := 3800093173099847636977513

theorem tailTrace_7400655 : CollatzResearch.WordTrace tailWord_7400655 prefixEnd_7400655 3800093173099847636977513 := by
  unfold tailWord_7400655
  simp only [CollatzResearch.WordTrace]
  refine ⟨269924063003698341092403419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179949375335798894061602279 269924063003698341092403419)
  ·
    refine ⟨404886094505547511638605129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269924063003698341092403419 404886094505547511638605129)
    ·
      refine ⟨303664570879160633728953847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404886094505547511638605129 303664570879160633728953847)
      ·
        refine ⟨455496856318740950593430771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303664570879160633728953847 455496856318740950593430771)
        ·
          refine ⟨683245284478111425890146157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455496856318740950593430771 683245284478111425890146157)
          ·
            refine ⟨256216981679291784708804809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 683245284478111425890146157 256216981679291784708804809)
            ·
              refine ⟨192162736259468838531603607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256216981679291784708804809 192162736259468838531603607)
              ·
                refine ⟨288244104389203257797405411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192162736259468838531603607 288244104389203257797405411)
                ·
                  refine ⟨432366156583804886696108117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288244104389203257797405411 432366156583804886696108117)
                  ·
                    refine ⟨5066790897466463515970017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 432366156583804886696108117 5066790897466463515970017)
                    ·
                      refine ⟨3800093173099847636977513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5066790897466463515970017 3800093173099847636977513)
                      ·
                        rfl

theorem cell23_7400655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 8, 2].length) (baseStart_7400655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400655 prefixEnd_7400655 := by exact prefixLift 7400655
  have htrace : WordTrace (prefixWord ++ tailWord_7400655) baseStart_7400655 baseEnd_7400655 := by
    simpa [prefixWord, tailWord_7400655, baseEnd_7400655] using wordTrace_append hprefix tailTrace_7400655
  have hstable : (prefixWord ++ tailWord_7400655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400655).length < 2 ^ (prefixWord ++ tailWord_7400655).sum := by decide
  have hdescent : baseEnd_7400655 < baseStart_7400655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400665 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 4, 4]
def baseStart_7400665 : Nat := 118140960795 + 7400665 * 2 ^ 59
def prefixEnd_7400665 : Nat := 4983230072969 + 3 ^ 40 * 7400665 * 2
def baseEnd_7400665 : Nat := 1266699435968797532617489

theorem tailTrace_7400665 : CollatzResearch.WordTrace tailWord_7400665 prefixEnd_7400665 1266699435968797532617489 := by
  unfold tailWord_7400665
  simp only [CollatzResearch.WordTrace]
  refine ⟨269924427733662112800267449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179949618489108075200178299 269924427733662112800267449)
  ·
    refine ⟨202443320800246584600200587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269924427733662112800267449 202443320800246584600200587)
    ·
      refine ⟨303664981200369876900300881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202443320800246584600200587 303664981200369876900300881)
      ·
        refine ⟨227748735900277407675225661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303664981200369876900300881 227748735900277407675225661)
        ·
          refine ⟨85405775962604027878209623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227748735900277407675225661 85405775962604027878209623)
          ·
            refine ⟨128108663943906041817314435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85405775962604027878209623 128108663943906041817314435)
            ·
              refine ⟨192162995915859062725971653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128108663943906041817314435 192162995915859062725971653)
              ·
                refine ⟨36030561734223574261119685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192162995915859062725971653 36030561734223574261119685)
                ·
                  refine ⟨6755730325166920173959941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36030561734223574261119685 6755730325166920173959941)
                  ·
                    refine ⟨1266699435968797532617489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6755730325166920173959941 1266699435968797532617489)
                    ·
                      rfl

theorem cell23_7400665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 4].length) (baseStart_7400665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400665 prefixEnd_7400665 := by exact prefixLift 7400665
  have htrace : WordTrace (prefixWord ++ tailWord_7400665) baseStart_7400665 baseEnd_7400665 := by
    simpa [prefixWord, tailWord_7400665, baseEnd_7400665] using wordTrace_append hprefix tailTrace_7400665
  have hstable : (prefixWord ++ tailWord_7400665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400665).length < 2 ^ (prefixWord ++ tailWord_7400665).sum := by decide
  have hdescent : baseEnd_7400665 < baseStart_7400665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400669 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_7400669 : Nat := 118140960795 + 7400669 * 2 ^ 59
def prefixEnd_7400669 : Nat := 4983230072969 + 3 ^ 40 * 7400669 * 2
def baseEnd_7400669 : Nat := 1266700120609670194067483

theorem tailTrace_7400669 : CollatzResearch.WordTrace tailWord_7400669 prefixEnd_7400669 1266700120609670194067483 := by
  unfold tailWord_7400669
  simp only [CollatzResearch.WordTrace]
  refine ⟨269924573625647621483413061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179949715750431747655608707 269924573625647621483413061)
  ·
    refine ⟨50610857554808929028139949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269924573625647621483413061 50610857554808929028139949)
    ·
      refine ⟨18979071583053348385552481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50610857554808929028139949 18979071583053348385552481)
      ·
        refine ⟨14234303687290011289164361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18979071583053348385552481 14234303687290011289164361)
        ·
          refine ⟨10675727765467508466873271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14234303687290011289164361 10675727765467508466873271)
          ·
            refine ⟨16013591648201262700309907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10675727765467508466873271 16013591648201262700309907)
            ·
              refine ⟨24020387472301894050464861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16013591648201262700309907 24020387472301894050464861)
              ·
                refine ⟨9007645302113210268924323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24020387472301894050464861 9007645302113210268924323)
                ·
                  refine ⟨13511467953169815403386485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9007645302113210268924323 13511467953169815403386485)
                  ·
                    refine ⟨1266700120609670194067483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13511467953169815403386485 1266700120609670194067483)
                    ·
                      rfl

theorem cell23_7400669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_7400669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400669 prefixEnd_7400669 := by exact prefixLift 7400669
  have htrace : WordTrace (prefixWord ++ tailWord_7400669) baseStart_7400669 baseEnd_7400669 := by
    simpa [prefixWord, tailWord_7400669, baseEnd_7400669] using wordTrace_append hprefix tailTrace_7400669
  have hstable : (prefixWord ++ tailWord_7400669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400669).length < 2 ^ (prefixWord ++ tailWord_7400669).sum := by decide
  have hdescent : baseEnd_7400669 < baseStart_7400669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400672 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 4]
def baseStart_7400672 : Nat := 118140960795 + 7400672 * 2 ^ 59
def prefixEnd_7400672 : Nat := 4983230072969 + 3 ^ 40 * 7400672 * 2
def baseEnd_7400672 : Nat := 3800101902270974070464935

theorem tailTrace_7400672 : CollatzResearch.WordTrace tailWord_7400672 prefixEnd_7400672 3800101902270974070464935 := by
  unfold tailWord_7400672
  simp only [CollatzResearch.WordTrace]
  refine ⟨134962341522318376497886135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179949788696424501997181513 134962341522318376497886135)
  ·
    refine ⟨202443512283477564746829203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134962341522318376497886135 202443512283477564746829203)
    ·
      refine ⟨303665268425216347120243805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202443512283477564746829203 303665268425216347120243805)
      ·
        refine ⟨113874475659456130170091427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303665268425216347120243805 113874475659456130170091427)
        ·
          refine ⟨170811713489184195255137141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113874475659456130170091427 170811713489184195255137141)
          ·
            refine ⟨16013598139611018305169107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170811713489184195255137141 16013598139611018305169107)
            ·
              refine ⟨24020397209416527457753661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16013598139611018305169107 24020397209416527457753661)
              ·
                refine ⟨9007648953531197796657623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24020397209416527457753661 9007648953531197796657623)
                ·
                  refine ⟨13511473430296796694986435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9007648953531197796657623 13511473430296796694986435)
                  ·
                    refine ⟨20267210145445195042479653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13511473430296796694986435 20267210145445195042479653)
                    ·
                      refine ⟨3800101902270974070464935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20267210145445195042479653 3800101902270974070464935)
                      ·
                        rfl

theorem cell23_7400672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_7400672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400672 prefixEnd_7400672 := by exact prefixLift 7400672
  have htrace : WordTrace (prefixWord ++ tailWord_7400672) baseStart_7400672 baseEnd_7400672 := by
    simpa [prefixWord, tailWord_7400672, baseEnd_7400672] using wordTrace_append hprefix tailTrace_7400672
  have hstable : (prefixWord ++ tailWord_7400672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400672).length < 2 ^ (prefixWord ++ tailWord_7400672).sum := by decide
  have hdescent : baseEnd_7400672 < baseStart_7400672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400682 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 4, 4]
def baseStart_7400682 : Nat := 118140960795 + 7400682 * 2 ^ 59
def prefixEnd_7400682 : Nat := 4983230072969 + 3 ^ 40 * 7400682 * 2
def baseEnd_7400682 : Nat := 1266702345692506343779963

theorem tailTrace_7400682 : CollatzResearch.WordTrace tailWord_7400682 prefixEnd_7400682 1266702345692506343779963 := by
  unfold tailWord_7400682
  simp only [CollatzResearch.WordTrace]
  refine ⟨67481261943650131175909075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179950031849733683135757533 67481261943650131175909075)
  ·
    refine ⟨101221892915475196763863613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67481261943650131175909075 101221892915475196763863613)
    ·
      refine ⟨37958209843303198786448855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101221892915475196763863613 37958209843303198786448855)
      ·
        refine ⟨56937314764954798179673283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37958209843303198786448855 56937314764954798179673283)
        ·
          refine ⟨85405972147432197269509925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56937314764954798179673283 85405972147432197269509925)
          ·
            refine ⟨16013619777643536988033111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85405972147432197269509925 16013619777643536988033111)
            ·
              refine ⟨24020429666465305482049667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16013619777643536988033111 24020429666465305482049667)
              ·
                refine ⟨36030644499697958223074501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24020429666465305482049667 36030644499697958223074501)
                ·
                  refine ⟨6755745843693367166826469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36030644499697958223074501 6755745843693367166826469)
                  ·
                    refine ⟨1266702345692506343779963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6755745843693367166826469 1266702345692506343779963)
                    ·
                      rfl

theorem cell23_7400682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_7400682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400682 prefixEnd_7400682 := by exact prefixLift 7400682
  have htrace : WordTrace (prefixWord ++ tailWord_7400682) baseStart_7400682 baseEnd_7400682 := by
    simpa [prefixWord, tailWord_7400682, baseEnd_7400682] using wordTrace_append hprefix tailTrace_7400682
  have hstable : (prefixWord ++ tailWord_7400682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400682).length < 2 ^ (prefixWord ++ tailWord_7400682).sum := by decide
  have hdescent : baseEnd_7400682 < baseStart_7400682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400688 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_7400688 : Nat := 118140960795 + 7400688 * 2 ^ 59
def prefixEnd_7400688 : Nat := 4983230072969 + 3 ^ 40 * 7400688 * 2
def baseEnd_7400688 : Nat := 3800110117961446007864861

theorem tailTrace_7400688 : CollatzResearch.WordTrace tailWord_7400688 prefixEnd_7400688 3800110117961446007864861 := by
  unfold tailWord_7400688
  simp only [CollatzResearch.WordTrace]
  refine ⟨134962633306289393864177359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179950177741719191818903145 134962633306289393864177359)
  ·
    refine ⟨202443949959434090796266039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134962633306289393864177359 202443949959434090796266039)
    ·
      refine ⟨303665924939151136194399059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202443949959434090796266039 303665924939151136194399059)
      ·
        refine ⟨455498887408726704291598589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303665924939151136194399059 455498887408726704291598589)
        ·
          refine ⟨170812082778272514109349471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455498887408726704291598589 170812082778272514109349471)
          ·
            refine ⟨256218124167408771164024207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170812082778272514109349471 256218124167408771164024207)
            ·
              refine ⟨384327186251113156746036311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256218124167408771164024207 384327186251113156746036311)
              ·
                refine ⟨576490779376669735119054467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384327186251113156746036311 576490779376669735119054467)
                ·
                  refine ⟨864736169065004602678581701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576490779376669735119054467 864736169065004602678581701)
                  ·
                    refine ⟨162138031699688363002234069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 864736169065004602678581701 162138031699688363002234069)
                    ·
                      refine ⟨3800110117961446007864861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162138031699688363002234069 3800110117961446007864861)
                      ·
                        rfl

theorem cell23_7400688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_7400688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400688 prefixEnd_7400688 := by exact prefixLift 7400688
  have htrace : WordTrace (prefixWord ++ tailWord_7400688) baseStart_7400688 baseEnd_7400688 := by
    simpa [prefixWord, tailWord_7400688, baseEnd_7400688] using wordTrace_append hprefix tailTrace_7400688
  have hstable : (prefixWord ++ tailWord_7400688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400688).length < 2 ^ (prefixWord ++ tailWord_7400688).sum := by decide
  have hdescent : baseEnd_7400688 < baseStart_7400688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400702 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_7400702 : Nat := 118140960795 + 7400702 * 2 ^ 59
def prefixEnd_7400702 : Nat := 4983230072969 + 3 ^ 40 * 7400702 * 2
def baseEnd_7400702 : Nat := 3800117306690608953089797

theorem tailTrace_7400702 : CollatzResearch.WordTrace tailWord_7400702 prefixEnd_7400702 3800117306690608953089797 := by
  unfold tailWord_7400702
  simp only [CollatzResearch.WordTrace]
  refine ⟨33740722154316008514920545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179950518156352045412909573 33740722154316008514920545)
  ·
    refine ⟨25305541615737006386190409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33740722154316008514920545 25305541615737006386190409)
    ·
      refine ⟨18979156211802754789642807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25305541615737006386190409 18979156211802754789642807)
      ·
        refine ⟨28468734317704132184464211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18979156211802754789642807 28468734317704132184464211)
        ·
          refine ⟨42703101476556198276696317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28468734317704132184464211 42703101476556198276696317)
          ·
            refine ⟨16013663053708574353761119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42703101476556198276696317 16013663053708574353761119)
            ·
              refine ⟨24020494580562861530641679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16013663053708574353761119 24020494580562861530641679)
              ·
                refine ⟨36030741870844292295962519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24020494580562861530641679 36030741870844292295962519)
                ·
                  refine ⟨54046112806266438443943779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36030741870844292295962519 54046112806266438443943779)
                  ·
                    refine ⟨81069169209399657665915669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54046112806266438443943779 81069169209399657665915669)
                    ·
                      refine ⟨3800117306690608953089797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81069169209399657665915669 3800117306690608953089797)
                      ·
                        rfl

theorem cell23_7400702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_7400702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400702 prefixEnd_7400702 := by exact prefixLift 7400702
  have htrace : WordTrace (prefixWord ++ tailWord_7400702) baseStart_7400702 baseEnd_7400702 := by
    simpa [prefixWord, tailWord_7400702, baseEnd_7400702] using wordTrace_append hprefix tailTrace_7400702
  have hstable : (prefixWord ++ tailWord_7400702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400702).length < 2 ^ (prefixWord ++ tailWord_7400702).sum := by decide
  have hdescent : baseEnd_7400702 < baseStart_7400702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400706 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_7400706 : Nat := 118140960795 + 7400706 * 2 ^ 59
def prefixEnd_7400706 : Nat := 4983230072969 + 3 ^ 40 * 7400706 * 2
def baseEnd_7400706 : Nat := 3800119360613226937439779

theorem tailTrace_7400706 : CollatzResearch.WordTrace tailWord_7400706 prefixEnd_7400706 3800119360613226937439779 := by
  unfold tailWord_7400706
  simp only [CollatzResearch.WordTrace]
  refine ⟨67481480781628394200627493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179950615417675717868339981 67481480781628394200627493)
  ·
    refine ⟨12652777646555323912617655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67481480781628394200627493 12652777646555323912617655)
    ·
      refine ⟨18979166469832985868926483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12652777646555323912617655 18979166469832985868926483)
      ·
        refine ⟨28468749704749478803389725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18979166469832985868926483 28468749704749478803389725)
        ·
          refine ⟨10675781139281054551271147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28468749704749478803389725 10675781139281054551271147)
          ·
            refine ⟨16013671708921581826906721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10675781139281054551271147 16013671708921581826906721)
            ·
              refine ⟨12010253781691186370180041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16013671708921581826906721 12010253781691186370180041)
              ·
                refine ⟨9007690336268389777635031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12010253781691186370180041 9007690336268389777635031)
                ·
                  refine ⟨13511535504402584666452547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9007690336268389777635031 13511535504402584666452547)
                  ·
                    refine ⟨20267303256603876999678821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13511535504402584666452547 20267303256603876999678821)
                    ·
                      refine ⟨3800119360613226937439779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20267303256603876999678821 3800119360613226937439779)
                      ·
                        rfl

theorem cell23_7400706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_7400706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400706 prefixEnd_7400706 := by exact prefixLift 7400706
  have htrace : WordTrace (prefixWord ++ tailWord_7400706) baseStart_7400706 baseEnd_7400706 := by
    simpa [prefixWord, tailWord_7400706, baseEnd_7400706] using wordTrace_append hprefix tailTrace_7400706
  have hstable : (prefixWord ++ tailWord_7400706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400706).length < 2 ^ (prefixWord ++ tailWord_7400706).sum := by decide
  have hdescent : baseEnd_7400706 < baseStart_7400706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400756 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_7400756 : Nat := 118140960795 + 7400756 * 2 ^ 59
def prefixEnd_7400756 : Nat := 4983230072969 + 3 ^ 40 * 7400756 * 2
def baseEnd_7400756 : Nat := 3800145034645951741814549

theorem tailTrace_7400756 : CollatzResearch.WordTrace tailWord_7400756 prefixEnd_7400756 3800145034645951741814549 := by
  unfold tailWord_7400756
  simp only [CollatzResearch.WordTrace]
  refine ⟨134963873388166217670915061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179951831184221623561220081 134963873388166217670915061)
  ·
    refine ⟨12652863130140582906648287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134963873388166217670915061 12652863130140582906648287)
    ·
      refine ⟨18979294695210874359972431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12652863130140582906648287 18979294695210874359972431)
      ·
        refine ⟨28468942042816311539958647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18979294695210874359972431 28468942042816311539958647)
        ·
          refine ⟨42703413064224467309937971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28468942042816311539958647 42703413064224467309937971)
          ·
            refine ⟨64055119596336700964906957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42703413064224467309937971 64055119596336700964906957)
            ·
              refine ⟨24020669848626262861840109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64055119596336700964906957 24020669848626262861840109)
              ·
                refine ⟨9007751193234848573190041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24020669848626262861840109 9007751193234848573190041)
                ·
                  refine ⟨6755813394926136429892531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9007751193234848573190041 6755813394926136429892531)
                  ·
                    refine ⟨10133720092389204644838797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6755813394926136429892531 10133720092389204644838797)
                    ·
                      refine ⟨3800145034645951741814549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10133720092389204644838797 3800145034645951741814549)
                      ·
                        rfl

theorem cell23_7400756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_7400756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400756 prefixEnd_7400756 := by exact prefixLift 7400756
  have htrace : WordTrace (prefixWord ++ tailWord_7400756) baseStart_7400756 baseEnd_7400756 := by
    simpa [prefixWord, tailWord_7400756, baseEnd_7400756] using wordTrace_append hprefix tailTrace_7400756
  have hstable : (prefixWord ++ tailWord_7400756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400756).length < 2 ^ (prefixWord ++ tailWord_7400756).sum := by decide
  have hdescent : baseEnd_7400756 < baseStart_7400756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400802 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 7]
def baseStart_7400802 : Nat := 118140960795 + 7400802 * 2 ^ 59
def prefixEnd_7400802 : Nat := 4983230072969 + 3 ^ 40 * 7400802 * 2
def baseEnd_7400802 : Nat := 422240961639562062426593

theorem tailTrace_7400802 : CollatzResearch.WordTrace tailWord_7400802 prefixEnd_7400802 422240961639562062426593 := by
  unfold tailWord_7400802
  simp only [CollatzResearch.WordTrace]
  refine ⟨67482356133541446299501165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179952949689443856798669773 67482356133541446299501165)
  ·
    refine ⟨25305883550078042362312937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67482356133541446299501165 25305883550078042362312937)
    ·
      refine ⟨18979412662558531771734703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25305883550078042362312937 18979412662558531771734703)
      ·
        refine ⟨28469118993837797657602055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18979412662558531771734703 28469118993837797657602055)
        ·
          refine ⟨42703678490756696486403083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28469118993837797657602055 42703678490756696486403083)
          ·
            refine ⟨64055517736135044729604625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42703678490756696486403083 64055517736135044729604625)
            ·
              refine ⟨48041638302101283547203469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64055517736135044729604625 48041638302101283547203469)
              ·
                refine ⟨18015614363287981330201301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48041638302101283547203469 18015614363287981330201301)
                ·
                  refine ⟨422240961639562062426593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18015614363287981330201301 422240961639562062426593)
                  ·
                    rfl

theorem cell23_7400802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_7400802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400802 prefixEnd_7400802 := by exact prefixLift 7400802
  have htrace : WordTrace (prefixWord ++ tailWord_7400802) baseStart_7400802 baseEnd_7400802 := by
    simpa [prefixWord, tailWord_7400802, baseEnd_7400802] using wordTrace_append hprefix tailTrace_7400802
  have hstable : (prefixWord ++ tailWord_7400802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400802).length < 2 ^ (prefixWord ++ tailWord_7400802).sum := by decide
  have hdescent : baseEnd_7400802 < baseStart_7400802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400812 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 3]
def baseStart_7400812 : Nat := 118140960795 + 7400812 * 2 ^ 59
def prefixEnd_7400812 : Nat := 4983230072969 + 3 ^ 40 * 7400812 * 2
def baseEnd_7400812 : Nat := 3800173789562603522714291

theorem tailTrace_7400812 : CollatzResearch.WordTrace tailWord_7400812 prefixEnd_7400812 3800173789562603522714291 := by
  unfold tailWord_7400812
  simp only [CollatzResearch.WordTrace]
  refine ⟨134964894632064778452934345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179953192842753037937245793 134964894632064778452934345)
  ·
    refine ⟨101223670974048583839700759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134964894632064778452934345 101223670974048583839700759)
    ·
      refine ⟨151835506461072875759551139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101223670974048583839700759 151835506461072875759551139)
      ·
        refine ⟨227753259691609313639326709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151835506461072875759551139 227753259691609313639326709)
        ·
          refine ⟨21351868096088373153686879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227753259691609313639326709 21351868096088373153686879)
          ·
            refine ⟨32027802144132559730530319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21351868096088373153686879 32027802144132559730530319)
            ·
              refine ⟨48041703216198839595795479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32027802144132559730530319 48041703216198839595795479)
              ·
                refine ⟨72062554824298259393693219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48041703216198839595795479 72062554824298259393693219)
                ·
                  refine ⟨108093832236447389090539829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72062554824298259393693219 108093832236447389090539829)
                  ·
                    refine ⟨10133796772166942727238109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108093832236447389090539829 10133796772166942727238109)
                    ·
                      refine ⟨3800173789562603522714291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10133796772166942727238109 3800173789562603522714291)
                      ·
                        rfl

theorem cell23_7400812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_7400812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400812 prefixEnd_7400812 := by exact prefixLift 7400812
  have htrace : WordTrace (prefixWord ++ tailWord_7400812) baseStart_7400812 baseEnd_7400812 := by
    simpa [prefixWord, tailWord_7400812, baseEnd_7400812] using wordTrace_append hprefix tailTrace_7400812
  have hstable : (prefixWord ++ tailWord_7400812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400812).length < 2 ^ (prefixWord ++ tailWord_7400812).sum := by decide
  have hdescent : baseEnd_7400812 < baseStart_7400812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400815 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 1, 7]
def baseStart_7400815 : Nat := 118140960795 + 7400815 * 2 ^ 59
def prefixEnd_7400815 : Nat := 4983230072969 + 3 ^ 40 * 7400815 * 2
def baseEnd_7400815 : Nat := 1266725110001522336992259

theorem tailTrace_7400815 : CollatzResearch.WordTrace tailWord_7400815 prefixEnd_7400815 1266725110001522336992259 := by
  unfold tailWord_7400815
  simp only [CollatzResearch.WordTrace]
  refine ⟨269929898683118688418227899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179953265788745792278818599 269929898683118688418227899)
  ·
    refine ⟨404894848024678032627341849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269929898683118688418227899 404894848024678032627341849)
    ·
      refine ⟨303671136018508524470506387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404894848024678032627341849 303671136018508524470506387)
      ·
        refine ⟨455506704027762786705759581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303671136018508524470506387 455506704027762786705759581)
        ·
          refine ⟨170815014010411045014659843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455506704027762786705759581 170815014010411045014659843)
          ·
            refine ⟨256222521015616567521989765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170815014010411045014659843 256222521015616567521989765)
            ·
              refine ⟨48041722690428106410373081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256222521015616567521989765 48041722690428106410373081)
              ·
                refine ⟨36031292017821079807779811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48041722690428106410373081 36031292017821079807779811)
                ·
                  refine ⟨54046938026731619711669717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36031292017821079807779811 54046938026731619711669717)
                  ·
                    refine ⟨1266725110001522336992259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54046938026731619711669717 1266725110001522336992259)
                    ·
                      rfl

theorem cell23_7400815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_7400815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400815 prefixEnd_7400815 := by exact prefixLift 7400815
  have htrace : WordTrace (prefixWord ++ tailWord_7400815) baseStart_7400815 baseEnd_7400815 := by
    simpa [prefixWord, tailWord_7400815, baseEnd_7400815] using wordTrace_append hprefix tailTrace_7400815
  have hstable : (prefixWord ++ tailWord_7400815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400815).length < 2 ^ (prefixWord ++ tailWord_7400815).sum := by decide
  have hdescent : baseEnd_7400815 < baseStart_7400815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400825 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_7400825 : Nat := 118140960795 + 7400825 * 2 ^ 59
def prefixEnd_7400825 : Nat := 4983230072969 + 3 ^ 40 * 7400825 * 2
def baseEnd_7400825 : Nat := 3800180464811111971851731

theorem tailTrace_7400825 : CollatzResearch.WordTrace tailWord_7400825 prefixEnd_7400825 3800180464811111971851731 := by
  unfold tailWord_7400825
  simp only [CollatzResearch.WordTrace]
  refine ⟨269930263413082460126091929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179953508942054973417394619 269930263413082460126091929)
  ·
    refine ⟨202447697559811845094568947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269930263413082460126091929 202447697559811845094568947)
    ·
      refine ⟨303671546339717767641853421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202447697559811845094568947 303671546339717767641853421)
      ·
        refine ⟨113876829877394162865695033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303671546339717767641853421 113876829877394162865695033)
        ·
          refine ⟨85407622408045622149271275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113876829877394162865695033 85407622408045622149271275)
          ·
            refine ⟨128111433612068433223906913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85407622408045622149271275 128111433612068433223906913)
            ·
              refine ⟨96083575209051324917930185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128111433612068433223906913 96083575209051324917930185)
              ·
                refine ⟨72062681406788493688447639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96083575209051324917930185 72062681406788493688447639)
                ·
                  refine ⟨108094022110182740532671459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72062681406788493688447639 108094022110182740532671459)
                  ·
                    refine ⟨162141033165274110799007189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108094022110182740532671459 162141033165274110799007189)
                    ·
                      refine ⟨3800180464811111971851731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162141033165274110799007189 3800180464811111971851731)
                      ·
                        rfl

theorem cell23_7400825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_7400825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400825 prefixEnd_7400825 := by exact prefixLift 7400825
  have htrace : WordTrace (prefixWord ++ tailWord_7400825) baseStart_7400825 baseEnd_7400825 := by
    simpa [prefixWord, tailWord_7400825, baseEnd_7400825] using wordTrace_append hprefix tailTrace_7400825
  have hstable : (prefixWord ++ tailWord_7400825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400825).length < 2 ^ (prefixWord ++ tailWord_7400825).sum := by decide
  have hdescent : baseEnd_7400825 < baseStart_7400825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400896 : List Nat := [2, 1, 1, 2, 3, 1, 5, 3, 1, 4]
def baseStart_7400896 : Nat := 118140960795 + 7400896 * 2 ^ 59
def prefixEnd_7400896 : Nat := 4983230072969 + 3 ^ 40 * 7400896 * 2
def baseEnd_7400896 : Nat := 1266738973979193731354635

theorem tailTrace_7400896 : CollatzResearch.WordTrace tailWord_7400896 prefixEnd_7400896 1266738973979193731354635 := by
  unfold tailWord_7400896
  simp only [CollatzResearch.WordTrace]
  refine ⟨134966426497912619625963271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179955235330550159501284361 134966426497912619625963271)
  ·
    refine ⟨202449639746868929438944907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134966426497912619625963271 202449639746868929438944907)
    ·
      refine ⟨303674459620303394158417361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202449639746868929438944907 303674459620303394158417361)
      ·
        refine ⟨227755844715227545618813021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303674459620303394158417361 227755844715227545618813021)
        ·
          refine ⟨85408441768210329607054883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227755844715227545618813021 85408441768210329607054883)
          ·
            refine ⟨128112662652315494410582325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85408441768210329607054883 128112662652315494410582325)
            ·
              refine ⟨12010562123654577600992093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128112662652315494410582325 12010562123654577600992093)
              ·
                refine ⟨4503960796370466600372035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12010562123654577600992093 4503960796370466600372035)
                ·
                  refine ⟨6755941194555699900558053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503960796370466600372035 6755941194555699900558053)
                  ·
                    refine ⟨1266738973979193731354635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6755941194555699900558053 1266738973979193731354635)
                    ·
                      rfl

theorem cell23_7400896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 1, 4].length) (baseStart_7400896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400896 prefixEnd_7400896 := by exact prefixLift 7400896
  have htrace : WordTrace (prefixWord ++ tailWord_7400896) baseStart_7400896 baseEnd_7400896 := by
    simpa [prefixWord, tailWord_7400896, baseEnd_7400896] using wordTrace_append hprefix tailTrace_7400896
  have hstable : (prefixWord ++ tailWord_7400896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400896).length < 2 ^ (prefixWord ++ tailWord_7400896).sum := by decide
  have hdescent : baseEnd_7400896 < baseStart_7400896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400952 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 3, 6]
def baseStart_7400952 : Nat := 118140960795 + 7400952 * 2 ^ 59
def prefixEnd_7400952 : Nat := 4983230072969 + 3 ^ 40 * 7400952 * 2
def baseEnd_7400952 : Nat := 1266748558951410991654549

theorem tailTrace_7400952 : CollatzResearch.WordTrace tailWord_7400952 prefixEnd_7400952 1266748558951410991654549 := by
  unfold tailWord_7400952
  simp only [CollatzResearch.WordTrace]
  refine ⟨134967447741811180407982555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179956596989081573877310073 134967447741811180407982555)
  ·
    refine ⟨202451171612716770611973833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134967447741811180407982555 202451171612716770611973833)
    ·
      refine ⟨151838378709537577958980375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202451171612716770611973833 151838378709537577958980375)
      ·
        refine ⟨227757568064306366938470563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151838378709537577958980375 227757568064306366938470563)
        ·
          refine ⟨341636352096459550407705845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227757568064306366938470563 341636352096459550407705845)
          ·
            refine ⟨32028408009043082850722423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 341636352096459550407705845 32028408009043082850722423)
            ·
              refine ⟨48042612013564624276083635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32028408009043082850722423 48042612013564624276083635)
              ·
                refine ⟨72063918020346936414125453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48042612013564624276083635 72063918020346936414125453)
                ·
                  refine ⟨27023969257630101155297045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72063918020346936414125453 27023969257630101155297045)
                  ·
                    refine ⟨1266748558951410991654549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27023969257630101155297045 1266748558951410991654549)
                    ·
                      rfl

theorem cell23_7400952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_7400952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400952 prefixEnd_7400952 := by exact prefixLift 7400952
  have htrace : WordTrace (prefixWord ++ tailWord_7400952) baseStart_7400952 baseEnd_7400952 := by
    simpa [prefixWord, tailWord_7400952, baseEnd_7400952] using wordTrace_append hprefix tailTrace_7400952
  have hstable : (prefixWord ++ tailWord_7400952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400952).length < 2 ^ (prefixWord ++ tailWord_7400952).sum := by decide
  have hdescent : baseEnd_7400952 < baseStart_7400952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400970 : List Nat := [3, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3]
def baseStart_7400970 : Nat := 118140960795 + 7400970 * 2 ^ 59
def prefixEnd_7400970 : Nat := 4983230072969 + 3 ^ 40 * 7400970 * 2
def baseEnd_7400970 : Nat := 3800254919506013904538565

theorem tailTrace_7400970 : CollatzResearch.WordTrace tailWord_7400970 prefixEnd_7400970 3800254919506013904538565 := by
  unfold tailWord_7400970
  simp only [CollatzResearch.WordTrace]
  refine ⟨67483887999389287472530091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179957034665038099926746909 67483887999389287472530091)
  ·
    refine ⟨101225831999083931208795137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67483887999389287472530091 101225831999083931208795137)
    ·
      refine ⟨75919373999312948406596353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101225831999083931208795137 75919373999312948406596353)
      ·
        refine ⟨56939530499484711304947265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75919373999312948406596353 56939530499484711304947265)
        ·
          refine ⟨42704647874613533478710449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56939530499484711304947265 42704647874613533478710449)
          ·
            refine ⟨32028485905960150109032837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42704647874613533478710449 32028485905960150109032837)
            ·
              refine ⟨6005341107367528145443657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32028485905960150109032837 6005341107367528145443657)
              ·
                refine ⟨4504005830525646109082743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005341107367528145443657 4504005830525646109082743)
                ·
                  refine ⟨6756008745788469163624115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504005830525646109082743 6756008745788469163624115)
                  ·
                    refine ⟨10134013118682703745436173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6756008745788469163624115 10134013118682703745436173)
                    ·
                      refine ⟨3800254919506013904538565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10134013118682703745436173 3800254919506013904538565)
                      ·
                        rfl

theorem cell23_7400970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_7400970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400970 prefixEnd_7400970 := by exact prefixLift 7400970
  have htrace : WordTrace (prefixWord ++ tailWord_7400970) baseStart_7400970 baseEnd_7400970 := by
    simpa [prefixWord, tailWord_7400970, baseEnd_7400970] using wordTrace_append hprefix tailTrace_7400970
  have hstable : (prefixWord ++ tailWord_7400970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400970).length < 2 ^ (prefixWord ++ tailWord_7400970).sum := by decide
  have hdescent : baseEnd_7400970 < baseStart_7400970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400979 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 3]
def baseStart_7400979 : Nat := 118140960795 + 7400979 * 2 ^ 59
def prefixEnd_7400979 : Nat := 4983230072969 + 3 ^ 40 * 7400979 * 2
def baseEnd_7400979 : Nat := 3800259540831904369326023

theorem tailTrace_7400979 : CollatzResearch.WordTrace tailWord_7400979 prefixEnd_7400979 3800259540831904369326023 := by
  unfold tailWord_7400979
  simp only [CollatzResearch.WordTrace]
  refine ⟨269935880254524544427197991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179957253503016362951465327 269935880254524544427197991)
  ·
    refine ⟨404903820381786816640796987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269935880254524544427197991 404903820381786816640796987)
    ·
      refine ⟨607355730572680224961195481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404903820381786816640796987 607355730572680224961195481)
      ·
        refine ⟨455516797929510168720896611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607355730572680224961195481 455516797929510168720896611)
        ·
          refine ⟨683275196894265253081344917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455516797929510168720896611 683275196894265253081344917)
          ·
            refine ⟨32028524854418683738188043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 683275196894265253081344917 32028524854418683738188043)
            ·
              refine ⟨48042787281628025607282065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32028524854418683738188043 48042787281628025607282065)
              ·
                refine ⟨36032090461221019205461549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48042787281628025607282065 36032090461221019205461549)
                ·
                  refine ⟨13512033922957882202048081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36032090461221019205461549 13512033922957882202048081)
                  ·
                    refine ⟨10134025442218411651536061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13512033922957882202048081 10134025442218411651536061)
                    ·
                      refine ⟨3800259540831904369326023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10134025442218411651536061 3800259540831904369326023)
                      ·
                        rfl

theorem cell23_7400979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 3].length) (baseStart_7400979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400979 prefixEnd_7400979 := by exact prefixLift 7400979
  have htrace : WordTrace (prefixWord ++ tailWord_7400979) baseStart_7400979 baseEnd_7400979 := by
    simpa [prefixWord, tailWord_7400979, baseEnd_7400979] using wordTrace_append hprefix tailTrace_7400979
  have hstable : (prefixWord ++ tailWord_7400979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400979).length < 2 ^ (prefixWord ++ tailWord_7400979).sum := by decide
  have hdescent : baseEnd_7400979 < baseStart_7400979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400993 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 3, 2, 2]
def baseStart_7400993 : Nat := 118140960795 + 7400993 * 2 ^ 59
def prefixEnd_7400993 : Nat := 4983230072969 + 3 ^ 40 * 7400993 * 2
def baseEnd_7400993 : Nat := 3800266729561067314550959

theorem tailTrace_7400993 : CollatzResearch.WordTrace tailWord_7400993 prefixEnd_7400993 3800266729561067314550959 := by
  unfold tailWord_7400993
  simp only [CollatzResearch.WordTrace]
  refine ⟨269936390876473824818207633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179957593917649216545471755 269936390876473824818207633)
  ·
    refine ⟨202452293157355368613655725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269936390876473824818207633 202452293157355368613655725)
    ·
      refine ⟨75919609934008263230120897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202452293157355368613655725 75919609934008263230120897)
      ·
        refine ⟨56939707450506197422590673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75919609934008263230120897 56939707450506197422590673)
        ·
          refine ⟨42704780587879648066943005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56939707450506197422590673 42704780587879648066943005)
          ·
            refine ⟨16014292720454868025103627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42704780587879648066943005 16014292720454868025103627)
            ·
              refine ⟨24021439080682302037655441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16014292720454868025103627 24021439080682302037655441)
              ·
                refine ⟨18016079310511726528241581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24021439080682302037655441 18016079310511726528241581)
                ·
                  refine ⟨6756029741441897448090593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18016079310511726528241581 6756029741441897448090593)
                  ·
                    refine ⟨5067022306081423086067945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6756029741441897448090593 5067022306081423086067945)
                    ·
                      refine ⟨3800266729561067314550959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067022306081423086067945 3800266729561067314550959)
                      ·
                        rfl

theorem cell23_7400993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_7400993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7400993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7400993 prefixEnd_7400993 := by exact prefixLift 7400993
  have htrace : WordTrace (prefixWord ++ tailWord_7400993) baseStart_7400993 baseEnd_7400993 := by
    simpa [prefixWord, tailWord_7400993, baseEnd_7400993] using wordTrace_append hprefix tailTrace_7400993
  have hstable : (prefixWord ++ tailWord_7400993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400993).length < 2 ^ (prefixWord ++ tailWord_7400993).sum := by decide
  have hdescent : baseEnd_7400993 < baseStart_7400993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401006 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_7401006 : Nat := 118140960795 + 7401006 * 2 ^ 59
def prefixEnd_7401006 : Nat := 4983230072969 + 3 ^ 40 * 7401006 * 2
def baseEnd_7401006 : Nat := 3800273404809575763688399

theorem tailTrace_7401006 : CollatzResearch.WordTrace tailWord_7401006 prefixEnd_7401006 3800273404809575763688399 := by
  unfold tailWord_7401006
  simp only [CollatzResearch.WordTrace]
  refine ⟨33742108128178341004803859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179957910016951152025620581 33742108128178341004803859)
  ·
    refine ⟨50613162192267511507205789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33742108128178341004803859 50613162192267511507205789)
    ·
      refine ⟨18979935822100316815202171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50613162192267511507205789 18979935822100316815202171)
      ·
        refine ⟨28469903733150475222803257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18979935822100316815202171 28469903733150475222803257)
        ·
          refine ⟨21352427799862856417102443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28469903733150475222803257 21352427799862856417102443)
          ·
            refine ⟨32028641699794284625653665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21352427799862856417102443 32028641699794284625653665)
            ·
              refine ⟨24021481274845713469240249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32028641699794284625653665 24021481274845713469240249)
              ·
                refine ⟨18016110956134285101930187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24021481274845713469240249 18016110956134285101930187)
                ·
                  refine ⟨27024166434201427652895281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18016110956134285101930187 27024166434201427652895281)
                  ·
                    refine ⟨20268124825651070739671461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27024166434201427652895281 20268124825651070739671461)
                    ·
                      refine ⟨3800273404809575763688399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20268124825651070739671461 3800273404809575763688399)
                      ·
                        rfl

theorem cell23_7401006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_7401006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401006 prefixEnd_7401006 := by exact prefixLift 7401006
  have htrace : WordTrace (prefixWord ++ tailWord_7401006) baseStart_7401006 baseEnd_7401006 := by
    simpa [prefixWord, tailWord_7401006, baseEnd_7401006] using wordTrace_append hprefix tailTrace_7401006
  have hstable : (prefixWord ++ tailWord_7401006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401006).length < 2 ^ (prefixWord ++ tailWord_7401006).sum := by decide
  have hdescent : baseEnd_7401006 < baseStart_7401006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401013 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_7401013 : Nat := 118140960795 + 7401013 * 2 ^ 59
def prefixEnd_7401013 : Nat := 4983230072969 + 3 ^ 40 * 7401013 * 2
def baseEnd_7401013 : Nat := 3800276999174157236300867

theorem tailTrace_7401013 : CollatzResearch.WordTrace tailWord_7401013 prefixEnd_7401013 3800276999174157236300867 := by
  unfold tailWord_7401013
  simp only [CollatzResearch.WordTrace]
  refine ⟨269937120336401368233935693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179958080224267578822623795 269937120336401368233935693)
  ·
    refine ⟨101226420126150513087725885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269937120336401368233935693 101226420126150513087725885)
    ·
      refine ⟨37959907547306442407897207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101226420126150513087725885 37959907547306442407897207)
      ·
        refine ⟨56939861320959663611845811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37959907547306442407897207 56939861320959663611845811)
        ·
          refine ⟨85409791981439495417768717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56939861320959663611845811 85409791981439495417768717)
          ·
            refine ⟨32028671993039810781663269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85409791981439495417768717 32028671993039810781663269)
            ·
              refine ⟨6005375998694964521561863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32028671993039810781663269 6005375998694964521561863)
              ·
                refine ⟨9008063998042446782342795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6005375998694964521561863 9008063998042446782342795)
                ·
                  refine ⟨13512095997063670173514193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9008063998042446782342795 13512095997063670173514193)
                  ·
                    refine ⟨10134071997797752630135645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13512095997063670173514193 10134071997797752630135645)
                    ·
                      refine ⟨3800276999174157236300867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10134071997797752630135645 3800276999174157236300867)
                      ·
                        rfl

theorem cell23_7401013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_7401013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401013 prefixEnd_7401013 := by exact prefixLift 7401013
  have htrace : WordTrace (prefixWord ++ tailWord_7401013) baseStart_7401013 baseEnd_7401013 := by
    simpa [prefixWord, tailWord_7401013, baseEnd_7401013] using wordTrace_append hprefix tailTrace_7401013
  have hstable : (prefixWord ++ tailWord_7401013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401013).length < 2 ^ (prefixWord ++ tailWord_7401013).sum := by decide
  have hdescent : baseEnd_7401013 < baseStart_7401013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401020 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 2, 4]
def baseStart_7401020 : Nat := 118140960795 + 7401020 * 2 ^ 59
def prefixEnd_7401020 : Nat := 4983230072969 + 3 ^ 40 * 7401020 * 2
def baseEnd_7401020 : Nat := 1266760197846246236304445

theorem tailTrace_7401020 : CollatzResearch.WordTrace tailWord_7401020 prefixEnd_7401020 1266760197846246236304445 := by
  unfold tailWord_7401020
  simp only [CollatzResearch.WordTrace]
  refine ⟨134968687823688004214720257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179958250431584005619627009 134968687823688004214720257)
  ·
    refine ⟨101226515867766003161040193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134968687823688004214720257 101226515867766003161040193)
    ·
      refine ⟨75919886900824502370780145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101226515867766003161040193 75919886900824502370780145)
      ·
        refine ⟨56939915175618376778085109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75919886900824502370780145 56939915175618376778085109)
        ·
          refine ⟨5338117047714222822945479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56939915175618376778085109 5338117047714222822945479)
          ·
            refine ⟨8007175571571334234418219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338117047714222822945479 8007175571571334234418219)
            ·
              refine ⟨12010763357357001351627329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007175571571334234418219 12010763357357001351627329)
              ·
                refine ⟨9008072518017751013720497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12010763357357001351627329 9008072518017751013720497)
                ·
                  refine ⟨6756054388513313260290373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9008072518017751013720497 6756054388513313260290373)
                  ·
                    refine ⟨1266760197846246236304445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6756054388513313260290373 1266760197846246236304445)
                    ·
                      rfl

theorem cell23_7401020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_7401020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401020 prefixEnd_7401020 := by exact prefixLift 7401020
  have htrace : WordTrace (prefixWord ++ tailWord_7401020) baseStart_7401020 baseEnd_7401020 := by
    simpa [prefixWord, tailWord_7401020, baseEnd_7401020] using wordTrace_append hprefix tailTrace_7401020
  have hstable : (prefixWord ++ tailWord_7401020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401020).length < 2 ^ (prefixWord ++ tailWord_7401020).sum := by decide
  have hdescent : baseEnd_7401020 < baseStart_7401020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401083 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 2, 2, 2]
def baseStart_7401083 : Nat := 118140960795 + 7401083 * 2 ^ 59
def prefixEnd_7401083 : Nat := 4983230072969 + 3 ^ 40 * 7401083 * 2
def baseEnd_7401083 : Nat := 3800312942819971962425545

theorem tailTrace_7401083 : CollatzResearch.WordTrace tailWord_7401083 prefixEnd_7401083 3800312942819971962425545 := by
  unfold tailWord_7401083
  simp only [CollatzResearch.WordTrace]
  refine ⟨269939673446147770188983903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179959782297431846792655935 269939673446147770188983903)
  ·
    refine ⟨404909510169221655283475855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269939673446147770188983903 404909510169221655283475855)
    ·
      refine ⟨607364265253832482925213783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404909510169221655283475855 607364265253832482925213783)
      ·
        refine ⟨911046397880748724387820675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607364265253832482925213783 911046397880748724387820675)
        ·
          refine ⟨1366569596821123086581731013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911046397880748724387820675 1366569596821123086581731013)
          ·
            refine ⟨256231799403960578734074565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1366569596821123086581731013 256231799403960578734074565)
            ·
              refine ⟨48043462388242608512638981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256231799403960578734074565 48043462388242608512638981)
              ·
                refine ⟨9008149197795489096119809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48043462388242608512638981 9008149197795489096119809)
                ·
                  refine ⟨6756111898346616822089857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9008149197795489096119809 6756111898346616822089857)
                  ·
                    refine ⟨5067083923759962616567393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6756111898346616822089857 5067083923759962616567393)
                    ·
                      refine ⟨3800312942819971962425545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067083923759962616567393 3800312942819971962425545)
                      ·
                        rfl

theorem cell23_7401083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 2, 2].length) (baseStart_7401083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401083 prefixEnd_7401083 := by exact prefixLift 7401083
  have htrace : WordTrace (prefixWord ++ tailWord_7401083) baseStart_7401083 baseEnd_7401083 := by
    simpa [prefixWord, tailWord_7401083, baseEnd_7401083] using wordTrace_append hprefix tailTrace_7401083
  have hstable : (prefixWord ++ tailWord_7401083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401083).length < 2 ^ (prefixWord ++ tailWord_7401083).sum := by decide
  have hdescent : baseEnd_7401083 < baseStart_7401083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401099 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 3]
def baseStart_7401099 : Nat := 118140960795 + 7401099 * 2 ^ 59
def prefixEnd_7401099 : Nat := 4983230072969 + 3 ^ 40 * 7401099 * 2
def baseEnd_7401099 : Nat := 3800321158510443899825471

theorem tailTrace_7401099 : CollatzResearch.WordTrace tailWord_7401099 prefixEnd_7401099 3800321158510443899825471 := by
  unfold tailWord_7401099
  simp only [CollatzResearch.WordTrace]
  refine ⟨269940257014089804921566351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179960171342726536614377567 269940257014089804921566351)
  ·
    refine ⟨404910385521134707382349527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269940257014089804921566351 404910385521134707382349527)
    ·
      refine ⟨607365578281702061073524291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404910385521134707382349527 607365578281702061073524291)
      ·
        refine ⟨911048367422553091610286437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607365578281702061073524291 911048367422553091610286437)
        ·
          refine ⟨170821568891728704676928707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 911048367422553091610286437 170821568891728704676928707)
          ·
            refine ⟨256232353337593057015393061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170821568891728704676928707 256232353337593057015393061)
            ·
              refine ⟨48043566250798698190386199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256232353337593057015393061 48043566250798698190386199)
              ·
                refine ⟨72065349376198047285579299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48043566250798698190386199 72065349376198047285579299)
                ·
                  refine ⟨108098024064297070928368949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72065349376198047285579299 108098024064297070928368949)
                  ·
                    refine ⟨10134189756027850399534589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108098024064297070928368949 10134189756027850399534589)
                    ·
                      refine ⟨3800321158510443899825471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10134189756027850399534589 3800321158510443899825471)
                      ·
                        rfl

theorem cell23_7401099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 3].length) (baseStart_7401099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401099 prefixEnd_7401099 := by exact prefixLift 7401099
  have htrace : WordTrace (prefixWord ++ tailWord_7401099) baseStart_7401099 baseEnd_7401099 := by
    simpa [prefixWord, tailWord_7401099, baseEnd_7401099] using wordTrace_append hprefix tailTrace_7401099
  have hstable : (prefixWord ++ tailWord_7401099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401099).length < 2 ^ (prefixWord ++ tailWord_7401099).sum := by decide
  have hdescent : baseEnd_7401099 < baseStart_7401099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401134 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_7401134 : Nat := 118140960795 + 7401134 * 2 ^ 59
def prefixEnd_7401134 : Nat := 4983230072969 + 3 ^ 40 * 7401134 * 2
def baseEnd_7401134 : Nat := 3800339130333351262887811

theorem tailTrace_7401134 : CollatzResearch.WordTrace tailWord_7401134 prefixEnd_7401134 3800339130333351262887811 := by
  unfold tailWord_7401134
  simp only [CollatzResearch.WordTrace]
  refine ⟨33742691696120375737386307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179961022379308670599393637 33742691696120375737386307)
  ·
    refine ⟨50614037544180563606079461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33742691696120375737386307 50614037544180563606079461)
    ·
      refine ⟨9490132039533855676139899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50614037544180563606079461 9490132039533855676139899)
      ·
        refine ⟨14235198059300783514209849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9490132039533855676139899 14235198059300783514209849)
        ·
          refine ⟨10676398544475587635657387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14235198059300783514209849 10676398544475587635657387)
          ·
            refine ⟨16014597816713381453486081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10676398544475587635657387 16014597816713381453486081)
            ·
              refine ⟨12010948362535036090114561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16014597816713381453486081 12010948362535036090114561)
              ·
                refine ⟨9008211271901277067585921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12010948362535036090114561 9008211271901277067585921)
                ·
                  refine ⟨6756158453925957800689441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9008211271901277067585921 6756158453925957800689441)
                  ·
                    refine ⟨5067118840444468350517081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6756158453925957800689441 5067118840444468350517081)
                    ·
                      refine ⟨3800339130333351262887811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067118840444468350517081 3800339130333351262887811)
                      ·
                        rfl

theorem cell23_7401134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_7401134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401134 prefixEnd_7401134 := by exact prefixLift 7401134
  have htrace : WordTrace (prefixWord ++ tailWord_7401134) baseStart_7401134 baseEnd_7401134 := by
    simpa [prefixWord, tailWord_7401134, baseEnd_7401134] using wordTrace_append hprefix tailTrace_7401134
  have hstable : (prefixWord ++ tailWord_7401134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401134).length < 2 ^ (prefixWord ++ tailWord_7401134).sum := by decide
  have hdescent : baseEnd_7401134 < baseStart_7401134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401156 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_7401156 : Nat := 118140960795 + 7401156 * 2 ^ 59
def prefixEnd_7401156 : Nat := 4983230072969 + 3 ^ 40 * 7401156 * 2
def baseEnd_7401156 : Nat := 3800350426907750176812709

theorem tailTrace_7401156 : CollatzResearch.WordTrace tailWord_7401156 prefixEnd_7401156 3800350426907750176812709 := by
  unfold tailWord_7401156
  simp only [CollatzResearch.WordTrace]
  refine ⟨134971167987441651828195661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179961557316588869104260881 134971167987441651828195661)
  ·
    refine ⟨50614187995290619435573373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134971167987441651828195661 50614187995290619435573373)
    ·
      refine ⟨18980320498233982288340015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50614187995290619435573373 18980320498233982288340015)
      ·
        refine ⟨28470480747350973432510023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18980320498233982288340015 28470480747350973432510023)
        ·
          refine ⟨42705721121026460148765035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28470480747350973432510023 42705721121026460148765035)
          ·
            refine ⟨64058581681539690223147553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42705721121026460148765035 64058581681539690223147553)
            ·
              refine ⟨48043936261154767667360665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64058581681539690223147553 48043936261154767667360665)
              ·
                refine ⟨36032952195866075750520499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48043936261154767667360665 36032952195866075750520499)
                ·
                  refine ⟨54049428293799113625780749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36032952195866075750520499 54049428293799113625780749)
                  ·
                    refine ⟨20268535610174667609667781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54049428293799113625780749 20268535610174667609667781)
                    ·
                      refine ⟨3800350426907750176812709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20268535610174667609667781 3800350426907750176812709)
                      ·
                        rfl

theorem cell23_7401156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_7401156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401156 prefixEnd_7401156 := by exact prefixLift 7401156
  have htrace : WordTrace (prefixWord ++ tailWord_7401156) baseStart_7401156 baseEnd_7401156 := by
    simpa [prefixWord, tailWord_7401156, baseEnd_7401156] using wordTrace_append hprefix tailTrace_7401156
  have hstable : (prefixWord ++ tailWord_7401156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401156).length < 2 ^ (prefixWord ++ tailWord_7401156).sum := by decide
  have hdescent : baseEnd_7401156 < baseStart_7401156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401176 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 1, 4, 3]
def baseStart_7401176 : Nat := 118140960795 + 7401176 * 2 ^ 59
def prefixEnd_7401176 : Nat := 4983230072969 + 3 ^ 40 * 7401176 * 2
def baseEnd_7401176 : Nat := 3800360696520840098562617

theorem tailTrace_7401176 : CollatzResearch.WordTrace tailWord_7401176 prefixEnd_7401176 3800360696520840098562617 := by
  unfold tailWord_7401176
  simp only [CollatzResearch.WordTrace]
  refine ⟨134971532717405423536059691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179962043623207231381412921 134971532717405423536059691)
  ·
    refine ⟨202457299076108135304089537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134971532717405423536059691 202457299076108135304089537)
    ·
      refine ⟨151842974307081101478067153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202457299076108135304089537 151842974307081101478067153)
      ·
        refine ⟨113882230730310826108550365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151842974307081101478067153 113882230730310826108550365)
        ·
          refine ⟨42705836523866559790706387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113882230730310826108550365 42705836523866559790706387)
          ·
            refine ⟨64058754785799839686059581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42705836523866559790706387 64058754785799839686059581)
            ·
              refine ⟨24022033044674939882272343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64058754785799839686059581 24022033044674939882272343)
              ·
                refine ⟨36033049567012409823408515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24022033044674939882272343 36033049567012409823408515)
                ·
                  refine ⟨54049574350518614735112773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36033049567012409823408515 54049574350518614735112773)
                  ·
                    refine ⟨10134295190722240262833645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54049574350518614735112773 10134295190722240262833645)
                    ·
                      refine ⟨3800360696520840098562617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10134295190722240262833645 3800360696520840098562617)
                      ·
                        rfl

theorem cell23_7401176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_7401176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401176 prefixEnd_7401176 := by exact prefixLift 7401176
  have htrace : WordTrace (prefixWord ++ tailWord_7401176) baseStart_7401176 baseEnd_7401176 := by
    simpa [prefixWord, tailWord_7401176, baseEnd_7401176] using wordTrace_append hprefix tailTrace_7401176
  have hstable : (prefixWord ++ tailWord_7401176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401176).length < 2 ^ (prefixWord ++ tailWord_7401176).sum := by decide
  have hdescent : baseEnd_7401176 < baseStart_7401176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401196 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 6]
def baseStart_7401196 : Nat := 118140960795 + 7401196 * 2 ^ 59
def prefixEnd_7401196 : Nat := 4983230072969 + 3 ^ 40 * 7401196 * 2
def baseEnd_7401196 : Nat := 422263440681547780034725

theorem tailTrace_7401196 : CollatzResearch.WordTrace tailWord_7401196 prefixEnd_7401196 422263440681547780034725 := by
  unfold tailWord_7401196
  simp only [CollatzResearch.WordTrace]
  refine ⟨134971897447369195243923721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179962529929825593658564961 134971897447369195243923721)
  ·
    refine ⟨101228923085526896432942791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134971897447369195243923721 101228923085526896432942791)
    ·
      refine ⟨151843384628290344649414187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101228923085526896432942791 151843384628290344649414187)
      ·
        refine ⟨227765076942435516974121281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151843384628290344649414187 227765076942435516974121281)
        ·
          refine ⟨170823807706826637730590961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227765076942435516974121281 170823807706826637730590961)
          ·
            refine ⟨128117855780119978297943221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170823807706826637730590961 128117855780119978297943221)
            ·
              refine ⟨12011048979386247965432177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128117855780119978297943221 12011048979386247965432177)
              ·
                refine ⟨9008286734539685974074133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12011048979386247965432177 9008286734539685974074133)
                ·
                  refine ⟨422263440681547780034725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9008286734539685974074133 422263440681547780034725)
                  ·
                    rfl

theorem cell23_7401196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_7401196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401196 prefixEnd_7401196 := by exact prefixLift 7401196
  have htrace : WordTrace (prefixWord ++ tailWord_7401196) baseStart_7401196 baseEnd_7401196 := by
    simpa [prefixWord, tailWord_7401196, baseEnd_7401196] using wordTrace_append hprefix tailTrace_7401196
  have hstable : (prefixWord ++ tailWord_7401196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401196).length < 2 ^ (prefixWord ++ tailWord_7401196).sum := by decide
  have hdescent : baseEnd_7401196 < baseStart_7401196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401199 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_7401199 : Nat := 118140960795 + 7401199 * 2 ^ 59
def prefixEnd_7401199 : Nat := 4983230072969 + 3 ^ 40 * 7401199 * 2
def baseEnd_7401199 : Nat := 3800372506575893508575011

theorem tailTrace_7401199 : CollatzResearch.WordTrace tailWord_7401199 prefixEnd_7401199 3800372506575893508575011 := by
  unfold tailWord_7401199
  simp only [CollatzResearch.WordTrace]
  refine ⟨269943904313727522000206651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179962602875818348000137767 269943904313727522000206651)
  ·
    refine ⟨404915856470591283000309977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269943904313727522000206651 404915856470591283000309977)
    ·
      refine ⟨303686892352943462250232483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404915856470591283000309977 303686892352943462250232483)
      ·
        refine ⟨455530338529415193375348725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303686892352943462250232483 455530338529415193375348725)
        ·
          refine ⟨42705969237132674378938943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 455530338529415193375348725 42705969237132674378938943)
          ·
            refine ⟨64058953855699011568408415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42705969237132674378938943 64058953855699011568408415)
            ·
              refine ⟨96088430783548517352612623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64058953855699011568408415 96088430783548517352612623)
              ·
                refine ⟨144132646175322776028918935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96088430783548517352612623 144132646175322776028918935)
                ·
                  refine ⟨216198969262984164043378403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144132646175322776028918935 216198969262984164043378403)
                  ·
                    refine ⟨324298453894476246065067605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216198969262984164043378403 324298453894476246065067605)
                    ·
                      refine ⟨3800372506575893508575011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 324298453894476246065067605 3800372506575893508575011)
                      ·
                        rfl

theorem cell23_7401199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_7401199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401199 prefixEnd_7401199 := by exact prefixLift 7401199
  have htrace : WordTrace (prefixWord ++ tailWord_7401199) baseStart_7401199 baseEnd_7401199 := by
    simpa [prefixWord, tailWord_7401199, baseEnd_7401199] using wordTrace_append hprefix tailTrace_7401199
  have hstable : (prefixWord ++ tailWord_7401199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401199).length < 2 ^ (prefixWord ++ tailWord_7401199).sum := by decide
  have hdescent : baseEnd_7401199 < baseStart_7401199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401219 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 7]
def baseStart_7401219 : Nat := 118140960795 + 7401219 * 2 ^ 59
def prefixEnd_7401219 : Nat := 4983230072969 + 3 ^ 40 * 7401219 * 2
def baseEnd_7401219 : Nat := 3800382776188983430324919

theorem tailTrace_7401219 : CollatzResearch.WordTrace tailWord_7401219 prefixEnd_7401219 3800382776188983430324919 := by
  unfold tailWord_7401219
  simp only [CollatzResearch.WordTrace]
  refine ⟨269944633773655065415934711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179963089182436710277289807 269944633773655065415934711)
  ·
    refine ⟨404916950660482598123902067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269944633773655065415934711 404916950660482598123902067)
    ·
      refine ⟨607375425990723897185853101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404916950660482598123902067 607375425990723897185853101)
      ·
        refine ⟨227765784746521461444694913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607375425990723897185853101 227765784746521461444694913)
        ·
          refine ⟨170824338559891096083521185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227765784746521461444694913 170824338559891096083521185)
          ·
            refine ⟨128118253919918322062640889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170824338559891096083521185 128118253919918322062640889)
            ·
              refine ⟨96088690439938741546980667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128118253919918322062640889 96088690439938741546980667)
              ·
                refine ⟨144133035659908112320471001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96088690439938741546980667 144133035659908112320471001)
                ·
                  refine ⟨108099776744931084240353251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144133035659908112320471001 108099776744931084240353251)
                  ·
                    refine ⟨162149665117396626360529877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108099776744931084240353251 162149665117396626360529877)
                    ·
                      refine ⟨3800382776188983430324919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162149665117396626360529877 3800382776188983430324919)
                      ·
                        rfl

theorem cell23_7401219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_7401219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401219 prefixEnd_7401219 := by exact prefixLift 7401219
  have htrace : WordTrace (prefixWord ++ tailWord_7401219) baseStart_7401219 baseEnd_7401219 := by
    simpa [prefixWord, tailWord_7401219, baseEnd_7401219] using wordTrace_append hprefix tailTrace_7401219
  have hstable : (prefixWord ++ tailWord_7401219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401219).length < 2 ^ (prefixWord ++ tailWord_7401219).sum := by decide
  have hdescent : baseEnd_7401219 < baseStart_7401219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401233 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 2, 3, 2]
def baseStart_7401233 : Nat := 118140960795 + 7401233 * 2 ^ 59
def prefixEnd_7401233 : Nat := 4983230072969 + 3 ^ 40 * 7401233 * 2
def baseEnd_7401233 : Nat := 3800389964918146375549855

theorem tailTrace_7401233 : CollatzResearch.WordTrace tailWord_7401233 prefixEnd_7401233 3800389964918146375549855 := by
  unfold tailWord_7401233
  simp only [CollatzResearch.WordTrace]
  refine ⟨269945144395604345806944353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179963429597069563871296235 269945144395604345806944353)
  ·
    refine ⟨202458858296703259355208265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269945144395604345806944353 202458858296703259355208265)
    ·
      refine ⟨151844143722527444516406199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202458858296703259355208265 151844143722527444516406199)
      ·
        refine ⟨227766215583791166774609299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151844143722527444516406199 227766215583791166774609299)
        ·
          refine ⟨341649323375686750161913949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227766215583791166774609299 341649323375686750161913949)
          ·
            refine ⟨128118496265882531310717731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341649323375686750161913949 128118496265882531310717731)
            ·
              refine ⟨192177744398823796966076597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128118496265882531310717731 192177744398823796966076597)
              ·
                refine ⟨18016663537389730965569681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192177744398823796966076597 18016663537389730965569681)
                ·
                  refine ⟨13512497653042298224177261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18016663537389730965569681 13512497653042298224177261)
                  ·
                    refine ⟨5067186619890861834066473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13512497653042298224177261 5067186619890861834066473)
                    ·
                      refine ⟨3800389964918146375549855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067186619890861834066473 3800389964918146375549855)
                      ·
                        rfl

theorem cell23_7401233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 3, 2].length) (baseStart_7401233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401233 prefixEnd_7401233 := by exact prefixLift 7401233
  have htrace : WordTrace (prefixWord ++ tailWord_7401233) baseStart_7401233 baseEnd_7401233 := by
    simpa [prefixWord, tailWord_7401233, baseEnd_7401233] using wordTrace_append hprefix tailTrace_7401233
  have hstable : (prefixWord ++ tailWord_7401233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401233).length < 2 ^ (prefixWord ++ tailWord_7401233).sum := by decide
  have hdescent : baseEnd_7401233 < baseStart_7401233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401234 : List Nat := [3, 2, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_7401234 : Nat := 118140960795 + 7401234 * 2 ^ 59
def prefixEnd_7401234 : Nat := 4983230072969 + 3 ^ 40 * 7401234 * 2
def baseEnd_7401234 : Nat := 1266796826132933623879117

theorem tailTrace_7401234 : CollatzResearch.WordTrace tailWord_7401234 prefixEnd_7401234 1266796826132933623879117 := by
  unfold tailWord_7401234
  simp only [CollatzResearch.WordTrace]
  refine ⟨67486295217150180744432689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179963453912400481985153837 67486295217150180744432689)
  ·
    refine ⟨50614721412862635558324517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67486295217150180744432689 50614721412862635558324517)
    ·
      refine ⟨9490260264911744167185847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50614721412862635558324517 9490260264911744167185847)
      ·
        refine ⟨14235390397367616250778771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9490260264911744167185847 14235390397367616250778771)
        ·
          refine ⟨21353085596051424376168157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14235390397367616250778771 21353085596051424376168157)
          ·
            refine ⟨8007407098519284141063059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21353085596051424376168157 8007407098519284141063059)
            ·
              refine ⟨12011110647778926211594589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007407098519284141063059 12011110647778926211594589)
              ·
                refine ⟨4504166492917097329347971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12011110647778926211594589 4504166492917097329347971)
                ·
                  refine ⟨6756249739375645994021957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504166492917097329347971 6756249739375645994021957)
                  ·
                    refine ⟨1266796826132933623879117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6756249739375645994021957 1266796826132933623879117)
                    ·
                      rfl

theorem cell23_7401234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_7401234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401234 prefixEnd_7401234 := by exact prefixLift 7401234
  have htrace : WordTrace (prefixWord ++ tailWord_7401234) baseStart_7401234 baseEnd_7401234 := by
    simpa [prefixWord, tailWord_7401234, baseEnd_7401234] using wordTrace_append hprefix tailTrace_7401234
  have hstable : (prefixWord ++ tailWord_7401234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401234).length < 2 ^ (prefixWord ++ tailWord_7401234).sum := by decide
  have hdescent : baseEnd_7401234 < baseStart_7401234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401250 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_7401250 : Nat := 118140960795 + 7401250 * 2 ^ 59
def prefixEnd_7401250 : Nat := 4983230072969 + 3 ^ 40 * 7401250 * 2
def baseEnd_7401250 : Nat := 3800398694089272809037277

theorem tailTrace_7401250 : CollatzResearch.WordTrace tailWord_7401250 prefixEnd_7401250 3800398694089272809037277 := by
  unfold tailWord_7401250
  simp only [CollatzResearch.WordTrace]
  refine ⟨67486441109135689427578301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179963842957695171806875469 67486441109135689427578301)
  ·
    refine ⟨25307415415925883535341863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67486441109135689427578301 25307415415925883535341863)
    ·
      refine ⟨37961123123888825303012795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25307415415925883535341863 37961123123888825303012795)
      ·
        refine ⟨56941684685833237954519193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37961123123888825303012795 56941684685833237954519193)
        ·
          refine ⟨42706263514374928465889395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56941684685833237954519193 42706263514374928465889395)
          ·
            refine ⟨64059395271562392698834093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42706263514374928465889395 64059395271562392698834093)
            ·
              refine ⟨24022273226835897262062785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64059395271562392698834093 24022273226835897262062785)
              ·
                refine ⟨18016704920126922946547089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24022273226835897262062785 18016704920126922946547089)
                ·
                  refine ⟨13512528690095192209910317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18016704920126922946547089 13512528690095192209910317)
                  ·
                    refine ⟨5067198258785697078716369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13512528690095192209910317 5067198258785697078716369)
                    ·
                      refine ⟨3800398694089272809037277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067198258785697078716369 3800398694089272809037277)
                      ·
                        rfl

theorem cell23_7401250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_7401250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401250 prefixEnd_7401250 := by exact prefixLift 7401250
  have htrace : WordTrace (prefixWord ++ tailWord_7401250) baseStart_7401250 baseEnd_7401250 := by
    simpa [prefixWord, tailWord_7401250, baseEnd_7401250] using wordTrace_append hprefix tailTrace_7401250
  have hstable : (prefixWord ++ tailWord_7401250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401250).length < 2 ^ (prefixWord ++ tailWord_7401250).sum := by decide
  have hdescent : baseEnd_7401250 < baseStart_7401250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401276 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_7401276 : Nat := 118140960795 + 7401276 * 2 ^ 59
def prefixEnd_7401276 : Nat := 4983230072969 + 3 ^ 40 * 7401276 * 2
def baseEnd_7401276 : Nat := 3800412044586289707312157

theorem tailTrace_7401276 : CollatzResearch.WordTrace tailWord_7401276 prefixEnd_7401276 3800412044586289707312157 := by
  unfold tailWord_7401276
  simp only [CollatzResearch.WordTrace]
  refine ⟨134973356367224282075379841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179964475156299042767173121 134973356367224282075379841)
  ·
    refine ⟨101230017275418211556534881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134973356367224282075379841 101230017275418211556534881)
    ·
      refine ⟨75922512956563658667401161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101230017275418211556534881 75922512956563658667401161)
      ·
        refine ⟨56941884717422744000550871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75922512956563658667401161 56941884717422744000550871)
        ·
          refine ⟨85412827076134116000826307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56941884717422744000550871 85412827076134116000826307)
          ·
            refine ⟨128119240614201174001239461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85412827076134116000826307 128119240614201174001239461)
            ·
              refine ⟨24022357615162720125232399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128119240614201174001239461 24022357615162720125232399)
              ·
                refine ⟨36033536422744080187848599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24022357615162720125232399 36033536422744080187848599)
                ·
                  refine ⟨54050304634116120281772899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36033536422744080187848599 54050304634116120281772899)
                  ·
                    refine ⟨81075456951174180422659349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54050304634116120281772899 81075456951174180422659349)
                    ·
                      refine ⟨3800412044586289707312157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81075456951174180422659349 3800412044586289707312157)
                      ·
                        rfl

theorem cell23_7401276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_7401276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401276 prefixEnd_7401276 := by exact prefixLift 7401276
  have htrace : WordTrace (prefixWord ++ tailWord_7401276) baseStart_7401276 baseEnd_7401276 := by
    simpa [prefixWord, tailWord_7401276, baseEnd_7401276] using wordTrace_append hprefix tailTrace_7401276
  have hstable : (prefixWord ++ tailWord_7401276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401276).length < 2 ^ (prefixWord ++ tailWord_7401276).sum := by decide
  have hdescent : baseEnd_7401276 < baseStart_7401276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401283 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 3]
def baseStart_7401283 : Nat := 118140960795 + 7401283 * 2 ^ 59
def prefixEnd_7401283 : Nat := 4983230072969 + 3 ^ 40 * 7401283 * 2
def baseEnd_7401283 : Nat := 3800415638950871179924625

theorem tailTrace_7401283 : CollatzResearch.WordTrace tailWord_7401283 prefixEnd_7401283 3800415638950871179924625 := by
  unfold tailWord_7401283
  simp only [CollatzResearch.WordTrace]
  refine ⟨269946968045423204346264503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179964645363615469564176335 269946968045423204346264503)
  ·
    refine ⟨404920452068134806519396755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269946968045423204346264503 404920452068134806519396755)
    ·
      refine ⟨607380678102202209779095133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404920452068134806519396755 607380678102202209779095133)
      ·
        refine ⟨227767754288325828667160675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607380678102202209779095133 227767754288325828667160675)
        ·
          refine ⟨341651631432488743000741013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227767754288325828667160675 341651631432488743000741013)
          ·
            refine ⟨16014920223397909828159735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 341651631432488743000741013 16014920223397909828159735)
            ·
              refine ⟨24022380335096864742239603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16014920223397909828159735 24022380335096864742239603)
              ·
                refine ⟨36033570502645297113359405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24022380335096864742239603 36033570502645297113359405)
                ·
                  refine ⟨13512588938491986417509777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36033570502645297113359405 13512588938491986417509777)
                  ·
                    refine ⟨10134441703868989813132333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13512588938491986417509777 10134441703868989813132333)
                    ·
                      refine ⟨3800415638950871179924625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10134441703868989813132333 3800415638950871179924625)
                      ·
                        rfl

theorem cell23_7401283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_7401283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401283 prefixEnd_7401283 := by exact prefixLift 7401283
  have htrace : WordTrace (prefixWord ++ tailWord_7401283) baseStart_7401283 baseEnd_7401283 := by
    simpa [prefixWord, tailWord_7401283, baseEnd_7401283] using wordTrace_append hprefix tailTrace_7401283
  have hstable : (prefixWord ++ tailWord_7401283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401283).length < 2 ^ (prefixWord ++ tailWord_7401283).sum := by decide
  have hdescent : baseEnd_7401283 < baseStart_7401283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401300 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_7401300 : Nat := 118140960795 + 7401300 * 2 ^ 59
def prefixEnd_7401300 : Nat := 4983230072969 + 3 ^ 40 * 7401300 * 2
def baseEnd_7401300 : Nat := 3800424368121997613412047

theorem tailTrace_7401300 : CollatzResearch.WordTrace tailWord_7401300 prefixEnd_7401300 3800424368121997613412047 := by
  unfold tailWord_7401300
  simp only [CollatzResearch.WordTrace]
  refine ⟨134973794043180808124816677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179965058724241077499755569 134973794043180808124816677)
  ·
    refine ⟨25307586383096401523403127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134973794043180808124816677 25307586383096401523403127)
    ·
      refine ⟨37961379574644602285104691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25307586383096401523403127 37961379574644602285104691)
      ·
        refine ⟨56942069361966903427657037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37961379574644602285104691 56942069361966903427657037)
        ·
          refine ⟨21353276010737588785371389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56942069361966903427657037 21353276010737588785371389)
          ·
            refine ⟨8007478504026595794514271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21353276010737588785371389 8007478504026595794514271)
            ·
              refine ⟨12011217756039893691771407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007478504026595794514271 12011217756039893691771407)
              ·
                refine ⟨18016826634059840537657111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12011217756039893691771407 18016826634059840537657111)
                ·
                  refine ⟨27025239951089760806485667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18016826634059840537657111 27025239951089760806485667)
                  ·
                    refine ⟨40537859926634641209728501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27025239951089760806485667 40537859926634641209728501)
                    ·
                      refine ⟨3800424368121997613412047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40537859926634641209728501 3800424368121997613412047)
                      ·
                        rfl

theorem cell23_7401300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_7401300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401300 prefixEnd_7401300 := by exact prefixLift 7401300
  have htrace : WordTrace (prefixWord ++ tailWord_7401300) baseStart_7401300 baseEnd_7401300 := by
    simpa [prefixWord, tailWord_7401300, baseEnd_7401300] using wordTrace_append hprefix tailTrace_7401300
  have hstable : (prefixWord ++ tailWord_7401300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401300).length < 2 ^ (prefixWord ++ tailWord_7401300).sum := by decide
  have hdescent : baseEnd_7401300 < baseStart_7401300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401308 : List Nat := [2, 2, 4, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_7401308 : Nat := 118140960795 + 7401308 * 2 ^ 59
def prefixEnd_7401308 : Nat := 4983230072969 + 3 ^ 40 * 7401308 * 2
def baseEnd_7401308 : Nat := 3800428475967233582112011

theorem tailTrace_7401308 : CollatzResearch.WordTrace tailWord_7401308 prefixEnd_7401308 3800428475967233582112011 := by
  unfold tailWord_7401308
  simp only [CollatzResearch.WordTrace]
  refine ⟨134973939935166316807962289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179965253246888422410616385 134973939935166316807962289)
  ·
    refine ⟨101230454951374737605971717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134973939935166316807962289 101230454951374737605971717)
    ·
      refine ⟨18980710303382763301119697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101230454951374737605971717 18980710303382763301119697)
      ·
        refine ⟨14235532727537072475839773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18980710303382763301119697 14235532727537072475839773)
        ·
          refine ⟨5338324772826402178439915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14235532727537072475839773 5338324772826402178439915)
          ·
            refine ⟨8007487159239603267659873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338324772826402178439915 8007487159239603267659873)
            ·
              refine ⟨6005615369429702450744905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8007487159239603267659873 6005615369429702450744905)
              ·
                refine ⟨4504211527072276838058679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005615369429702450744905 4504211527072276838058679)
                ·
                  refine ⟨6756317290608415257088019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504211527072276838058679 6756317290608415257088019)
                  ·
                    refine ⟨10134475935912622885632029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6756317290608415257088019 10134475935912622885632029)
                    ·
                      refine ⟨3800428475967233582112011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10134475935912622885632029 3800428475967233582112011)
                      ·
                        rfl

theorem cell23_7401308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_7401308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401308 prefixEnd_7401308 := by exact prefixLift 7401308
  have htrace : WordTrace (prefixWord ++ tailWord_7401308) baseStart_7401308 baseEnd_7401308 := by
    simpa [prefixWord, tailWord_7401308, baseEnd_7401308] using wordTrace_append hprefix tailTrace_7401308
  have hstable : (prefixWord ++ tailWord_7401308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401308).length < 2 ^ (prefixWord ++ tailWord_7401308).sum := by decide
  have hdescent : baseEnd_7401308 < baseStart_7401308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401356 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_7401356 : Nat := 118140960795 + 7401356 * 2 ^ 59
def prefixEnd_7401356 : Nat := 4983230072969 + 3 ^ 40 * 7401356 * 2
def baseEnd_7401356 : Nat := 3800453123038649394311789

theorem tailTrace_7401356 : CollatzResearch.WordTrace tailWord_7401356 prefixEnd_7401356 3800453123038649394311789 := by
  unfold tailWord_7401356
  simp only [CollatzResearch.WordTrace]
  refine ⟨134974815287079368906835961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179966420382772491875781281 134974815287079368906835961)
  ·
    refine ⟨101231111465309526680126971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134974815287079368906835961 101231111465309526680126971)
    ·
      refine ⟨151846667197964290020190457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101231111465309526680126971 151846667197964290020190457)
      ·
        refine ⟨113885000398473217515142843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151846667197964290020190457 113885000398473217515142843)
        ·
          refine ⟨170827500597709826272714265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113885000398473217515142843 170827500597709826272714265)
          ·
            refine ⟨128120625448282369704535699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170827500597709826272714265 128120625448282369704535699)
            ·
              refine ⟨192180938172423554556803549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128120625448282369704535699 192180938172423554556803549)
              ·
                refine ⟨72067851814658832958801331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192180938172423554556803549 72067851814658832958801331)
                ·
                  refine ⟨108101777721988249438201997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72067851814658832958801331 108101777721988249438201997)
                  ·
                    refine ⟨40538166645745593539325749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108101777721988249438201997 40538166645745593539325749)
                    ·
                      refine ⟨3800453123038649394311789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40538166645745593539325749 3800453123038649394311789)
                      ·
                        rfl

theorem cell23_7401356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_7401356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401356 prefixEnd_7401356 := by exact prefixLift 7401356
  have htrace : WordTrace (prefixWord ++ tailWord_7401356) baseStart_7401356 baseEnd_7401356 := by
    simpa [prefixWord, tailWord_7401356, baseEnd_7401356] using wordTrace_append hprefix tailTrace_7401356
  have hstable : (prefixWord ++ tailWord_7401356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401356).length < 2 ^ (prefixWord ++ tailWord_7401356).sum := by decide
  have hdescent : baseEnd_7401356 < baseStart_7401356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401364 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_7401364 : Nat := 118140960795 + 7401364 * 2 ^ 59
def prefixEnd_7401364 : Nat := 4983230072969 + 3 ^ 40 * 7401364 * 2
def baseEnd_7401364 : Nat := 3800457230883885363011753

theorem tailTrace_7401364 : CollatzResearch.WordTrace tailWord_7401364 prefixEnd_7401364 3800457230883885363011753 := by
  unfold tailWord_7401364
  simp only [CollatzResearch.WordTrace]
  refine ⟨134974961179064877589981573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179966614905419836786642097 134974961179064877589981573)
  ·
    refine ⟨25307805221074664548121545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134974961179064877589981573 25307805221074664548121545)
    ·
      refine ⟨18980853915805998411091159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25307805221074664548121545 18980853915805998411091159)
      ·
        refine ⟨28471280873708997616636739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18980853915805998411091159 28471280873708997616636739)
        ·
          refine ⟨42706921310563496424955109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28471280873708997616636739 42706921310563496424955109)
          ·
            refine ⟨8007547745730655579679083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42706921310563496424955109 8007547745730655579679083)
            ·
              refine ⟨12011321618595983369518625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007547745730655579679083 12011321618595983369518625)
              ·
                refine ⟨9008491213946987527138969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12011321618595983369518625 9008491213946987527138969)
                ·
                  refine ⟨6756368410460240645354227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9008491213946987527138969 6756368410460240645354227)
                  ·
                    refine ⟨10134552615690360968031341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6756368410460240645354227 10134552615690360968031341)
                    ·
                      refine ⟨3800457230883885363011753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10134552615690360968031341 3800457230883885363011753)
                      ·
                        rfl

theorem cell23_7401364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_7401364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401364 prefixEnd_7401364 := by exact prefixLift 7401364
  have htrace : WordTrace (prefixWord ++ tailWord_7401364) baseStart_7401364 baseEnd_7401364 := by
    simpa [prefixWord, tailWord_7401364, baseEnd_7401364] using wordTrace_append hprefix tailTrace_7401364
  have hstable : (prefixWord ++ tailWord_7401364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401364).length < 2 ^ (prefixWord ++ tailWord_7401364).sum := by decide
  have hdescent : baseEnd_7401364 < baseStart_7401364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401393 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 7]
def baseStart_7401393 : Nat := 118140960795 + 7401393 * 2 ^ 59
def prefixEnd_7401393 : Nat := 4983230072969 + 3 ^ 40 * 7401393 * 2
def baseEnd_7401393 : Nat := 422274680202540638838791

theorem tailTrace_7401393 : CollatzResearch.WordTrace tailWord_7401393 prefixEnd_7401393 422274680202540638838791 := by
  unfold tailWord_7401393
  simp only [CollatzResearch.WordTrace]
  refine ⟨269950980075024693132768833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179967320050016462088512555 269950980075024693132768833)
  ·
    refine ⟨202463235056268519849576625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269950980075024693132768833 202463235056268519849576625)
    ·
      refine ⟨151847426292201389887182469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202463235056268519849576625 151847426292201389887182469)
      ·
        refine ⟨28471392429787760603846713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151847426292201389887182469 28471392429787760603846713)
        ·
          refine ⟨21353544322340820452885035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28471392429787760603846713 21353544322340820452885035)
          ·
            refine ⟨32030316483511230679327553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21353544322340820452885035 32030316483511230679327553)
            ·
              refine ⟨24022737362633423009495665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32030316483511230679327553 24022737362633423009495665)
              ·
                refine ⟨18017053021975067257121749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24022737362633423009495665 18017053021975067257121749)
                ·
                  refine ⟨422274680202540638838791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18017053021975067257121749 422274680202540638838791)
                  ·
                    rfl

theorem cell23_7401393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 7].length) (baseStart_7401393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401393 prefixEnd_7401393 := by exact prefixLift 7401393
  have htrace : WordTrace (prefixWord ++ tailWord_7401393) baseStart_7401393 baseEnd_7401393 := by
    simpa [prefixWord, tailWord_7401393, baseEnd_7401393] using wordTrace_append hprefix tailTrace_7401393
  have hstable : (prefixWord ++ tailWord_7401393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401393).length < 2 ^ (prefixWord ++ tailWord_7401393).sum := by decide
  have hdescent : baseEnd_7401393 < baseStart_7401393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401423 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 2, 5]
def baseStart_7401423 : Nat := 118140960795 + 7401423 * 2 ^ 59
def prefixEnd_7401423 : Nat := 4983230072969 + 3 ^ 40 * 7401423 * 2
def baseEnd_7401423 : Nat := 1266829175414166877391327

theorem tailTrace_7401423 : CollatzResearch.WordTrace tailWord_7401423 prefixEnd_7401423 1266829175414166877391327 := by
  unfold tailWord_7401423
  simp only [CollatzResearch.WordTrace]
  refine ⟨269952074264916008256360923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179968049509944005504240615 269952074264916008256360923)
  ·
    refine ⟨404928111397374012384541385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269952074264916008256360923 404928111397374012384541385)
    ·
      refine ⟨303696083548030509288406039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404928111397374012384541385 303696083548030509288406039)
      ·
        refine ⟨455544125322045763932609059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303696083548030509288406039 455544125322045763932609059)
        ·
          refine ⟨683316187983068645898913589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455544125322045763932609059 683316187983068645898913589)
          ·
            refine ⟨64060892623412685553023149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 683316187983068645898913589 64060892623412685553023149)
            ·
              refine ⟨24022834733779757082383681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64060892623412685553023149 24022834733779757082383681)
              ·
                refine ⟨18017126050334817811787761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24022834733779757082383681 18017126050334817811787761)
                ·
                  refine ⟨13512844537751113358840821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18017126050334817811787761 13512844537751113358840821)
                  ·
                    refine ⟨1266829175414166877391327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13512844537751113358840821 1266829175414166877391327)
                    ·
                      rfl

theorem cell23_7401423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_7401423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401423 prefixEnd_7401423 := by exact prefixLift 7401423
  have htrace : WordTrace (prefixWord ++ tailWord_7401423) baseStart_7401423 baseEnd_7401423 := by
    simpa [prefixWord, tailWord_7401423, baseEnd_7401423] using wordTrace_append hprefix tailTrace_7401423
  have hstable : (prefixWord ++ tailWord_7401423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401423).length < 2 ^ (prefixWord ++ tailWord_7401423).sum := by decide
  have hdescent : baseEnd_7401423 < baseStart_7401423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401473 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_7401473 : Nat := 118140960795 + 7401473 * 2 ^ 59
def prefixEnd_7401473 : Nat := 4983230072969 + 3 ^ 40 * 7401473 * 2
def baseEnd_7401473 : Nat := 3800513200275225436548751

theorem tailTrace_7401473 : CollatzResearch.WordTrace tailWord_7401473 prefixEnd_7401473 3800513200275225436548751 := by
  unfold tailWord_7401473
  simp only [CollatzResearch.WordTrace]
  refine ⟨269953897914734866795681073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179969265276489911197120715 269953897914734866795681073)
  ·
    refine ⟨202465423436051150096760805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269953897914734866795681073 202465423436051150096760805)
    ·
      refine ⟨37962266894259590643142651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202465423436051150096760805 37962266894259590643142651)
      ·
        refine ⟨56943400341389385964713977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37962266894259590643142651 56943400341389385964713977)
        ·
          refine ⟨42707550256042039473535483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56943400341389385964713977 42707550256042039473535483)
          ·
            refine ⟨64061325384063059210303225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42707550256042039473535483 64061325384063059210303225)
            ·
              refine ⟨48045994038047294407727419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64061325384063059210303225 48045994038047294407727419)
              ·
                refine ⟨72068991057070941611591129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48045994038047294407727419 72068991057070941611591129)
                ·
                  refine ⟨54051743292803206208693347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72068991057070941611591129 54051743292803206208693347)
                  ·
                    refine ⟨81077614939204809313040021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54051743292803206208693347 81077614939204809313040021)
                    ·
                      refine ⟨3800513200275225436548751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81077614939204809313040021 3800513200275225436548751)
                      ·
                        rfl

theorem cell23_7401473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_7401473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401473 prefixEnd_7401473 := by exact prefixLift 7401473
  have htrace : WordTrace (prefixWord ++ tailWord_7401473) baseStart_7401473 baseEnd_7401473 := by
    simpa [prefixWord, tailWord_7401473, baseEnd_7401473] using wordTrace_append hprefix tailTrace_7401473
  have hstable : (prefixWord ++ tailWord_7401473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401473).length < 2 ^ (prefixWord ++ tailWord_7401473).sum := by decide
  have hdescent : baseEnd_7401473 < baseStart_7401473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401478 : List Nat := [6, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_7401478 : Nat := 118140960795 + 7401478 * 2 ^ 59
def prefixEnd_7401478 : Nat := 4983230072969 + 3 ^ 40 * 7401478 * 2
def baseEnd_7401478 : Nat := 422279529742055324109581

theorem tailTrace_7401478 : CollatzResearch.WordTrace tailWord_7401478 prefixEnd_7401478 422279529742055324109581 := by
  unfold tailWord_7401478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8436065008741148520300409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179969386853144501766408725 8436065008741148520300409)
  ·
    refine ⟨6327048756555861390225307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8436065008741148520300409 6327048756555861390225307)
    ·
      refine ⟨9490573134833792085337961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6327048756555861390225307 9490573134833792085337961)
      ·
        refine ⟨7117929851125344064003471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9490573134833792085337961 7117929851125344064003471)
        ·
          refine ⟨10676894776688016096005207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7117929851125344064003471 10676894776688016096005207)
          ·
            refine ⟨16015342165032024144007811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10676894776688016096005207 16015342165032024144007811)
            ·
              refine ⟨24023013247548036216011717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16015342165032024144007811 24023013247548036216011717)
              ·
                refine ⟨4504314983915256790502197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24023013247548036216011717 4504314983915256790502197)
                ·
                  refine ⟨422279529742055324109581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4504314983915256790502197 422279529742055324109581)
                  ·
                    rfl

theorem cell23_7401478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_7401478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401478 prefixEnd_7401478 := by exact prefixLift 7401478
  have htrace : WordTrace (prefixWord ++ tailWord_7401478) baseStart_7401478 baseEnd_7401478 := by
    simpa [prefixWord, tailWord_7401478, baseEnd_7401478] using wordTrace_append hprefix tailTrace_7401478
  have hstable : (prefixWord ++ tailWord_7401478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401478).length < 2 ^ (prefixWord ++ tailWord_7401478).sum := by decide
  have hdescent : baseEnd_7401478 < baseStart_7401478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401480 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_7401480 : Nat := 118140960795 + 7401480 * 2 ^ 59
def prefixEnd_7401480 : Nat := 4983230072969 + 3 ^ 40 * 7401480 * 2
def baseEnd_7401480 : Nat := 3800516794639806909161219

theorem tailTrace_7401480 : CollatzResearch.WordTrace tailWord_7401480 prefixEnd_7401480 3800516794639806909161219 := by
  unfold tailWord_7401480
  simp only [CollatzResearch.WordTrace]
  refine ⟨134977076612854753495592947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179969435483806337994123929 134977076612854753495592947)
  ·
    refine ⟨202465614919282130243389421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134977076612854753495592947 202465614919282130243389421)
    ·
      refine ⟨75924605594730798841271033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202465614919282130243389421 75924605594730798841271033)
      ·
        refine ⟨56943454196048099130953275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75924605594730798841271033 56943454196048099130953275)
        ·
          refine ⟨85415181294072148696429913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56943454196048099130953275 85415181294072148696429913)
          ·
            refine ⟨64061385970554111522322435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85415181294072148696429913 64061385970554111522322435)
            ·
              refine ⟨96092078955831167283483653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64061385970554111522322435 96092078955831167283483653)
              ·
                refine ⟨18017264804218343865653185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96092078955831167283483653 18017264804218343865653185)
                ·
                  refine ⟨13512948603163757899239889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18017264804218343865653185 13512948603163757899239889)
                  ·
                    refine ⟨10134711452372818424429917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13512948603163757899239889 10134711452372818424429917)
                    ·
                      refine ⟨3800516794639806909161219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10134711452372818424429917 3800516794639806909161219)
                      ·
                        rfl

theorem cell23_7401480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_7401480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401480 prefixEnd_7401480 := by exact prefixLift 7401480
  have htrace : WordTrace (prefixWord ++ tailWord_7401480) baseStart_7401480 baseEnd_7401480 := by
    simpa [prefixWord, tailWord_7401480, baseEnd_7401480] using wordTrace_append hprefix tailTrace_7401480
  have hstable : (prefixWord ++ tailWord_7401480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401480).length < 2 ^ (prefixWord ++ tailWord_7401480).sum := by decide
  have hdescent : baseEnd_7401480 < baseStart_7401480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401500 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 6]
def baseStart_7401500 : Nat := 118140960795 + 7401500 * 2 ^ 59
def prefixEnd_7401500 : Nat := 4983230072969 + 3 ^ 40 * 7401500 * 2
def baseEnd_7401500 : Nat := 422280784916988536767903

theorem tailTrace_7401500 : CollatzResearch.WordTrace tailWord_7401500 prefixEnd_7401500 422280784916988536767903 := by
  unfold tailWord_7401500
  simp only [CollatzResearch.WordTrace]
  refine ⟨134977441342818525203456977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179969921790424700271275969 134977441342818525203456977)
  ·
    refine ⟨101233081007113893902592733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134977441342818525203456977 101233081007113893902592733)
    ·
      refine ⟨37962405377667710213472275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101233081007113893902592733 37962405377667710213472275)
      ·
        refine ⟨56943608066501565320208413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37962405377667710213472275 56943608066501565320208413)
        ·
          refine ⟨21353853024938086995078155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56943608066501565320208413 21353853024938086995078155)
          ·
            refine ⟨32030779537407130492617233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21353853024938086995078155 32030779537407130492617233)
            ·
              refine ⟨24023084653055347869462925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32030779537407130492617233 24023084653055347869462925)
              ·
                refine ⟨9008656744895755451048597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24023084653055347869462925 9008656744895755451048597)
                ·
                  refine ⟨422280784916988536767903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9008656744895755451048597 422280784916988536767903)
                  ·
                    rfl

theorem cell23_7401500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_7401500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401500 prefixEnd_7401500 := by exact prefixLift 7401500
  have htrace : WordTrace (prefixWord ++ tailWord_7401500) baseStart_7401500 baseEnd_7401500 := by
    simpa [prefixWord, tailWord_7401500, baseEnd_7401500] using wordTrace_append hprefix tailTrace_7401500
  have hstable : (prefixWord ++ tailWord_7401500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401500).length < 2 ^ (prefixWord ++ tailWord_7401500).sum := by decide
  have hdescent : baseEnd_7401500 < baseStart_7401500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401511 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_7401511 : Nat := 118140960795 + 7401511 * 2 ^ 59
def prefixEnd_7401511 : Nat := 4983230072969 + 3 ^ 40 * 7401511 * 2
def baseEnd_7401511 : Nat := 3800532712540096287873577

theorem tailTrace_7401511 : CollatzResearch.WordTrace tailWord_7401511 prefixEnd_7401511 3800532712540096287873577 := by
  unfold tailWord_7401511
  simp only [CollatzResearch.WordTrace]
  refine ⟨269955283888597199285564387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179970189259064799523709591 269955283888597199285564387)
  ·
    refine ⟨404932925832895798928346581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269955283888597199285564387 404932925832895798928346581)
    ·
      refine ⟨9490615449208495287383123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 404932925832895798928346581 9490615449208495287383123)
      ·
        refine ⟨14235923173812742931074685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9490615449208495287383123 14235923173812742931074685)
        ·
          refine ⟨5338471190179778599153007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14235923173812742931074685 5338471190179778599153007)
          ·
            refine ⟨8007706785269667898729511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338471190179778599153007 8007706785269667898729511)
            ·
              refine ⟨12011560177904501848094267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007706785269667898729511 12011560177904501848094267)
              ·
                refine ⟨18017340266856752772141401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12011560177904501848094267 18017340266856752772141401)
                ·
                  refine ⟨13513005200142564579106051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18017340266856752772141401 13513005200142564579106051)
                  ·
                    refine ⟨20269507800213846868659077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13513005200142564579106051 20269507800213846868659077)
                    ·
                      refine ⟨3800532712540096287873577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20269507800213846868659077 3800532712540096287873577)
                      ·
                        rfl

theorem cell23_7401511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_7401511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401511 prefixEnd_7401511 := by exact prefixLift 7401511
  have htrace : WordTrace (prefixWord ++ tailWord_7401511) baseStart_7401511 baseEnd_7401511 := by
    simpa [prefixWord, tailWord_7401511, baseEnd_7401511] using wordTrace_append hprefix tailTrace_7401511
  have hstable : (prefixWord ++ tailWord_7401511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401511).length < 2 ^ (prefixWord ++ tailWord_7401511).sum := by decide
  have hdescent : baseEnd_7401511 < baseStart_7401511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401514 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_7401514 : Nat := 118140960795 + 7401514 * 2 ^ 59
def prefixEnd_7401514 : Nat := 4983230072969 + 3 ^ 40 * 7401514 * 2
def baseEnd_7401514 : Nat := 3800534252982059776136063

theorem tailTrace_7401514 : CollatzResearch.WordTrace tailWord_7401514 prefixEnd_7401514 3800534252982059776136063 := by
  unfold tailWord_7401514
  simp only [CollatzResearch.WordTrace]
  refine ⟨67488848326896582699480899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179970262205057553865282397 67488848326896582699480899)
  ·
    refine ⟨101233272490344874049221349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67488848326896582699480899 101233272490344874049221349)
    ·
      refine ⟨18981238591939663884229003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101233272490344874049221349 18981238591939663884229003)
      ·
        refine ⟨28471857887909495826343505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18981238591939663884229003 28471857887909495826343505)
        ·
          refine ⟨21353893415932121869757629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28471857887909495826343505 21353893415932121869757629)
          ·
            refine ⟨8007710030974545701159111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21353893415932121869757629 8007710030974545701159111)
            ·
              refine ⟨12011565046461818551738667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007710030974545701159111 12011565046461818551738667)
              ·
                refine ⟨18017347569692727827608001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12011565046461818551738667 18017347569692727827608001)
                ·
                  refine ⟨13513010677269545870706001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18017347569692727827608001 13513010677269545870706001)
                  ·
                    refine ⟨10134758007952159403029501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13513010677269545870706001 10134758007952159403029501)
                    ·
                      refine ⟨3800534252982059776136063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10134758007952159403029501 3800534252982059776136063)
                      ·
                        rfl

theorem cell23_7401514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_7401514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401514 prefixEnd_7401514 := by exact prefixLift 7401514
  have htrace : WordTrace (prefixWord ++ tailWord_7401514) baseStart_7401514 baseEnd_7401514 := by
    simpa [prefixWord, tailWord_7401514, baseEnd_7401514] using wordTrace_append hprefix tailTrace_7401514
  have hstable : (prefixWord ++ tailWord_7401514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401514).length < 2 ^ (prefixWord ++ tailWord_7401514).sum := by decide
  have hdescent : baseEnd_7401514 < baseStart_7401514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401534 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_7401534 : Nat := 118140960795 + 7401534 * 2 ^ 59
def prefixEnd_7401534 : Nat := 4983230072969 + 3 ^ 40 * 7401534 * 2
def baseEnd_7401534 : Nat := 422282724732794410876219

theorem tailTrace_7401534 : CollatzResearch.WordTrace tailWord_7401534 prefixEnd_7401534 422282724732794410876219 := by
  unfold tailWord_7401534
  simp only [CollatzResearch.WordTrace]
  refine ⟨33744515345939234276706457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179970748511675916142434437 33744515345939234276706457)
  ·
    refine ⟨25308386509454425707529843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33744515345939234276706457 25308386509454425707529843)
    ·
      refine ⟨37962579764181638561294765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25308386509454425707529843 37962579764181638561294765)
      ·
        refine ⟨14235967411568114460485537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37962579764181638561294765 14235967411568114460485537)
        ·
          refine ⟨10676975558676085845364153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14235967411568114460485537 10676975558676085845364153)
          ·
            refine ⟨8007731669007064384023115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10676975558676085845364153 8007731669007064384023115)
            ·
              refine ⟨12011597503510596576034673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007731669007064384023115 12011597503510596576034673)
              ·
                refine ⟨9008698127632947432026005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12011597503510596576034673 9008698127632947432026005)
                ·
                  refine ⟨422282724732794410876219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9008698127632947432026005 422282724732794410876219)
                  ·
                    rfl

theorem cell23_7401534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_7401534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401534 prefixEnd_7401534 := by exact prefixLift 7401534
  have htrace : WordTrace (prefixWord ++ tailWord_7401534) baseStart_7401534 baseEnd_7401534 := by
    simpa [prefixWord, tailWord_7401534, baseEnd_7401534] using wordTrace_append hprefix tailTrace_7401534
  have hstable : (prefixWord ++ tailWord_7401534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401534).length < 2 ^ (prefixWord ++ tailWord_7401534).sum := by decide
  have hdescent : baseEnd_7401534 < baseStart_7401534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401560 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 1, 6]
def baseStart_7401560 : Nat := 118140960795 + 7401560 * 2 ^ 59
def prefixEnd_7401560 : Nat := 4983230072969 + 3 ^ 40 * 7401560 * 2
def baseEnd_7401560 : Nat := 1266852624364055532053617

theorem tailTrace_7401560 : CollatzResearch.WordTrace tailWord_7401560 prefixEnd_7401560 1266852624364055532053617 := by
  unfold tailWord_7401560
  simp only [CollatzResearch.WordTrace]
  refine ⟨134978535532709840327049067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179971380710279787102732089 134978535532709840327049067)
  ·
    refine ⟨202467803299064760490573601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134978535532709840327049067 202467803299064760490573601)
    ·
      refine ⟨151850852474298570367930201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202467803299064760490573601 151850852474298570367930201)
      ·
        refine ⟨113888139355723927775947651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151850852474298570367930201 113888139355723927775947651)
        ·
          refine ⟨170832209033585891663921477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113888139355723927775947651 170832209033585891663921477)
          ·
            refine ⟨32031039193797354686985277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170832209033585891663921477 32031039193797354686985277)
            ·
              refine ⟨12011639697674008007619479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32031039193797354686985277 12011639697674008007619479)
              ·
                refine ⟨18017459546511012011429219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12011639697674008007619479 18017459546511012011429219)
                ·
                  refine ⟨27026189319766518017143829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18017459546511012011429219 27026189319766518017143829)
                  ·
                    refine ⟨1266852624364055532053617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27026189319766518017143829 1266852624364055532053617)
                    ·
                      rfl

theorem cell23_7401560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_7401560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401560 prefixEnd_7401560 := by exact prefixLift 7401560
  have htrace : WordTrace (prefixWord ++ tailWord_7401560) baseStart_7401560 baseEnd_7401560 := by
    simpa [prefixWord, tailWord_7401560, baseEnd_7401560] using wordTrace_append hprefix tailTrace_7401560
  have hstable : (prefixWord ++ tailWord_7401560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401560).length < 2 ^ (prefixWord ++ tailWord_7401560).sum := by decide
  have hdescent : baseEnd_7401560 < baseStart_7401560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401567 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 5, 2, 2]
def baseStart_7401567 : Nat := 118140960795 + 7401567 * 2 ^ 59
def prefixEnd_7401567 : Nat := 4983230072969 + 3 ^ 40 * 7401567 * 2
def baseEnd_7401567 : Nat := 3800561467456748068773319

theorem tailTrace_7401567 : CollatzResearch.WordTrace tailWord_7401567 prefixEnd_7401567 3800561467456748068773319 := by
  unfold tailWord_7401567
  simp only [CollatzResearch.WordTrace]
  refine ⟨269957326376394320849602955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179971550917596213899735303 269957326376394320849602955)
  ·
    refine ⟨404935989564591481274404433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269957326376394320849602955 404935989564591481274404433)
    ·
      refine ⟨303701992173443610955803325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404935989564591481274404433 303701992173443610955803325)
      ·
        refine ⟨113888247065041354108426247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303701992173443610955803325 113888247065041354108426247)
        ·
          refine ⟨170832370597562031162639371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113888247065041354108426247 170832370597562031162639371)
          ·
            refine ⟨256248555896343046743959057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170832370597562031162639371 256248555896343046743959057)
            ·
              refine ⟨192186416922257285057969293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256248555896343046743959057 192186416922257285057969293)
              ·
                refine ⟨72069906345846481896738485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192186416922257285057969293 72069906345846481896738485)
                ·
                  refine ⟨6756553719923107677819233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72069906345846481896738485 6756553719923107677819233)
                  ·
                    refine ⟨5067415289942330758364425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6756553719923107677819233 5067415289942330758364425)
                    ·
                      refine ⟨3800561467456748068773319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067415289942330758364425 3800561467456748068773319)
                      ·
                        rfl

theorem cell23_7401567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_7401567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401567 prefixEnd_7401567 := by exact prefixLift 7401567
  have htrace : WordTrace (prefixWord ++ tailWord_7401567) baseStart_7401567 baseEnd_7401567 := by
    simpa [prefixWord, tailWord_7401567, baseEnd_7401567] using wordTrace_append hprefix tailTrace_7401567
  have hstable : (prefixWord ++ tailWord_7401567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401567).length < 2 ^ (prefixWord ++ tailWord_7401567).sum := by decide
  have hdescent : baseEnd_7401567 < baseStart_7401567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401578 : List Nat := [3, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_7401578 : Nat := 118140960795 + 7401578 * 2 ^ 59
def prefixEnd_7401578 : Nat := 4983230072969 + 3 ^ 40 * 7401578 * 2
def baseEnd_7401578 : Nat := 3800567115743947525735769

theorem tailTrace_7401578 : CollatzResearch.WordTrace tailWord_7401578 prefixEnd_7401578 3800567115743947525735769 := by
  unfold tailWord_7401578
  simp only [CollatzResearch.WordTrace]
  refine ⟨67489431894838617432063347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179971818386236313152168925 67489431894838617432063347)
  ·
    refine ⟨101234147842257926148095021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67489431894838617432063347 101234147842257926148095021)
    ·
      refine ⟨37962805440846722305535633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101234147842257926148095021 37962805440846722305535633)
      ·
        refine ⟨28472104080635041729151725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37962805440846722305535633 28472104080635041729151725)
        ·
          refine ⟨10677039030238140648431897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28472104080635041729151725 10677039030238140648431897)
          ·
            refine ⟨8007779272678605486323923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10677039030238140648431897 8007779272678605486323923)
            ·
              refine ⟨12011668909017908229485885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007779272678605486323923 12011668909017908229485885)
              ·
                refine ⟨4504375840881715586057207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12011668909017908229485885 4504375840881715586057207)
                ·
                  refine ⟨6756563761322573379085811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504375840881715586057207 6756563761322573379085811)
                  ·
                    refine ⟨10134845641983860068628717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6756563761322573379085811 10134845641983860068628717)
                    ·
                      refine ⟨3800567115743947525735769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10134845641983860068628717 3800567115743947525735769)
                      ·
                        rfl

theorem cell23_7401578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_7401578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401578 prefixEnd_7401578 := by exact prefixLift 7401578
  have htrace : WordTrace (prefixWord ++ tailWord_7401578) baseStart_7401578 baseEnd_7401578 := by
    simpa [prefixWord, tailWord_7401578, baseEnd_7401578] using wordTrace_append hprefix tailTrace_7401578
  have hstable : (prefixWord ++ tailWord_7401578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401578).length < 2 ^ (prefixWord ++ tailWord_7401578).sum := by decide
  have hdescent : baseEnd_7401578 < baseStart_7401578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401590 : List Nat := [5, 1, 1, 2, 1, 2, 11]
def baseStart_7401590 : Nat := 118140960795 + 7401590 * 2 ^ 59
def prefixEnd_7401590 : Nat := 4983230072969 + 3 ^ 40 * 7401590 * 2
def baseEnd_7401590 : Nat := 46920657747059277515873

theorem tailTrace_7401590 : CollatzResearch.WordTrace tailWord_7401590 prefixEnd_7401590 46920657747059277515873 := by
  unfold tailWord_7401590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16872385328456937236105639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179972110170207330518460149 16872385328456937236105639)
  ·
    refine ⟨25308577992685405854158459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16872385328456937236105639 25308577992685405854158459)
    ·
      refine ⟨37962866989028108781237689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25308577992685405854158459 37962866989028108781237689)
      ·
        refine ⟨28472150241771081585928267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37962866989028108781237689 28472150241771081585928267)
        ·
          refine ⟨42708225362656622378892401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28472150241771081585928267 42708225362656622378892401)
          ·
            refine ⟨32031169021992466784169301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42708225362656622378892401 32031169021992466784169301)
            ·
              refine ⟨46920657747059277515873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32031169021992466784169301 46920657747059277515873)
              ·
                rfl

theorem cell23_7401590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 11].length) (baseStart_7401590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401590 prefixEnd_7401590 := by exact prefixLift 7401590
  have htrace : WordTrace (prefixWord ++ tailWord_7401590) baseStart_7401590 baseEnd_7401590 := by
    simpa [prefixWord, tailWord_7401590, baseEnd_7401590] using wordTrace_append hprefix tailTrace_7401590
  have hstable : (prefixWord ++ tailWord_7401590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401590).length < 2 ^ (prefixWord ++ tailWord_7401590).sum := by decide
  have hdescent : baseEnd_7401590 < baseStart_7401590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401622 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7401622 : Nat := 118140960795 + 7401622 * 2 ^ 59
def prefixEnd_7401622 : Nat := 4983230072969 + 3 ^ 40 * 7401622 * 2
def baseEnd_7401622 : Nat := 3800589708892745353585567

theorem tailTrace_7401622 : CollatzResearch.WordTrace tailWord_7401622 prefixEnd_7401622 3800589708892745353585567 := by
  unfold tailWord_7401622
  simp only [CollatzResearch.WordTrace]
  refine ⟨16872458274449691577678445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179972888260796710161903413 16872458274449691577678445)
  ·
    refine ⟨6327171852918634341629417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16872458274449691577678445 6327171852918634341629417)
    ·
      refine ⟨4745378889688975756222063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6327171852918634341629417 4745378889688975756222063)
      ·
        refine ⟨7118068334533463634333095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4745378889688975756222063 7118068334533463634333095)
        ·
          refine ⟨10677102501800195451499643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7118068334533463634333095 10677102501800195451499643)
          ·
            refine ⟨16015653752700293177249465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10677102501800195451499643 16015653752700293177249465)
            ·
              refine ⟨12011740314525219882937099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16015653752700293177249465 12011740314525219882937099)
              ·
                refine ⟨18017610471787829824405649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12011740314525219882937099 18017610471787829824405649)
                ·
                  refine ⟨13513207853840872368304237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18017610471787829824405649 13513207853840872368304237)
                  ·
                    refine ⟨5067452945190327138114089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13513207853840872368304237 5067452945190327138114089)
                    ·
                      refine ⟨3800589708892745353585567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067452945190327138114089 3800589708892745353585567)
                      ·
                        rfl

theorem cell23_7401622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7401622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401622 prefixEnd_7401622 := by exact prefixLift 7401622
  have htrace : WordTrace (prefixWord ++ tailWord_7401622) baseStart_7401622 baseEnd_7401622 := by
    simpa [prefixWord, tailWord_7401622, baseEnd_7401622] using wordTrace_append hprefix tailTrace_7401622
  have hstable : (prefixWord ++ tailWord_7401622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401622).length < 2 ^ (prefixWord ++ tailWord_7401622).sum := by decide
  have hdescent : baseEnd_7401622 < baseStart_7401622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401634 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_7401634 : Nat := 118140960795 + 7401634 * 2 ^ 59
def prefixEnd_7401634 : Nat := 4983230072969 + 3 ^ 40 * 7401634 * 2
def baseEnd_7401634 : Nat := 3800595870660599306635511

theorem tailTrace_7401634 : CollatzResearch.WordTrace tailWord_7401634 prefixEnd_7401634 3800595870660599306635511 := by
  unfold tailWord_7401634
  simp only [CollatzResearch.WordTrace]
  refine ⟨67489942516787897823072989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179973180044767727528194637 67489942516787897823072989)
  ·
    refine ⟨25308728443795461683652371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67489942516787897823072989 25308728443795461683652371)
    ·
      refine ⟨37963092665693192525478557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25308728443795461683652371 37963092665693192525478557)
      ·
        refine ⟨14236159749634947197054459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37963092665693192525478557 14236159749634947197054459)
        ·
          refine ⟨21354239624452420795581689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14236159749634947197054459 21354239624452420795581689)
          ·
            refine ⟨16015679718339315596686267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21354239624452420795581689 16015679718339315596686267)
            ·
              refine ⟨24023519577508973395029401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16015679718339315596686267 24023519577508973395029401)
              ·
                refine ⟨18017639683131730046272051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24023519577508973395029401 18017639683131730046272051)
                ·
                  refine ⟨27026459524697595069408077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18017639683131730046272051 27026459524697595069408077)
                  ·
                    refine ⟨10134922321761598151028029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27026459524697595069408077 10134922321761598151028029)
                    ·
                      refine ⟨3800595870660599306635511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10134922321761598151028029 3800595870660599306635511)
                      ·
                        rfl

theorem cell23_7401634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_7401634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401634 prefixEnd_7401634 := by exact prefixLift 7401634
  have htrace : WordTrace (prefixWord ++ tailWord_7401634) baseStart_7401634 baseEnd_7401634 := by
    simpa [prefixWord, tailWord_7401634, baseEnd_7401634] using wordTrace_append hprefix tailTrace_7401634
  have hstable : (prefixWord ++ tailWord_7401634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401634).length < 2 ^ (prefixWord ++ tailWord_7401634).sum := by decide
  have hdescent : baseEnd_7401634 < baseStart_7401634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401650 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_7401650 : Nat := 118140960795 + 7401650 * 2 ^ 59
def prefixEnd_7401650 : Nat := 4983230072969 + 3 ^ 40 * 7401650 * 2
def baseEnd_7401650 : Nat := 1266868028783690414678479

theorem tailTrace_7401650 : CollatzResearch.WordTrace tailWord_7401650 prefixEnd_7401650 1266868028783690414678479 := by
  unfold tailWord_7401650
  simp only [CollatzResearch.WordTrace]
  refine ⟨67490088408773406506218601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179973569090062417349916269 67490088408773406506218601)
  ·
    refine ⟨50617566306580054879663951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67490088408773406506218601 50617566306580054879663951)
    ·
      refine ⟨75926349459870082319495927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50617566306580054879663951 75926349459870082319495927)
      ·
        refine ⟨113889524189805123479243891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75926349459870082319495927 113889524189805123479243891)
        ·
          refine ⟨170834286284707685218865837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113889524189805123479243891 170834286284707685218865837)
          ·
            refine ⟨64062857356765381957074689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170834286284707685218865837 64062857356765381957074689)
            ·
              refine ⟨48047143017574036467806017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64062857356765381957074689 48047143017574036467806017)
              ·
                refine ⟨36035357263180527350854513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48047143017574036467806017 36035357263180527350854513)
                ·
                  refine ⟨27026517947385395513140885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36035357263180527350854513 27026517947385395513140885)
                  ·
                    refine ⟨1266868028783690414678479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27026517947385395513140885 1266868028783690414678479)
                    ·
                      rfl

theorem cell23_7401650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_7401650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401650 prefixEnd_7401650 := by exact prefixLift 7401650
  have htrace : WordTrace (prefixWord ++ tailWord_7401650) baseStart_7401650 baseEnd_7401650 := by
    simpa [prefixWord, tailWord_7401650, baseEnd_7401650] using wordTrace_append hprefix tailTrace_7401650
  have hstable : (prefixWord ++ tailWord_7401650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401650).length < 2 ^ (prefixWord ++ tailWord_7401650).sum := by decide
  have hdescent : baseEnd_7401650 < baseStart_7401650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401657 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 3, 4, 2]
def baseStart_7401657 : Nat := 118140960795 + 7401657 * 2 ^ 59
def prefixEnd_7401657 : Nat := 4983230072969 + 3 ^ 40 * 7401657 * 2
def baseEnd_7401657 : Nat := 3800607680715652716647905

theorem tailTrace_7401657 : CollatzResearch.WordTrace tailWord_7401657 prefixEnd_7401657 3800607680715652716647905 := by
  unfold tailWord_7401657
  simp only [CollatzResearch.WordTrace]
  refine ⟨269960608946068266220379225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179973739297378844146919483 269960608946068266220379225)
  ·
    refine ⟨202470456709551199665284419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269960608946068266220379225 202470456709551199665284419)
    ·
      refine ⟨303705685064326799497926629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202470456709551199665284419 303705685064326799497926629)
      ·
        refine ⟨56944815949561274905861243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303705685064326799497926629 56944815949561274905861243)
        ·
          refine ⟨85417223924341912358791865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56944815949561274905861243 85417223924341912358791865)
          ·
            refine ⟨64062917943256434269093899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85417223924341912358791865 64062917943256434269093899)
            ·
              refine ⟨96094376914884651403640849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64062917943256434269093899 96094376914884651403640849)
              ·
                refine ⟨72070782686163488552730637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96094376914884651403640849 72070782686163488552730637)
                ·
                  refine ⟨27026543507311308207273989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72070782686163488552730637 27026543507311308207273989)
                  ·
                    refine ⟨5067476907620870288863873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27026543507311308207273989 5067476907620870288863873)
                    ·
                      refine ⟨3800607680715652716647905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067476907620870288863873 3800607680715652716647905)
                      ·
                        rfl

theorem cell23_7401657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_7401657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401657 prefixEnd_7401657 := by exact prefixLift 7401657
  have htrace : WordTrace (prefixWord ++ tailWord_7401657) baseStart_7401657 baseEnd_7401657 := by
    simpa [prefixWord, tailWord_7401657, baseEnd_7401657] using wordTrace_append hprefix tailTrace_7401657
  have hstable : (prefixWord ++ tailWord_7401657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401657).length < 2 ^ (prefixWord ++ tailWord_7401657).sum := by decide
  have hdescent : baseEnd_7401657 < baseStart_7401657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401674 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2]
def baseStart_7401674 : Nat := 118140960795 + 7401674 * 2 ^ 59
def prefixEnd_7401674 : Nat := 4983230072969 + 3 ^ 40 * 7401674 * 2
def baseEnd_7401674 : Nat := 3800616409886779150135327

theorem tailTrace_7401674 : CollatzResearch.WordTrace tailWord_7401674 prefixEnd_7401674 3800616409886779150135327 := by
  unfold tailWord_7401674
  simp only [CollatzResearch.WordTrace]
  refine ⟨67490307246751669530937019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179974152658004452082498717 67490307246751669530937019)
  ·
    refine ⟨101235460870127504296405529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67490307246751669530937019 101235460870127504296405529)
    ·
      refine ⟨75926595652595628222304147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101235460870127504296405529 75926595652595628222304147)
      ·
        refine ⟨113889893478893442333456221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75926595652595628222304147 113889893478893442333456221)
        ·
          refine ⟨42708710054585040875046083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113889893478893442333456221 42708710054585040875046083)
          ·
            refine ⟨64063065081877561312569125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42708710054585040875046083 64063065081877561312569125)
            ·
              refine ⟨12011824702852042746106711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64063065081877561312569125 12011824702852042746106711)
              ·
                refine ⟨18017737054278064119160067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12011824702852042746106711 18017737054278064119160067)
                ·
                  refine ⟨27026605581417096178740101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18017737054278064119160067 27026605581417096178740101)
                  ·
                    refine ⟨5067488546515705533513769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27026605581417096178740101 5067488546515705533513769)
                    ·
                      refine ⟨3800616409886779150135327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067488546515705533513769 3800616409886779150135327)
                      ·
                        rfl

theorem cell23_7401674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_7401674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401674 prefixEnd_7401674 := by exact prefixLift 7401674
  have htrace : WordTrace (prefixWord ++ tailWord_7401674) baseStart_7401674 baseEnd_7401674 := by
    simpa [prefixWord, tailWord_7401674, baseEnd_7401674] using wordTrace_append hprefix tailTrace_7401674
  have hstable : (prefixWord ++ tailWord_7401674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401674).length < 2 ^ (prefixWord ++ tailWord_7401674).sum := by decide
  have hdescent : baseEnd_7401674 < baseStart_7401674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401714 : List Nat := [3, 2, 1, 3, 2, 1, 2, 4, 5]
def baseStart_7401714 : Nat := 118140960795 + 7401714 * 2 ^ 59
def prefixEnd_7401714 : Nat := 4983230072969 + 3 ^ 40 * 7401714 * 2
def baseEnd_7401714 : Nat := 422292994345884332626127

theorem tailTrace_7401714 : CollatzResearch.WordTrace tailWord_7401714 prefixEnd_7401714 422292994345884332626127 := by
  unfold tailWord_7401714
  simp only [CollatzResearch.WordTrace]
  refine ⟨67490671976715441238801049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179975125271241176636802797 67490671976715441238801049)
  ·
    refine ⟨50618003982536580929100787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67490671976715441238801049 50618003982536580929100787)
    ·
      refine ⟨75927005973804871393651181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50618003982536580929100787 75927005973804871393651181)
      ·
        refine ⟨28472627240176826772619193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75927005973804871393651181 28472627240176826772619193)
        ·
          refine ⟨21354470430132620079464395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28472627240176826772619193 21354470430132620079464395)
          ·
            refine ⟨32031705645198930119196593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21354470430132620079464395 32031705645198930119196593)
            ·
              refine ⟨24023779233899197589397445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32031705645198930119196593 24023779233899197589397445)
              ·
                refine ⟨4504458606356099548012021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24023779233899197589397445 4504458606356099548012021)
                ·
                  refine ⟨422292994345884332626127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4504458606356099548012021 422292994345884332626127)
                  ·
                    rfl

theorem cell23_7401714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_7401714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401714 prefixEnd_7401714 := by exact prefixLift 7401714
  have htrace : WordTrace (prefixWord ++ tailWord_7401714) baseStart_7401714 baseEnd_7401714 := by
    simpa [prefixWord, tailWord_7401714, baseEnd_7401714] using wordTrace_append hprefix tailTrace_7401714
  have hstable : (prefixWord ++ tailWord_7401714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401714).length < 2 ^ (prefixWord ++ tailWord_7401714).sum := by decide
  have hdescent : baseEnd_7401714 < baseStart_7401714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401720 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_7401720 : Nat := 118140960795 + 7401720 * 2 ^ 59
def prefixEnd_7401720 : Nat := 4983230072969 + 3 ^ 40 * 7401720 * 2
def baseEnd_7401720 : Nat := 3800640029996885970160115

theorem tailTrace_7401720 : CollatzResearch.WordTrace tailWord_7401720 prefixEnd_7401720 3800640029996885970160115 := by
  unfold tailWord_7401720
  simp only [CollatzResearch.WordTrace]
  refine ⟨134981453372420013989961307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179975271163226685319948409 134981453372420013989961307)
  ·
    refine ⟨202472180058630020984941961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134981453372420013989961307 202472180058630020984941961)
    ·
      refine ⟨151854135043972515738706471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202472180058630020984941961 151854135043972515738706471)
      ·
        refine ⟨227781202565958773608059707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151854135043972515738706471 227781202565958773608059707)
        ·
          refine ⟨341671803848938160412089561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227781202565958773608059707 341671803848938160412089561)
          ·
            refine ⟨256253852886703620309067171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341671803848938160412089561 256253852886703620309067171)
            ·
              refine ⟨384380779330055430463600757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256253852886703620309067171 384380779330055430463600757)
              ·
                refine ⟨36035698062192696605962571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 384380779330055430463600757 36035698062192696605962571)
                ·
                  refine ⟨54053547093289044908943857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36035698062192696605962571 54053547093289044908943857)
                  ·
                    refine ⟨40540160319966783681707893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54053547093289044908943857 40540160319966783681707893)
                    ·
                      refine ⟨3800640029996885970160115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40540160319966783681707893 3800640029996885970160115)
                      ·
                        rfl

theorem cell23_7401720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_7401720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401720 prefixEnd_7401720 := by exact prefixLift 7401720
  have htrace : WordTrace (prefixWord ++ tailWord_7401720) baseStart_7401720 baseEnd_7401720 := by
    simpa [prefixWord, tailWord_7401720, baseEnd_7401720] using wordTrace_append hprefix tailTrace_7401720
  have hstable : (prefixWord ++ tailWord_7401720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401720).length < 2 ^ (prefixWord ++ tailWord_7401720).sum := by decide
  have hdescent : baseEnd_7401720 < baseStart_7401720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401740 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_7401740 : Nat := 118140960795 + 7401740 * 2 ^ 59
def prefixEnd_7401740 : Nat := 4983230072969 + 3 ^ 40 * 7401740 * 2
def baseEnd_7401740 : Nat := 1266883433203325297303341

theorem tailTrace_7401740 : CollatzResearch.WordTrace tailWord_7401740 prefixEnd_7401740 1266883433203325297303341 := by
  unfold tailWord_7401740
  simp only [CollatzResearch.WordTrace]
  refine ⟨134981818102383785697825337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179975757469845047597100449 134981818102383785697825337)
  ·
    refine ⟨101236363576787839273369003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134981818102383785697825337 101236363576787839273369003)
    ·
      refine ⟨151854545365181758910053505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101236363576787839273369003 151854545365181758910053505)
      ·
        refine ⟨113890909023886319182540129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151854545365181758910053505 113890909023886319182540129)
        ·
          refine ⟨85418181767914739386905097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113890909023886319182540129 85418181767914739386905097)
          ·
            refine ⟨64063636325936054540178823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85418181767914739386905097 64063636325936054540178823)
            ·
              refine ⟨96095454488904081810268235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64063636325936054540178823 96095454488904081810268235)
              ·
                refine ⟨144143181733356122715402353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96095454488904081810268235 144143181733356122715402353)
                ·
                  refine ⟨108107386300017092036551765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144143181733356122715402353 108107386300017092036551765)
                  ·
                    refine ⟨1266883433203325297303341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108107386300017092036551765 1266883433203325297303341)
                    ·
                      rfl

theorem cell23_7401740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_7401740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401740 prefixEnd_7401740 := by exact prefixLift 7401740
  have htrace : WordTrace (prefixWord ++ tailWord_7401740) baseStart_7401740 baseEnd_7401740 := by
    simpa [prefixWord, tailWord_7401740, baseEnd_7401740] using wordTrace_append hprefix tailTrace_7401740
  have hstable : (prefixWord ++ tailWord_7401740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401740).length < 2 ^ (prefixWord ++ tailWord_7401740).sum := by decide
  have hdescent : baseEnd_7401740 < baseStart_7401740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401747 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 1, 6, 2]
def baseStart_7401747 : Nat := 118140960795 + 7401747 * 2 ^ 59
def prefixEnd_7401747 : Nat := 4983230072969 + 3 ^ 40 * 7401747 * 2
def baseEnd_7401747 : Nat := 3800653893974557364522491

theorem tailTrace_7401747 : CollatzResearch.WordTrace tailWord_7401747 prefixEnd_7401747 3800653893974557364522491 := by
  unfold tailWord_7401747
  simp only [CollatzResearch.WordTrace]
  refine ⟨269963891515742211591155495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179975927677161474394103663 269963891515742211591155495)
  ·
    refine ⟨404945837273613317386733243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269963891515742211591155495 404945837273613317386733243)
    ·
      refine ⟨607418755910419976080099865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404945837273613317386733243 607418755910419976080099865)
      ·
        refine ⟨455564066932814982060074899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607418755910419976080099865 455564066932814982060074899)
        ·
          refine ⟨683346100399222473090112349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455564066932814982060074899 683346100399222473090112349)
          ·
            refine ⟨256254787649708427408792131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 683346100399222473090112349 256254787649708427408792131)
            ·
              refine ⟨384382181474562641113188197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256254787649708427408792131 384382181474562641113188197)
              ·
                refine ⟨72071659026480495208722787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384382181474562641113188197 72071659026480495208722787)
                ·
                  refine ⟨108107488539720742813084181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72071659026480495208722787 108107488539720742813084181)
                  ·
                    refine ⟨5067538525299409819363321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108107488539720742813084181 5067538525299409819363321)
                    ·
                      refine ⟨3800653893974557364522491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067538525299409819363321 3800653893974557364522491)
                      ·
                        rfl

theorem cell23_7401747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 6, 2].length) (baseStart_7401747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401747 prefixEnd_7401747 := by exact prefixLift 7401747
  have htrace : WordTrace (prefixWord ++ tailWord_7401747) baseStart_7401747 baseEnd_7401747 := by
    simpa [prefixWord, tailWord_7401747, baseEnd_7401747] using wordTrace_append hprefix tailTrace_7401747
  have hstable : (prefixWord ++ tailWord_7401747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401747).length < 2 ^ (prefixWord ++ tailWord_7401747).sum := by decide
  have hdescent : baseEnd_7401747 < baseStart_7401747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401764 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_7401764 : Nat := 118140960795 + 7401764 * 2 ^ 59
def prefixEnd_7401764 : Nat := 4983230072969 + 3 ^ 40 * 7401764 * 2
def baseEnd_7401764 : Nat := 3800662623145683798009913

theorem tailTrace_7401764 : CollatzResearch.WordTrace tailWord_7401764 prefixEnd_7401764 3800662623145683798009913 := by
  unfold tailWord_7401764
  simp only [CollatzResearch.WordTrace]
  refine ⟨134982255778340311747262173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179976341037787082329682897 134982255778340311747262173)
  ·
    refine ⟨50618345916877616905223315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134982255778340311747262173 50618345916877616905223315)
    ·
      refine ⟨75927518875316425357834973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50618345916877616905223315 75927518875316425357834973)
      ·
        refine ⟨28472819578243659509188115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75927518875316425357834973 28472819578243659509188115)
        ·
          refine ⟨42709229367365489263782173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28472819578243659509188115 42709229367365489263782173)
          ·
            refine ⟨16015961012762058473918315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42709229367365489263782173 16015961012762058473918315)
            ·
              refine ⟨24023941519143087710877473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16015961012762058473918315 24023941519143087710877473)
              ·
                refine ⟨18017956139357315783158105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24023941519143087710877473 18017956139357315783158105)
                ·
                  refine ⟨13513467104517986837368579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18017956139357315783158105 13513467104517986837368579)
                  ·
                    refine ⟨20270200656776980256052869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13513467104517986837368579 20270200656776980256052869)
                    ·
                      refine ⟨3800662623145683798009913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20270200656776980256052869 3800662623145683798009913)
                      ·
                        rfl

theorem cell23_7401764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_7401764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401764 prefixEnd_7401764 := by exact prefixLift 7401764
  have htrace : WordTrace (prefixWord ++ tailWord_7401764) baseStart_7401764 baseEnd_7401764 := by
    simpa [prefixWord, tailWord_7401764, baseEnd_7401764] using wordTrace_append hprefix tailTrace_7401764
  have hstable : (prefixWord ++ tailWord_7401764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401764).length < 2 ^ (prefixWord ++ tailWord_7401764).sum := by decide
  have hdescent : baseEnd_7401764 < baseStart_7401764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401834 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_7401834 : Nat := 118140960795 + 7401834 * 2 ^ 59
def prefixEnd_7401834 : Nat := 4983230072969 + 3 ^ 40 * 7401834 * 2
def baseEnd_7401834 : Nat := 1266899522263832841378197

theorem tailTrace_7401834 : CollatzResearch.WordTrace tailWord_7401834 prefixEnd_7401834 1266899522263832841378197 := by
  unfold tailWord_7401834
  simp only [CollatzResearch.WordTrace]
  refine ⟨67491766166606756362393139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179978043110951350299715037 67491766166606756362393139)
  ·
    refine ⟨101237649249910134543589709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67491766166606756362393139 101237649249910134543589709)
    ·
      refine ⟨37964118468716300453846141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101237649249910134543589709 37964118468716300453846141)
      ·
        refine ⟨14236544425768612670192303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37964118468716300453846141 14236544425768612670192303)
        ·
          refine ⟨21354816638652919005288455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14236544425768612670192303 21354816638652919005288455)
          ·
            refine ⟨32032224957979378507932683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21354816638652919005288455 32032224957979378507932683)
            ·
              refine ⟨48048337436969067761899025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32032224957979378507932683 48048337436969067761899025)
              ·
                refine ⟨36036253077726800821424269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48048337436969067761899025 36036253077726800821424269)
                ·
                  refine ⟨13513594904147550308034101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36036253077726800821424269 13513594904147550308034101)
                  ·
                    refine ⟨1266899522263832841378197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13513594904147550308034101 1266899522263832841378197)
                    ·
                      rfl

theorem cell23_7401834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_7401834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401834 prefixEnd_7401834 := by exact prefixLift 7401834
  have htrace : WordTrace (prefixWord ++ tailWord_7401834) baseStart_7401834 baseEnd_7401834 := by
    simpa [prefixWord, tailWord_7401834, baseEnd_7401834] using wordTrace_append hprefix tailTrace_7401834
  have hstable : (prefixWord ++ tailWord_7401834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401834).length < 2 ^ (prefixWord ++ tailWord_7401834).sum := by decide
  have hdescent : baseEnd_7401834 < baseStart_7401834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401864 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 4, 4]
def baseStart_7401864 : Nat := 118140960795 + 7401864 * 2 ^ 59
def prefixEnd_7401864 : Nat := 4983230072969 + 3 ^ 40 * 7401864 * 2
def baseEnd_7401864 : Nat := 1266904657070377802253151

theorem tailTrace_7401864 : CollatzResearch.WordTrace tailWord_7401864 prefixEnd_7401864 1266904657070377802253151 := by
  unfold tailWord_7401864
  simp only [CollatzResearch.WordTrace]
  refine ⟨134984079428159170286582323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179978772570878893715443097 134984079428159170286582323)
  ·
    refine ⟨202476119142238755429873485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134984079428159170286582323 202476119142238755429873485)
    ·
      refine ⟨75928544678339533286202557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202476119142238755429873485 75928544678339533286202557)
      ·
        refine ⟨28473204254377324982325959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75928544678339533286202557 28473204254377324982325959)
        ·
          refine ⟨42709806381565987473488939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28473204254377324982325959 42709806381565987473488939)
          ·
            refine ⟨64064709572348981210233409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42709806381565987473488939 64064709572348981210233409)
            ·
              refine ⟨48048532179261735907675057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64064709572348981210233409 48048532179261735907675057)
              ·
                refine ⟨36036399134446301930756293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48048532179261735907675057 36036399134446301930756293)
                ·
                  refine ⟨6756824837708681612016805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36036399134446301930756293 6756824837708681612016805)
                  ·
                    refine ⟨1266904657070377802253151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6756824837708681612016805 1266904657070377802253151)
                    ·
                      rfl

theorem cell23_7401864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_7401864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401864 prefixEnd_7401864 := by exact prefixLift 7401864
  have htrace : WordTrace (prefixWord ++ tailWord_7401864) baseStart_7401864 baseEnd_7401864 := by
    simpa [prefixWord, tailWord_7401864, baseEnd_7401864] using wordTrace_append hprefix tailTrace_7401864
  have hstable : (prefixWord ++ tailWord_7401864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401864).length < 2 ^ (prefixWord ++ tailWord_7401864).sum := by decide
  have hdescent : baseEnd_7401864 < baseStart_7401864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401888 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 3, 2, 2]
def baseStart_7401888 : Nat := 118140960795 + 7401888 * 2 ^ 59
def prefixEnd_7401888 : Nat := 4983230072969 + 3 ^ 40 * 7401888 * 2
def baseEnd_7401888 : Nat := 3800726294746841312859343

theorem tailTrace_7401888 : CollatzResearch.WordTrace tailWord_7401888 prefixEnd_7401888 3800726294746841312859343 := by
  unfold tailWord_7401888
  simp only [CollatzResearch.WordTrace]
  refine ⟨134984517104115696336019159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179979356138820928448025545 134984517104115696336019159)
  ·
    refine ⟨202476775656173544504028739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134984517104115696336019159 202476775656173544504028739)
    ·
      refine ⟨303715163484260316756043109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202476775656173544504028739 303715163484260316756043109)
      ·
        refine ⟨56946593153298809391758083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303715163484260316756043109 56946593153298809391758083)
        ·
          refine ⟨85419889729948214087637125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56946593153298809391758083 85419889729948214087637125)
          ·
            refine ⟨16016229324365290141431961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85419889729948214087637125 16016229324365290141431961)
            ·
              refine ⟨12012171993273967606073971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16016229324365290141431961 12012171993273967606073971)
              ·
                refine ⟨18018257989910951409110957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12012171993273967606073971 18018257989910951409110957)
                ·
                  refine ⟨6756846746216606778416609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18018257989910951409110957 6756846746216606778416609)
                  ·
                    refine ⟨5067635059662455083812457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6756846746216606778416609 5067635059662455083812457)
                    ·
                      refine ⟨3800726294746841312859343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067635059662455083812457 3800726294746841312859343)
                      ·
                        rfl

theorem cell23_7401888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_7401888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401888 prefixEnd_7401888 := by exact prefixLift 7401888
  have htrace : WordTrace (prefixWord ++ tailWord_7401888) baseStart_7401888 baseEnd_7401888 := by
    simpa [prefixWord, tailWord_7401888, baseEnd_7401888] using wordTrace_append hprefix tailTrace_7401888
  have hstable : (prefixWord ++ tailWord_7401888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401888).length < 2 ^ (prefixWord ++ tailWord_7401888).sum := by decide
  have hdescent : baseEnd_7401888 < baseStart_7401888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401901 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_7401901 : Nat := 118140960795 + 7401901 * 2 ^ 59
def prefixEnd_7401901 : Nat := 4983230072969 + 3 ^ 40 * 7401901 * 2
def baseEnd_7401901 : Nat := 3800732969995349761996783

theorem tailTrace_7401901 : CollatzResearch.WordTrace tailWord_7401901 prefixEnd_7401901 3800732969995349761996783 := by
  unfold tailWord_7401901
  simp only [CollatzResearch.WordTrace]
  refine ⟨269969508357184295892261557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179979672238122863928174371 269969508357184295892261557)
  ·
    refine ⟨25309641408486027739899521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269969508357184295892261557 25309641408486027739899521)
    ·
      refine ⟨18982231056364520804924641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25309641408486027739899521 18982231056364520804924641)
      ·
        refine ⟨14236673292273390603693481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18982231056364520804924641 14236673292273390603693481)
        ·
          refine ⟨10677504969205042952770111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14236673292273390603693481 10677504969205042952770111)
          ·
            refine ⟨16016257453807564429155167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10677504969205042952770111 16016257453807564429155167)
            ·
              refine ⟨24024386180711346643732751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16016257453807564429155167 24024386180711346643732751)
              ·
                refine ⟨36036579271067019965599127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24024386180711346643732751 36036579271067019965599127)
                ·
                  refine ⟨54054868906600529948398691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36036579271067019965599127 54054868906600529948398691)
                  ·
                    refine ⟨81082303359900794922598037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54054868906600529948398691 81082303359900794922598037)
                    ·
                      refine ⟨3800732969995349761996783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81082303359900794922598037 3800732969995349761996783)
                      ·
                        rfl

theorem cell23_7401901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_7401901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401901 prefixEnd_7401901 := by exact prefixLift 7401901
  have htrace : WordTrace (prefixWord ++ tailWord_7401901) baseStart_7401901 baseEnd_7401901 := by
    simpa [prefixWord, tailWord_7401901, baseEnd_7401901] using wordTrace_append hprefix tailTrace_7401901
  have hstable : (prefixWord ++ tailWord_7401901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401901).length < 2 ^ (prefixWord ++ tailWord_7401901).sum := by decide
  have hdescent : baseEnd_7401901 < baseStart_7401901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401914 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2]
def baseStart_7401914 : Nat := 118140960795 + 7401914 * 2 ^ 59
def prefixEnd_7401914 : Nat := 4983230072969 + 3 ^ 40 * 7401914 * 2
def baseEnd_7401914 : Nat := 3800739645243858211134223

theorem tailTrace_7401914 : CollatzResearch.WordTrace tailWord_7401914 prefixEnd_7401914 3800739645243858211134223 := by
  unfold tailWord_7401914
  simp only [CollatzResearch.WordTrace]
  refine ⟨67492495626534299778121199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179979988337424799408323197 67492495626534299778121199)
  ·
    refine ⟨101238743439801449667181799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67492495626534299778121199 101238743439801449667181799)
    ·
      refine ⟨151858115159702174500772699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101238743439801449667181799 151858115159702174500772699)
      ·
        refine ⟨227787172739553261751159049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151858115159702174500772699 227787172739553261751159049)
        ·
          refine ⟨170840379554664946313369287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227787172739553261751159049 170840379554664946313369287)
          ·
            refine ⟨256260569331997419470053931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170840379554664946313369287 256260569331997419470053931)
            ·
              refine ⟨384390853997996129205080897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256260569331997419470053931 384390853997996129205080897)
              ·
                refine ⟨288293140498497096903810673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384390853997996129205080897 288293140498497096903810673)
                ·
                  refine ⟨216219855373872822677858005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288293140498497096903810673 216219855373872822677858005)
                  ·
                    refine ⟨5067652860325144281512297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 216219855373872822677858005 5067652860325144281512297)
                    ·
                      refine ⟨3800739645243858211134223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067652860325144281512297 3800739645243858211134223)
                      ·
                        rfl

theorem cell23_7401914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2].length) (baseStart_7401914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401914 prefixEnd_7401914 := by exact prefixLift 7401914
  have htrace : WordTrace (prefixWord ++ tailWord_7401914) baseStart_7401914 baseEnd_7401914 := by
    simpa [prefixWord, tailWord_7401914, baseEnd_7401914] using wordTrace_append hprefix tailTrace_7401914
  have hstable : (prefixWord ++ tailWord_7401914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401914).length < 2 ^ (prefixWord ++ tailWord_7401914).sum := by decide
  have hdescent : baseEnd_7401914 < baseStart_7401914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401937 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 4, 6]
def baseStart_7401937 : Nat := 118140960795 + 7401937 * 2 ^ 59
def prefixEnd_7401937 : Nat := 4983230072969 + 3 ^ 40 * 7401937 * 2
def baseEnd_7401937 : Nat := 1266917151766303873715539

theorem tailTrace_7401937 : CollatzResearch.WordTrace tailWord_7401937 prefixEnd_7401937 1266917151766303873715539 := by
  unfold tailWord_7401937
  simp only [CollatzResearch.WordTrace]
  refine ⟨269970821385053874040572065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179980547590035916027048043 269970821385053874040572065)
  ·
    refine ⟨202478116038790405530429049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269970821385053874040572065 202478116038790405530429049)
    ·
      refine ⟨151858587029092804147821787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202478116038790405530429049 151858587029092804147821787)
      ·
        refine ⟨227787880543639206221732681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151858587029092804147821787 227787880543639206221732681)
        ·
          refine ⟨170840910407729404666299511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227787880543639206221732681 170840910407729404666299511)
          ·
            refine ⟨256261365611594106999449267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170840910407729404666299511 256261365611594106999449267)
            ·
              refine ⟨384392048417391160499173901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256261365611594106999449267 384392048417391160499173901)
              ·
                refine ⟨144147018156521685187190213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384392048417391160499173901 144147018156521685187190213)
                ·
                  refine ⟨27027565904347815972598165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144147018156521685187190213 27027565904347815972598165)
                  ·
                    refine ⟨1266917151766303873715539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27027565904347815972598165 1266917151766303873715539)
                    ·
                      rfl

theorem cell23_7401937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_7401937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401937 prefixEnd_7401937 := by exact prefixLift 7401937
  have htrace : WordTrace (prefixWord ++ tailWord_7401937) baseStart_7401937 baseEnd_7401937 := by
    simpa [prefixWord, tailWord_7401937, baseEnd_7401937] using wordTrace_append hprefix tailTrace_7401937
  have hstable : (prefixWord ++ tailWord_7401937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401937).length < 2 ^ (prefixWord ++ tailWord_7401937).sum := by decide
  have hdescent : baseEnd_7401937 < baseStart_7401937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401961 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 6, 2, 2]
def baseStart_7401961 : Nat := 118140960795 + 7401961 * 2 ^ 59
def prefixEnd_7401961 : Nat := 4983230072969 + 3 ^ 40 * 7401961 * 2
def baseEnd_7401961 : Nat := 3800763778834619527246507

theorem tailTrace_7401961 : CollatzResearch.WordTrace tailWord_7401961 prefixEnd_7401961 3800763778834619527246507 := by
  unfold tailWord_7401961
  simp only [CollatzResearch.WordTrace]
  refine ⟨269971696736966926139445737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179981131157977950759630491 269971696736966926139445737)
  ·
    refine ⟨202478772552725194604584303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269971696736966926139445737 202478772552725194604584303)
    ·
      refine ⟨303718158829087791906876455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202478772552725194604584303 303718158829087791906876455)
      ·
        refine ⟨455577238243631687860314683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303718158829087791906876455 455577238243631687860314683)
        ·
          refine ⟨683365857365447531790472025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455577238243631687860314683 683365857365447531790472025)
          ·
            refine ⟨512524393024085648842854019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683365857365447531790472025 512524393024085648842854019)
            ·
              refine ⟨768786589536128473264281029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512524393024085648842854019 768786589536128473264281029)
              ·
                refine ⟨144147485538024088737052693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768786589536128473264281029 144147485538024088737052693)
                ·
                  refine ⟨6756913384594879159549345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144147485538024088737052693 6756913384594879159549345)
                  ·
                    refine ⟨5067685038446159369662009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6756913384594879159549345 5067685038446159369662009)
                    ·
                      refine ⟨3800763778834619527246507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067685038446159369662009 3800763778834619527246507)
                      ·
                        rfl

theorem cell23_7401961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 2, 2].length) (baseStart_7401961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401961 prefixEnd_7401961 := by exact prefixLift 7401961
  have htrace : WordTrace (prefixWord ++ tailWord_7401961) baseStart_7401961 baseEnd_7401961 := by
    simpa [prefixWord, tailWord_7401961, baseEnd_7401961] using wordTrace_append hprefix tailTrace_7401961
  have hstable : (prefixWord ++ tailWord_7401961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401961).length < 2 ^ (prefixWord ++ tailWord_7401961).sum := by decide
  have hdescent : baseEnd_7401961 < baseStart_7401961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401965 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_7401965 : Nat := 118140960795 + 7401965 * 2 ^ 59
def prefixEnd_7401965 : Nat := 4983230072969 + 3 ^ 40 * 7401965 * 2
def baseEnd_7401965 : Nat := 3800765832757237511596489

theorem tailTrace_7401965 : CollatzResearch.WordTrace tailWord_7401965 prefixEnd_7401965 3800765832757237511596489 := by
  unfold tailWord_7401965
  simp only [CollatzResearch.WordTrace]
  refine ⟨269971842628952434822591349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179981228419301623215060899 269971842628952434822591349)
  ·
    refine ⟨25309860246464290764617939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269971842628952434822591349 25309860246464290764617939)
    ·
      refine ⟨37964790369696436146926909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25309860246464290764617939 37964790369696436146926909)
      ·
        refine ⟨14236796388636163555097591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37964790369696436146926909 14236796388636163555097591)
        ·
          refine ⟨21355194582954245332646387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14236796388636163555097591 21355194582954245332646387)
          ·
            refine ⟨32032791874431367998969581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21355194582954245332646387 32032791874431367998969581)
            ·
              refine ⟨12012296952911762999613593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32032791874431367998969581 12012296952911762999613593)
              ·
                refine ⟨9009222714683822249710195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12012296952911762999613593 9009222714683822249710195)
                ·
                  refine ⟨13513834072025733374565293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9009222714683822249710195 13513834072025733374565293)
                  ·
                    refine ⟨5067687777009650015461985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13513834072025733374565293 5067687777009650015461985)
                    ·
                      refine ⟨3800765832757237511596489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067687777009650015461985 3800765832757237511596489)
                      ·
                        rfl

theorem cell23_7401965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_7401965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401965 prefixEnd_7401965 := by exact prefixLift 7401965
  have htrace : WordTrace (prefixWord ++ tailWord_7401965) baseStart_7401965 baseEnd_7401965 := by
    simpa [prefixWord, tailWord_7401965, baseEnd_7401965] using wordTrace_append hprefix tailTrace_7401965
  have hstable : (prefixWord ++ tailWord_7401965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401965).length < 2 ^ (prefixWord ++ tailWord_7401965).sum := by decide
  have hdescent : baseEnd_7401965 < baseStart_7401965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401967 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 9]
def baseStart_7401967 : Nat := 118140960795 + 7401967 * 2 ^ 59
def prefixEnd_7401967 : Nat := 4983230072969 + 3 ^ 40 * 7401967 * 2
def baseEnd_7401967 : Nat := 422307428857616278196831

theorem tailTrace_7401967 : CollatzResearch.WordTrace tailWord_7401967 prefixEnd_7401967 422307428857616278196831 := by
  unfold tailWord_7401967
  simp only [CollatzResearch.WordTrace]
  refine ⟨269971915574945189164164155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179981277049963459442776103 269971915574945189164164155)
  ·
    refine ⟨404957873362417783746246233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269971915574945189164164155 404957873362417783746246233)
    ·
      refine ⟨303718405021813337809684675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404957873362417783746246233 303718405021813337809684675)
      ·
        refine ⟨455577607532720006714527013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303718405021813337809684675 455577607532720006714527013)
        ·
          refine ⟨85420801412385001258973815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 455577607532720006714527013 85420801412385001258973815)
          ·
            refine ⟨128131202118577501888460723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85420801412385001258973815 128131202118577501888460723)
            ·
              refine ⟨192196803177866252832691085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128131202118577501888460723 192196803177866252832691085)
              ·
                refine ⟨72073801191699844812259157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192196803177866252832691085 72073801191699844812259157)
                ·
                  refine ⟨422307428857616278196831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72073801191699844812259157 422307428857616278196831)
                  ·
                    rfl

theorem cell23_7401967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 9].length) (baseStart_7401967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401967 prefixEnd_7401967 := by exact prefixLift 7401967
  have htrace : WordTrace (prefixWord ++ tailWord_7401967) baseStart_7401967 baseEnd_7401967 := by
    simpa [prefixWord, tailWord_7401967, baseEnd_7401967] using wordTrace_append hprefix tailTrace_7401967
  have hstable : (prefixWord ++ tailWord_7401967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401967).length < 2 ^ (prefixWord ++ tailWord_7401967).sum := by decide
  have hdescent : baseEnd_7401967 < baseStart_7401967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7401995 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 2, 2, 2]
def baseStart_7401995 : Nat := 118140960795 + 7401995 * 2 ^ 59
def prefixEnd_7401995 : Nat := 4983230072969 + 3 ^ 40 * 7401995 * 2
def baseEnd_7401995 : Nat := 3800781237176872394221351

theorem tailTrace_7401995 : CollatzResearch.WordTrace tailWord_7401995 prefixEnd_7401995 3800781237176872394221351 := by
  unfold tailWord_7401995
  simp only [CollatzResearch.WordTrace]
  refine ⟨269972936818843749946183439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179981957879229166630788959 269972936818843749946183439)
  ·
    refine ⟨404959405228265624919275159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269972936818843749946183439 404959405228265624919275159)
    ·
      refine ⟨607439107842398437378912739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404959405228265624919275159 607439107842398437378912739)
      ·
        refine ⟨911158661763597656068369109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607439107842398437378912739 911158661763597656068369109)
        ·
          refine ⟨21355281135084320064102401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 911158661763597656068369109 21355281135084320064102401)
          ·
            refine ⟨16016460851313240048076801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21355281135084320064102401 16016460851313240048076801)
            ·
              refine ⟨12012345638484930036057601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16016460851313240048076801 12012345638484930036057601)
              ·
                refine ⟨9009259228863697527043201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12012345638484930036057601 9009259228863697527043201)
                ·
                  refine ⟨6756944421647773145282401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9009259228863697527043201 6756944421647773145282401)
                  ·
                    refine ⟨5067708316235829858961801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6756944421647773145282401 5067708316235829858961801)
                    ·
                      refine ⟨3800781237176872394221351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067708316235829858961801 3800781237176872394221351)
                      ·
                        rfl

theorem cell23_7401995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 2, 2].length) (baseStart_7401995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7401995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7401995 prefixEnd_7401995 := by exact prefixLift 7401995
  have htrace : WordTrace (prefixWord ++ tailWord_7401995) baseStart_7401995 baseEnd_7401995 := by
    simpa [prefixWord, tailWord_7401995, baseEnd_7401995] using wordTrace_append hprefix tailTrace_7401995
  have hstable : (prefixWord ++ tailWord_7401995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7401995).length < 2 ^ (prefixWord ++ tailWord_7401995).sum := by decide
  have hdescent : baseEnd_7401995 < baseStart_7401995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7401995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402046 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_7402046 : Nat := 118140960795 + 7402046 * 2 ^ 59
def prefixEnd_7402046 : Nat := 4983230072969 + 3 ^ 40 * 7402046 * 2
def baseEnd_7402046 : Nat := 3800807424690251694683617

theorem tailTrace_7402046 : CollatzResearch.WordTrace tailWord_7402046 prefixEnd_7402046 3800807424690251694683617 := by
  unfold tailWord_7402046
  simp only [CollatzResearch.WordTrace]
  refine ⟨33746849617707373207036249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179983197961105990437526661 33746849617707373207036249)
  ·
    refine ⟨25310137213280529905277187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33746849617707373207036249 25310137213280529905277187)
    ·
      refine ⟨37965205819920794857915781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25310137213280529905277187 37965205819920794857915781)
      ·
        refine ⟨7118476091235149035859209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37965205819920794857915781 7118476091235149035859209)
        ·
          refine ⟨5338857068426361776894407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7118476091235149035859209 5338857068426361776894407)
          ·
            refine ⟨8008285602639542665341611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338857068426361776894407 8008285602639542665341611)
            ·
              refine ⟨12012428403959313998012417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8008285602639542665341611 12012428403959313998012417)
              ·
                refine ⟨9009321302969485498509313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12012428403959313998012417 9009321302969485498509313)
                ·
                  refine ⟨6756990977227114123881985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9009321302969485498509313 6756990977227114123881985)
                  ·
                    refine ⟨5067743232920335592911489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6756990977227114123881985 5067743232920335592911489)
                    ·
                      refine ⟨3800807424690251694683617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067743232920335592911489 3800807424690251694683617)
                      ·
                        rfl

theorem cell23_7402046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_7402046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402046 prefixEnd_7402046 := by exact prefixLift 7402046
  have htrace : WordTrace (prefixWord ++ tailWord_7402046) baseStart_7402046 baseEnd_7402046 := by
    simpa [prefixWord, tailWord_7402046, baseEnd_7402046] using wordTrace_append hprefix tailTrace_7402046
  have hstable : (prefixWord ++ tailWord_7402046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402046).length < 2 ^ (prefixWord ++ tailWord_7402046).sum := by decide
  have hdescent : baseEnd_7402046 < baseStart_7402046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402068 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_7402068 : Nat := 118140960795 + 7402068 * 2 ^ 59
def prefixEnd_7402068 : Nat := 4983230072969 + 3 ^ 40 * 7402068 * 2
def baseEnd_7402068 : Nat := 3800818721264650608608515

theorem tailTrace_7402068 : CollatzResearch.WordTrace tailWord_7402068 prefixEnd_7402068 3800818721264650608608515 := by
  unfold tailWord_7402068
  simp only [CollatzResearch.WordTrace]
  refine ⟨134987799673789641706795429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179983732898386188942393905 134987799673789641706795429)
  ·
    refine ⟨25310212438835557820024143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134987799673789641706795429 25310212438835557820024143)
    ·
      refine ⟨37965318658253336730036215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25310212438835557820024143 37965318658253336730036215)
      ·
        refine ⟨56947977987380005095054323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37965318658253336730036215 56947977987380005095054323)
        ·
          refine ⟨85421966981070007642581485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56947977987380005095054323 85421966981070007642581485)
          ·
            refine ⟨32033237617901252865968057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85421966981070007642581485 32033237617901252865968057)
            ·
              refine ⟨24024928213425939649476043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32033237617901252865968057 24024928213425939649476043)
              ·
                refine ⟨36037392320138909474214065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24024928213425939649476043 36037392320138909474214065)
                ·
                  refine ⟨27028044240104182105660549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36037392320138909474214065 27028044240104182105660549)
                  ·
                    refine ⟨5067758295019534144811353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27028044240104182105660549 5067758295019534144811353)
                    ·
                      refine ⟨3800818721264650608608515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067758295019534144811353 3800818721264650608608515)
                      ·
                        rfl

theorem cell23_7402068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_7402068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402068 prefixEnd_7402068 := by exact prefixLift 7402068
  have htrace : WordTrace (prefixWord ++ tailWord_7402068) baseStart_7402068 baseEnd_7402068 := by
    simpa [prefixWord, tailWord_7402068, baseEnd_7402068] using wordTrace_append hprefix tailTrace_7402068
  have hstable : (prefixWord ++ tailWord_7402068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402068).length < 2 ^ (prefixWord ++ tailWord_7402068).sum := by decide
  have hdescent : baseEnd_7402068 < baseStart_7402068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402111 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 3, 5, 2]
def baseStart_7402111 : Nat := 118140960795 + 7402111 * 2 ^ 59
def prefixEnd_7402111 : Nat := 4983230072969 + 3 ^ 40 * 7402111 * 2
def baseEnd_7402111 : Nat := 3800840800932793940370817

theorem tailTrace_7402111 : CollatzResearch.WordTrace tailWord_7402111 prefixEnd_7402111 3800840800932793940370817 := by
  unfold tailWord_7402111
  simp only [CollatzResearch.WordTrace]
  refine ⟨269977167686423501757406187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179984778457615667838270791 269977167686423501757406187)
  ·
    refine ⟨404965751529635252636109281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269977167686423501757406187 404965751529635252636109281)
    ·
      refine ⟨303724313647226439477081961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404965751529635252636109281 303724313647226439477081961)
      ·
        refine ⟨227793235235419829607811471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303724313647226439477081961 227793235235419829607811471)
        ·
          refine ⟨341689852853129744411717207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227793235235419829607811471 341689852853129744411717207)
          ·
            refine ⟨512534779279694616617575811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341689852853129744411717207 512534779279694616617575811)
            ·
              refine ⟨768802168919541924926363717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512534779279694616617575811 768802168919541924926363717)
              ·
                refine ⟨144150406672414110923693197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768802168919541924926363717 144150406672414110923693197)
                ·
                  refine ⟨54056402502155291596384949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144150406672414110923693197 54056402502155291596384949)
                  ·
                    refine ⟨5067787734577058587161089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54056402502155291596384949 5067787734577058587161089)
                    ·
                      refine ⟨3800840800932793940370817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067787734577058587161089 3800840800932793940370817)
                      ·
                        rfl

theorem cell23_7402111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 5, 2].length) (baseStart_7402111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402111 prefixEnd_7402111 := by exact prefixLift 7402111
  have htrace : WordTrace (prefixWord ++ tailWord_7402111) baseStart_7402111 baseEnd_7402111 := by
    simpa [prefixWord, tailWord_7402111, baseEnd_7402111] using wordTrace_append hprefix tailTrace_7402111
  have hstable : (prefixWord ++ tailWord_7402111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402111).length < 2 ^ (prefixWord ++ tailWord_7402111).sum := by decide
  have hdescent : baseEnd_7402111 < baseStart_7402111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402188 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7402188 : Nat := 118140960795 + 7402188 * 2 ^ 59
def prefixEnd_7402188 : Nat := 4983230072969 + 3 ^ 40 * 7402188 * 2
def baseEnd_7402188 : Nat := 3800880338943190139107963

theorem tailTrace_7402188 : CollatzResearch.WordTrace tailWord_7402188 prefixEnd_7402188 3800880338943190139107963 := by
  unfold tailWord_7402188
  simp only [CollatzResearch.WordTrace]
  refine ⟨134989988053572271953979609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179986650738096362605306145 134989988053572271953979609)
  ·
    refine ⟨101242491040179203965484707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134989988053572271953979609 101242491040179203965484707)
    ·
      refine ⟨151863736560268805948227061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101242491040179203965484707 151863736560268805948227061)
      ·
        refine ⟨14237225302525200557646287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151863736560268805948227061 14237225302525200557646287)
        ·
          refine ⟨21355837953787800836469431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14237225302525200557646287 21355837953787800836469431)
          ·
            refine ⟨32033756930681701254704147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21355837953787800836469431 32033756930681701254704147)
            ·
              refine ⟨48050635396022551882056221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32033756930681701254704147 48050635396022551882056221)
              ·
                refine ⟨18018988273508456955771083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48050635396022551882056221 18018988273508456955771083)
                ·
                  refine ⟨27028482410262685433656625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18018988273508456955771083 27028482410262685433656625)
                  ·
                    refine ⟨20271361807697014075242469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27028482410262685433656625 20271361807697014075242469)
                    ·
                      refine ⟨3800880338943190139107963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20271361807697014075242469 3800880338943190139107963)
                      ·
                        rfl

theorem cell23_7402188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7402188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402188 prefixEnd_7402188 := by exact prefixLift 7402188
  have htrace : WordTrace (prefixWord ++ tailWord_7402188) baseStart_7402188 baseEnd_7402188 := by
    simpa [prefixWord, tailWord_7402188, baseEnd_7402188] using wordTrace_append hprefix tailTrace_7402188
  have hstable : (prefixWord ++ tailWord_7402188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402188).length < 2 ^ (prefixWord ++ tailWord_7402188).sum := by decide
  have hdescent : baseEnd_7402188 < baseStart_7402188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402208 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 4, 1, 3]
def baseStart_7402208 : Nat := 118140960795 + 7402208 * 2 ^ 59
def prefixEnd_7402208 : Nat := 4983230072969 + 3 ^ 40 * 7402208 * 2
def baseEnd_7402208 : Nat := 3800890608556280060857871

theorem tailTrace_7402208 : CollatzResearch.WordTrace tailWord_7402208 prefixEnd_7402208 3800890608556280060857871 := by
  unfold tailWord_7402208
  simp only [CollatzResearch.WordTrace]
  refine ⟨134990352783536043661843639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179987137044714724882458185 134990352783536043661843639)
  ·
    refine ⟨202485529175304065492765459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134990352783536043661843639 202485529175304065492765459)
    ·
      refine ⟨303728293762956098239148189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202485529175304065492765459 303728293762956098239148189)
      ·
        refine ⟨113898110161108536839680571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303728293762956098239148189 113898110161108536839680571)
        ·
          refine ⟨170847165241662805259520857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113898110161108536839680571 170847165241662805259520857)
          ·
            refine ⟨128135373931247103944640643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170847165241662805259520857 128135373931247103944640643)
            ·
              refine ⟨192203060896870655916960965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128135373931247103944640643 192203060896870655916960965)
              ·
                refine ⟨36038073918163247984430181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192203060896870655916960965 36038073918163247984430181)
                ·
                  refine ⟨6757138859655608997080659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36038073918163247984430181 6757138859655608997080659)
                  ·
                    refine ⟨10135708289483413495620989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6757138859655608997080659 10135708289483413495620989)
                    ·
                      refine ⟨3800890608556280060857871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10135708289483413495620989 3800890608556280060857871)
                      ·
                        rfl

theorem cell23_7402208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_7402208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402208 prefixEnd_7402208 := by exact prefixLift 7402208
  have htrace : WordTrace (prefixWord ++ tailWord_7402208) baseStart_7402208 baseEnd_7402208 := by
    simpa [prefixWord, tailWord_7402208, baseEnd_7402208] using wordTrace_append hprefix tailTrace_7402208
  have hstable : (prefixWord ++ tailWord_7402208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402208).length < 2 ^ (prefixWord ++ tailWord_7402208).sum := by decide
  have hdescent : baseEnd_7402208 < baseStart_7402208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402209 : List Nat := [1, 2, 3, 1, 4, 2, 2, 3, 1, 2, 2]
def baseStart_7402209 : Nat := 118140960795 + 7402209 * 2 ^ 59
def prefixEnd_7402209 : Nat := 4983230072969 + 3 ^ 40 * 7402209 * 2
def baseEnd_7402209 : Nat := 3800891122036934556945367

theorem tailTrace_7402209 : CollatzResearch.WordTrace tailWord_7402209 prefixEnd_7402209 3800891122036934556945367 := by
  unfold tailWord_7402209
  simp only [CollatzResearch.WordTrace]
  refine ⟨269980742040068464494473681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179987161360045642996315787 269980742040068464494473681)
  ·
    refine ⟨202485556530051348370855261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269980742040068464494473681 202485556530051348370855261)
    ·
      refine ⟨75932083698769255639070723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202485556530051348370855261 75932083698769255639070723)
      ·
        refine ⟨113898125548153883458606085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75932083698769255639070723 113898125548153883458606085)
        ·
          refine ⟨21355898540278853148488641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113898125548153883458606085 21355898540278853148488641)
          ·
            refine ⟨16016923905209139861366481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21355898540278853148488641 16016923905209139861366481)
            ·
              refine ⟨12012692928906854896024861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16016923905209139861366481 12012692928906854896024861)
              ·
                refine ⟨4504759848340070586009323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12012692928906854896024861 4504759848340070586009323)
                ·
                  refine ⟨6757139772510105879013985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504759848340070586009323 6757139772510105879013985)
                  ·
                    refine ⟨5067854829382579409260489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6757139772510105879013985 5067854829382579409260489)
                    ·
                      refine ⟨3800891122036934556945367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067854829382579409260489 3800891122036934556945367)
                      ·
                        rfl

theorem cell23_7402209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_7402209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402209 prefixEnd_7402209 := by exact prefixLift 7402209
  have htrace : WordTrace (prefixWord ++ tailWord_7402209) baseStart_7402209 baseEnd_7402209 := by
    simpa [prefixWord, tailWord_7402209, baseEnd_7402209] using wordTrace_append hprefix tailTrace_7402209
  have hstable : (prefixWord ++ tailWord_7402209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402209).length < 2 ^ (prefixWord ++ tailWord_7402209).sum := by decide
  have hdescent : baseEnd_7402209 < baseStart_7402209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402212 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 1, 2, 3]
def baseStart_7402212 : Nat := 118140960795 + 7402212 * 2 ^ 59
def prefixEnd_7402212 : Nat := 4983230072969 + 3 ^ 40 * 7402212 * 2
def baseEnd_7402212 : Nat := 3800892662478898045207853

theorem tailTrace_7402212 : CollatzResearch.WordTrace tailWord_7402212 prefixEnd_7402212 3800892662478898045207853 := by
  unfold tailWord_7402212
  simp only [CollatzResearch.WordTrace]
  refine ⟨134990425729528798003416445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179987234306038397337888593 134990425729528798003416445)
  ·
    refine ⟨50621409648573299251281167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134990425729528798003416445 50621409648573299251281167)
    ·
      refine ⟨75932114472859948876921751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50621409648573299251281167 75932114472859948876921751)
      ·
        refine ⟨113898171709289923315382627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75932114472859948876921751 113898171709289923315382627)
        ·
          refine ⟨170847257563934884973073941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113898171709289923315382627 170847257563934884973073941)
          ·
            refine ⟨8008465198309447733112841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170847257563934884973073941 8008465198309447733112841)
            ·
              refine ⟨6006348898732085799834631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8008465198309447733112841 6006348898732085799834631)
              ·
                refine ⟨9009523348098128699751947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006348898732085799834631 9009523348098128699751947)
                ·
                  refine ⟨13514285022147193049627921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9009523348098128699751947 13514285022147193049627921)
                  ·
                    refine ⟨10135713766610394787220941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13514285022147193049627921 10135713766610394787220941)
                    ·
                      refine ⟨3800892662478898045207853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10135713766610394787220941 3800892662478898045207853)
                      ·
                        rfl

theorem cell23_7402212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_7402212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402212 prefixEnd_7402212 := by exact prefixLift 7402212
  have htrace : WordTrace (prefixWord ++ tailWord_7402212) baseStart_7402212 baseEnd_7402212 := by
    simpa [prefixWord, tailWord_7402212, baseEnd_7402212] using wordTrace_append hprefix tailTrace_7402212
  have hstable : (prefixWord ++ tailWord_7402212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402212).length < 2 ^ (prefixWord ++ tailWord_7402212).sum := by decide
  have hdescent : baseEnd_7402212 < baseStart_7402212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402242 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_7402242 : Nat := 118140960795 + 7402242 * 2 ^ 59
def prefixEnd_7402242 : Nat := 4983230072969 + 3 ^ 40 * 7402242 * 2
def baseEnd_7402242 : Nat := 3800908066898532927832715

theorem tailTrace_7402242 : CollatzResearch.WordTrace tailWord_7402242 prefixEnd_7402242 3800908066898532927832715 := by
  unfold tailWord_7402242
  simp only [CollatzResearch.WordTrace]
  refine ⟨67495486412237227782606245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179987963765965940753616653 67495486412237227782606245)
  ·
    refine ⟨12655403702294480209238671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67495486412237227782606245 12655403702294480209238671)
    ·
      refine ⟨18983105553441720313858007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12655403702294480209238671 18983105553441720313858007)
      ·
        refine ⟨28474658330162580470787011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18983105553441720313858007 28474658330162580470787011)
        ·
          refine ⟨42711987495243870706180517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28474658330162580470787011 42711987495243870706180517)
          ·
            refine ⟨8008497655358225757408847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42711987495243870706180517 8008497655358225757408847)
            ·
              refine ⟨12012746483037338636113271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8008497655358225757408847 12012746483037338636113271)
              ·
                refine ⟨18019119724556007954169907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12012746483037338636113271 18019119724556007954169907)
                ·
                  refine ⟨27028679586834011931254861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18019119724556007954169907 27028679586834011931254861)
                  ·
                    refine ⟨10135754845062754474220573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27028679586834011931254861 10135754845062754474220573)
                    ·
                      refine ⟨3800908066898532927832715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10135754845062754474220573 3800908066898532927832715)
                      ·
                        rfl

theorem cell23_7402242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_7402242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402242 prefixEnd_7402242 := by exact prefixLift 7402242
  have htrace : WordTrace (prefixWord ++ tailWord_7402242) baseStart_7402242 baseEnd_7402242 := by
    simpa [prefixWord, tailWord_7402242, baseEnd_7402242] using wordTrace_append hprefix tailTrace_7402242
  have hstable : (prefixWord ++ tailWord_7402242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402242).length < 2 ^ (prefixWord ++ tailWord_7402242).sum := by decide
  have hdescent : baseEnd_7402242 < baseStart_7402242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402251 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 5]
def baseStart_7402251 : Nat := 118140960795 + 7402251 * 2 ^ 59
def prefixEnd_7402251 : Nat := 4983230072969 + 3 ^ 40 * 7402251 * 2
def baseEnd_7402251 : Nat := 3800912688224423392620173

theorem tailTrace_7402251 : CollatzResearch.WordTrace tailWord_7402251 prefixEnd_7402251 3800912688224423392620173 := by
  unfold tailWord_7402251
  simp only [CollatzResearch.WordTrace]
  refine ⟨269982273905916305667502607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179988182603944203778335071 269982273905916305667502607)
  ·
    refine ⟨404973410858874458501253911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269982273905916305667502607 404973410858874458501253911)
    ·
      refine ⟨607460116288311687751880867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404973410858874458501253911 607460116288311687751880867)
      ·
        refine ⟨911190174432467531627821301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607460116288311687751880867 911190174432467531627821301)
        ·
          refine ⟨85424078853043831090108247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 911190174432467531627821301 85424078853043831090108247)
          ·
            refine ⟨128136118279565746635162371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85424078853043831090108247 128136118279565746635162371)
            ·
              refine ⟨192204177419348619952743557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128136118279565746635162371 192204177419348619952743557)
              ·
                refine ⟨36038283266127866241139417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192204177419348619952743557 36038283266127866241139417)
                ·
                  refine ⟨27028712449595899680854563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36038283266127866241139417 27028712449595899680854563)
                  ·
                    refine ⟨40543068674393849521281845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27028712449595899680854563 40543068674393849521281845)
                    ·
                      refine ⟨3800912688224423392620173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40543068674393849521281845 3800912688224423392620173)
                      ·
                        rfl

theorem cell23_7402251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 5].length) (baseStart_7402251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402251 prefixEnd_7402251 := by exact prefixLift 7402251
  have htrace : WordTrace (prefixWord ++ tailWord_7402251) baseStart_7402251 baseEnd_7402251 := by
    simpa [prefixWord, tailWord_7402251, baseEnd_7402251] using wordTrace_append hprefix tailTrace_7402251
  have hstable : (prefixWord ++ tailWord_7402251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402251).length < 2 ^ (prefixWord ++ tailWord_7402251).sum := by decide
  have hdescent : baseEnd_7402251 < baseStart_7402251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402268 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_7402268 : Nat := 118140960795 + 7402268 * 2 ^ 59
def prefixEnd_7402268 : Nat := 4983230072969 + 3 ^ 40 * 7402268 * 2
def baseEnd_7402268 : Nat := 3800921417395549826107595

theorem tailTrace_7402268 : CollatzResearch.WordTrace tailWord_7402268 prefixEnd_7402268 3800921417395549826107595 := by
  unfold tailWord_7402268
  simp only [CollatzResearch.WordTrace]
  refine ⟨134991446973427358785435729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179988595964569811713914305 134991446973427358785435729)
  ·
    refine ⟨101243585230070519089076797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134991446973427358785435729 101243585230070519089076797)
    ·
      refine ⟨37966344461276444658403799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101243585230070519089076797 37966344461276444658403799)
      ·
        refine ⟨56949516691914666987605699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37966344461276444658403799 56949516691914666987605699)
        ·
          refine ⟨85424275037872000481408549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56949516691914666987605699 85424275037872000481408549)
          ·
            refine ⟨16017051569601000090264103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85424275037872000481408549 16017051569601000090264103)
            ·
              refine ⟨24025577354401500135396155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16017051569601000090264103 24025577354401500135396155)
              ·
                refine ⟨36038366031602250203094233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24025577354401500135396155 36038366031602250203094233)
                ·
                  refine ⟨27028774523701687652320675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36038366031602250203094233 27028774523701687652320675)
                  ·
                    refine ⟨40543161785552531478481013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27028774523701687652320675 40543161785552531478481013)
                    ·
                      refine ⟨3800921417395549826107595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40543161785552531478481013 3800921417395549826107595)
                      ·
                        rfl

theorem cell23_7402268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_7402268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402268 prefixEnd_7402268 := by exact prefixLift 7402268
  have htrace : WordTrace (prefixWord ++ tailWord_7402268) baseStart_7402268 baseEnd_7402268 := by
    simpa [prefixWord, tailWord_7402268, baseEnd_7402268] using wordTrace_append hprefix tailTrace_7402268
  have hstable : (prefixWord ++ tailWord_7402268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402268).length < 2 ^ (prefixWord ++ tailWord_7402268).sum := by decide
  have hdescent : baseEnd_7402268 < baseStart_7402268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402288 : List Nat := [2, 1, 1, 1, 2, 2, 1, 8, 5]
def baseStart_7402288 : Nat := 118140960795 + 7402288 * 2 ^ 59
def prefixEnd_7402288 : Nat := 4983230072969 + 3 ^ 40 * 7402288 * 2
def baseEnd_7402288 : Nat := 422325743000959971984167

theorem tailTrace_7402288 : CollatzResearch.WordTrace tailWord_7402288 prefixEnd_7402288 422325743000959971984167 := by
  unfold tailWord_7402288
  simp only [CollatzResearch.WordTrace]
  refine ⟨134991811703391130493299759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179989082271188173991066345 134991811703391130493299759)
  ·
    refine ⟨202487717555086695739949639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134991811703391130493299759 202487717555086695739949639)
    ·
      refine ⟨303731576332630043609924459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202487717555086695739949639 303731576332630043609924459)
      ·
        refine ⟨455597364498945065414886689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303731576332630043609924459 455597364498945065414886689)
        ·
          refine ⟨341698023374208799061165017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455597364498945065414886689 341698023374208799061165017)
          ·
            refine ⟨256273517530656599295873763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341698023374208799061165017 256273517530656599295873763)
            ·
              refine ⟨384410276295984898943810645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256273517530656599295873763 384410276295984898943810645)
              ·
                refine ⟨4504807925343573034497781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 384410276295984898943810645 4504807925343573034497781)
                ·
                  refine ⟨422325743000959971984167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4504807925343573034497781 422325743000959971984167)
                  ·
                    rfl

theorem cell23_7402288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 5].length) (baseStart_7402288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402288 prefixEnd_7402288 := by exact prefixLift 7402288
  have htrace : WordTrace (prefixWord ++ tailWord_7402288) baseStart_7402288 baseEnd_7402288 := by
    simpa [prefixWord, tailWord_7402288, baseEnd_7402288] using wordTrace_append hprefix tailTrace_7402288
  have hstable : (prefixWord ++ tailWord_7402288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402288).length < 2 ^ (prefixWord ++ tailWord_7402288).sum := by decide
  have hdescent : baseEnd_7402288 < baseStart_7402288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402311 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_7402311 : Nat := 118140960795 + 7402311 * 2 ^ 59
def prefixEnd_7402311 : Nat := 4983230072969 + 3 ^ 40 * 7402311 * 2
def baseEnd_7402311 : Nat := 3800943497063693157869897

theorem tailTrace_7402311 : CollatzResearch.WordTrace tailWord_7402311 prefixEnd_7402311 3800943497063693157869897 := by
  unfold tailWord_7402311
  simp only [CollatzResearch.WordTrace]
  refine ⟨269984462285698935914686787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179989641523799290609791191 269984462285698935914686787)
  ·
    refine ⟨404976693428548403872030181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269984462285698935914686787 404976693428548403872030181)
    ·
      refine ⟨75933130017852825726005659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404976693428548403872030181 75933130017852825726005659)
      ·
        refine ⟨113899695026779238589008489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75933130017852825726005659 113899695026779238589008489)
        ·
          refine ⟨85424771270084428941756367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113899695026779238589008489 85424771270084428941756367)
          ·
            refine ⟨128137156905126643412634551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85424771270084428941756367 128137156905126643412634551)
            ·
              refine ⟨192205735357689965118951827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128137156905126643412634551 192205735357689965118951827)
              ·
                refine ⟨288308603036534947678427741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192205735357689965118951827 288308603036534947678427741)
                ·
                  refine ⟨108115726138700605379410403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288308603036534947678427741 108115726138700605379410403)
                  ·
                    refine ⟨162173589208050908069115605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108115726138700605379410403 162173589208050908069115605)
                    ·
                      refine ⟨3800943497063693157869897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162173589208050908069115605 3800943497063693157869897)
                      ·
                        rfl

theorem cell23_7402311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_7402311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402311 prefixEnd_7402311 := by exact prefixLift 7402311
  have htrace : WordTrace (prefixWord ++ tailWord_7402311) baseStart_7402311 baseEnd_7402311 := by
    simpa [prefixWord, tailWord_7402311, baseEnd_7402311] using wordTrace_append hprefix tailTrace_7402311
  have hstable : (prefixWord ++ tailWord_7402311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402311).length < 2 ^ (prefixWord ++ tailWord_7402311).sum := by decide
  have hdescent : baseEnd_7402311 < baseStart_7402311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402375 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_7402375 : Nat := 118140960795 + 7402375 * 2 ^ 59
def prefixEnd_7402375 : Nat := 4983230072969 + 3 ^ 40 * 7402375 * 2
def baseEnd_7402375 : Nat := 3800976359825580907469603

theorem tailTrace_7402375 : CollatzResearch.WordTrace tailWord_7402375 prefixEnd_7402375 3800976359825580907469603 := by
  unfold tailWord_7402375
  simp only [CollatzResearch.WordTrace]
  refine ⟨269986796557467074845016579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179991197704978049896677719 269986796557467074845016579)
  ·
    refine ⟨404980194836200612267524869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269986796557467074845016579 404980194836200612267524869)
    ·
      refine ⟨75933786531787614800160913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404980194836200612267524869 75933786531787614800160913)
      ·
        refine ⟨56950339898840711100120685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75933786531787614800160913 56950339898840711100120685)
        ·
          refine ⟨21356377462065266662545257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56950339898840711100120685 21356377462065266662545257)
          ·
            refine ⟨16017283096548949996908943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21356377462065266662545257 16017283096548949996908943)
            ·
              refine ⟨24025924644823424995363415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16017283096548949996908943 24025924644823424995363415)
              ·
                refine ⟨36038886967235137493045123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24025924644823424995363415 36038886967235137493045123)
                ·
                  refine ⟨54058330450852706239567685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36038886967235137493045123 54058330450852706239567685)
                  ·
                    refine ⟨10135936959534882419918941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54058330450852706239567685 10135936959534882419918941)
                    ·
                      refine ⟨3800976359825580907469603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10135936959534882419918941 3800976359825580907469603)
                      ·
                        rfl

theorem cell23_7402375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_7402375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402375 prefixEnd_7402375 := by exact prefixLift 7402375
  have htrace : WordTrace (prefixWord ++ tailWord_7402375) baseStart_7402375 baseEnd_7402375 := by
    simpa [prefixWord, tailWord_7402375, baseEnd_7402375] using wordTrace_append hprefix tailTrace_7402375
  have hstable : (prefixWord ++ tailWord_7402375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402375).length < 2 ^ (prefixWord ++ tailWord_7402375).sum := by decide
  have hdescent : baseEnd_7402375 < baseStart_7402375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402415 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 6, 3, 2]
def baseStart_7402415 : Nat := 118140960795 + 7402415 * 2 ^ 59
def prefixEnd_7402415 : Nat := 4983230072969 + 3 ^ 40 * 7402415 * 2
def baseEnd_7402415 : Nat := 3800996899051760750969419

theorem tailTrace_7402415 : CollatzResearch.WordTrace tailWord_7402415 prefixEnd_7402415 3800996899051760750969419 := by
  unfold tailWord_7402415
  simp only [CollatzResearch.WordTrace]
  refine ⟨269988255477322161676472699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179992170318214774450981799 269988255477322161676472699)
  ·
    refine ⟨404982383215983242514709049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269988255477322161676472699 404982383215983242514709049)
    ·
      refine ⟨303736787411987431886031787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404982383215983242514709049 303736787411987431886031787)
      ·
        refine ⟨455605181117981147829047681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303736787411987431886031787 455605181117981147829047681)
        ·
          refine ⟨341703885838485860871785761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455605181117981147829047681 341703885838485860871785761)
          ·
            refine ⟨256277914378864395653839321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341703885838485860871785761 256277914378864395653839321)
            ·
              refine ⟨192208435784148296740379491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256277914378864395653839321 192208435784148296740379491)
              ·
                refine ⟨288312653676222445110569237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192208435784148296740379491 288312653676222445110569237)
                ·
                  refine ⟨13514655641072927114557933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 288312653676222445110569237 13514655641072927114557933)
                  ·
                    refine ⟨5067995865402347667959225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13514655641072927114557933 5067995865402347667959225)
                    ·
                      refine ⟨3800996899051760750969419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5067995865402347667959225 3800996899051760750969419)
                      ·
                        rfl

theorem cell23_7402415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 3, 2].length) (baseStart_7402415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402415 prefixEnd_7402415 := by exact prefixLift 7402415
  have htrace : WordTrace (prefixWord ++ tailWord_7402415) baseStart_7402415 baseEnd_7402415 := by
    simpa [prefixWord, tailWord_7402415, baseEnd_7402415] using wordTrace_append hprefix tailTrace_7402415
  have hstable : (prefixWord ++ tailWord_7402415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402415).length < 2 ^ (prefixWord ++ tailWord_7402415).sum := by decide
  have hdescent : baseEnd_7402415 < baseStart_7402415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402425 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 1, 5]
def baseStart_7402425 : Nat := 118140960795 + 7402425 * 2 ^ 59
def prefixEnd_7402425 : Nat := 4983230072969 + 3 ^ 40 * 7402425 * 2
def baseEnd_7402425 : Nat := 1267000677952768570614791

theorem tailTrace_7402425 : CollatzResearch.WordTrace tailWord_7402425 prefixEnd_7402425 1267000677952768570614791 := by
  unfold tailWord_7402425
  simp only [CollatzResearch.WordTrace]
  refine ⟨269988620207285933384336729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179992413471523955589557819 269988620207285933384336729)
  ·
    refine ⟨202491465155464450038252547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269988620207285933384336729 202491465155464450038252547)
    ·
      refine ⟨303737197733196675057378821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202491465155464450038252547 303737197733196675057378821)
      ·
        refine ⟨56950724574974376573258529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303737197733196675057378821 56950724574974376573258529)
        ·
          refine ⟨42713043431230782429943897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56950724574974376573258529 42713043431230782429943897)
          ·
            refine ⟨32034782573423086822457923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42713043431230782429943897 32034782573423086822457923)
            ·
              refine ⟨48052173860134630233686885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32034782573423086822457923 48052173860134630233686885)
              ·
                refine ⟨9009782598775243168816291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48052173860134630233686885 9009782598775243168816291)
                ·
                  refine ⟨13514673898162864753224437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9009782598775243168816291 13514673898162864753224437)
                  ·
                    refine ⟨1267000677952768570614791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13514673898162864753224437 1267000677952768570614791)
                    ·
                      rfl

theorem cell23_7402425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 5].length) (baseStart_7402425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402425 prefixEnd_7402425 := by exact prefixLift 7402425
  have htrace : WordTrace (prefixWord ++ tailWord_7402425) baseStart_7402425 baseEnd_7402425 := by
    simpa [prefixWord, tailWord_7402425, baseEnd_7402425] using wordTrace_append hprefix tailTrace_7402425
  have hstable : (prefixWord ++ tailWord_7402425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402425).length < 2 ^ (prefixWord ++ tailWord_7402425).sum := by decide
  have hdescent : baseEnd_7402425 < baseStart_7402425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402439 : List Nat := [1, 1, 4, 1, 1, 2, 5, 3, 1, 1, 3]
def baseStart_7402439 : Nat := 118140960795 + 7402439 * 2 ^ 59
def prefixEnd_7402439 : Nat := 4983230072969 + 3 ^ 40 * 7402439 * 2
def baseEnd_7402439 : Nat := 3801009222587468657069309

theorem tailTrace_7402439 : CollatzResearch.WordTrace tailWord_7402439 prefixEnd_7402439 3801009222587468657069309 := by
  unfold tailWord_7402439
  simp only [CollatzResearch.WordTrace]
  refine ⟨269989130829235213775346371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179992753886156809183564247 269989130829235213775346371)
  ·
    refine ⟨404983696243852820663019557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269989130829235213775346371 404983696243852820663019557)
    ·
      refine ⟨75934443045722403874316167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404983696243852820663019557 75934443045722403874316167)
      ·
        refine ⟨113901664568583605811474251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75934443045722403874316167 113901664568583605811474251)
        ·
          refine ⟨170852496852875408717211377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113901664568583605811474251 170852496852875408717211377)
          ·
            refine ⟨128139372639656556537908533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170852496852875408717211377 128139372639656556537908533)
            ·
              refine ⟨12013066184967802175428925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128139372639656556537908533 12013066184967802175428925)
              ·
                refine ⟨4504899819362925815785847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12013066184967802175428925 4504899819362925815785847)
                ·
                  refine ⟨6757349729044388723678771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504899819362925815785847 6757349729044388723678771)
                  ·
                    refine ⟨10136024593566583085518157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6757349729044388723678771 10136024593566583085518157)
                    ·
                      refine ⟨3801009222587468657069309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10136024593566583085518157 3801009222587468657069309)
                      ·
                        rfl

theorem cell23_7402439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_7402439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402439 prefixEnd_7402439 := by exact prefixLift 7402439
  have htrace : WordTrace (prefixWord ++ tailWord_7402439) baseStart_7402439 baseEnd_7402439 := by
    simpa [prefixWord, tailWord_7402439, baseEnd_7402439] using wordTrace_append hprefix tailTrace_7402439
  have hstable : (prefixWord ++ tailWord_7402439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402439).length < 2 ^ (prefixWord ++ tailWord_7402439).sum := by decide
  have hdescent : baseEnd_7402439 < baseStart_7402439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402456 : List Nat := [2, 1, 2, 2, 2, 4, 3, 2, 1, 1, 3]
def baseStart_7402456 : Nat := 118140960795 + 7402456 * 2 ^ 59
def prefixEnd_7402456 : Nat := 4983230072969 + 3 ^ 40 * 7402456 * 2
def baseEnd_7402456 : Nat := 3801017951758595090556731

theorem tailTrace_7402456 : CollatzResearch.WordTrace tailWord_7402456 prefixEnd_7402456 3801017951758595090556731 := by
  unfold tailWord_7402456
  simp only [CollatzResearch.WordTrace]
  refine ⟨134994875435086812839357611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179993167246782417119143481 134994875435086812839357611)
  ·
    refine ⟨202492313152630219259036417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134994875435086812839357611 202492313152630219259036417)
    ·
      refine ⟨151869234864472664444277313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202492313152630219259036417 151869234864472664444277313)
      ·
        refine ⟨113901926148354498333207985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151869234864472664444277313 113901926148354498333207985)
        ·
          refine ⟨85426444611265873749905989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113901926148354498333207985 85426444611265873749905989)
          ·
            refine ⟨16017458364612351328107373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85426444611265873749905989 16017458364612351328107373)
            ·
              refine ⟨6006546886729631748040265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16017458364612351328107373 6006546886729631748040265)
              ·
                refine ⟨4504910165047223811030199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6006546886729631748040265 4504910165047223811030199)
                ·
                  refine ⟨6757365247570835716545299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504910165047223811030199 6757365247570835716545299)
                  ·
                    refine ⟨10136047871356253574817949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6757365247570835716545299 10136047871356253574817949)
                    ·
                      refine ⟨3801017951758595090556731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10136047871356253574817949 3801017951758595090556731)
                      ·
                        rfl

theorem cell23_7402456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_7402456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402456 prefixEnd_7402456 := by exact prefixLift 7402456
  have htrace : WordTrace (prefixWord ++ tailWord_7402456) baseStart_7402456 baseEnd_7402456 := by
    simpa [prefixWord, tailWord_7402456, baseEnd_7402456] using wordTrace_append hprefix tailTrace_7402456
  have hstable : (prefixWord ++ tailWord_7402456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402456).length < 2 ^ (prefixWord ++ tailWord_7402456).sum := by decide
  have hdescent : baseEnd_7402456 < baseStart_7402456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402465 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_7402465 : Nat := 118140960795 + 7402465 * 2 ^ 59
def prefixEnd_7402465 : Nat := 4983230072969 + 3 ^ 40 * 7402465 * 2
def baseEnd_7402465 : Nat := 3801022573084485555344189

theorem tailTrace_7402465 : CollatzResearch.WordTrace tailWord_7402465 prefixEnd_7402465 3801022573084485555344189 := by
  unfold tailWord_7402465
  simp only [CollatzResearch.WordTrace]
  refine ⟨269990079127141020215792849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179993386084760680143861899 269990079127141020215792849)
  ·
    refine ⟨202492559345355765161844637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269990079127141020215792849 202492559345355765161844637)
    ·
      refine ⟨75934709754508411935691739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202492559345355765161844637 75934709754508411935691739)
      ·
        refine ⟨113902064631762617903537609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75934709754508411935691739 113902064631762617903537609)
        ·
          refine ⟨85426548473821963427653207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113902064631762617903537609 85426548473821963427653207)
          ·
            refine ⟨128139822710732945141479811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85426548473821963427653207 128139822710732945141479811)
            ·
              refine ⟨192209734066099417712219717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128139822710732945141479811 192209734066099417712219717)
              ·
                refine ⟨36039325137393640821041197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192209734066099417712219717 36039325137393640821041197)
                ·
                  refine ⟨13514746926522615307890449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36039325137393640821041197 13514746926522615307890449)
                  ·
                    refine ⟨10136060194891961480917837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13514746926522615307890449 10136060194891961480917837)
                    ·
                      refine ⟨3801022573084485555344189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10136060194891961480917837 3801022573084485555344189)
                      ·
                        rfl

theorem cell23_7402465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_7402465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402465 prefixEnd_7402465 := by exact prefixLift 7402465
  have htrace : WordTrace (prefixWord ++ tailWord_7402465) baseStart_7402465 baseEnd_7402465 := by
    simpa [prefixWord, tailWord_7402465, baseEnd_7402465] using wordTrace_append hprefix tailTrace_7402465
  have hstable : (prefixWord ++ tailWord_7402465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402465).length < 2 ^ (prefixWord ++ tailWord_7402465).sum := by decide
  have hdescent : baseEnd_7402465 < baseStart_7402465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402502 : List Nat := [6, 2, 1, 14]
def baseStart_7402502 : Nat := 118140960795 + 7402502 * 2 ^ 59
def prefixEnd_7402502 : Nat := 4983230072969 + 3 ^ 40 * 7402502 * 2
def baseEnd_7402502 : Nat := 1738016265143439373837

theorem tailTrace_7402502 : CollatzResearch.WordTrace tailWord_7402502 prefixEnd_7402502 1738016265143439373837 := by
  unfold tailWord_7402502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8437232144625217985465305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179994285752004650356593173 8437232144625217985465305)
  ·
    refine ⟨6327924108468913489098979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8437232144625217985465305 6327924108468913489098979)
    ·
      refine ⟨9491886162703370233648469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6327924108468913489098979 9491886162703370233648469)
      ·
        refine ⟨1738016265143439373837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 9491886162703370233648469 1738016265143439373837)
        ·
          rfl

theorem cell23_7402502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 14].length) (baseStart_7402502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402502 prefixEnd_7402502 := by exact prefixLift 7402502
  have htrace : WordTrace (prefixWord ++ tailWord_7402502) baseStart_7402502 baseEnd_7402502 := by
    simpa [prefixWord, tailWord_7402502, baseEnd_7402502] using wordTrace_append hprefix tailTrace_7402502
  have hstable : (prefixWord ++ tailWord_7402502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402502).length < 2 ^ (prefixWord ++ tailWord_7402502).sum := by decide
  have hdescent : baseEnd_7402502 < baseStart_7402502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402522 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2]
def baseStart_7402522 : Nat := 118140960795 + 7402522 * 2 ^ 59
def prefixEnd_7402522 : Nat := 4983230072969 + 3 ^ 40 * 7402522 * 2
def baseEnd_7402522 : Nat := 3801051841481791832331427

theorem tailTrace_7402522 : CollatzResearch.WordTrace tailWord_7402522 prefixEnd_7402522 3801051841481791832331427 := by
  unfold tailWord_7402522
  simp only [CollatzResearch.WordTrace]
  refine ⟨67498039521983629737654455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179994772058623012633745213 67498039521983629737654455)
  ·
    refine ⟨101247059282975444606481683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67498039521983629737654455 101247059282975444606481683)
    ·
      refine ⟨151870588924463166909722525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101247059282975444606481683 151870588924463166909722525)
      ·
        refine ⟨56951470846673687591145947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151870588924463166909722525 56951470846673687591145947)
        ·
          refine ⟨85427206270010531386718921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56951470846673687591145947 85427206270010531386718921)
          ·
            refine ⟨64070404702507898540039191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85427206270010531386718921 64070404702507898540039191)
            ·
              refine ⟨96105607053761847810058787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64070404702507898540039191 96105607053761847810058787)
              ·
                refine ⟨144158410580642771715088181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96105607053761847810058787 144158410580642771715088181)
                ·
                  refine ⟨13514850991935259848289517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144158410580642771715088181 13514850991935259848289517)
                  ·
                    refine ⟨5068069121975722443108569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13514850991935259848289517 5068069121975722443108569)
                    ·
                      refine ⟨3801051841481791832331427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068069121975722443108569 3801051841481791832331427)
                      ·
                        rfl

theorem cell23_7402522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_7402522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402522 prefixEnd_7402522 := by exact prefixLift 7402522
  have htrace : WordTrace (prefixWord ++ tailWord_7402522) baseStart_7402522 baseEnd_7402522 := by
    simpa [prefixWord, tailWord_7402522, baseEnd_7402522] using wordTrace_append hprefix tailTrace_7402522
  have hstable : (prefixWord ++ tailWord_7402522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402522).length < 2 ^ (prefixWord ++ tailWord_7402522).sum := by decide
  have hdescent : baseEnd_7402522 < baseStart_7402522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402529 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_7402529 : Nat := 118140960795 + 7402529 * 2 ^ 59
def prefixEnd_7402529 : Nat := 4983230072969 + 3 ^ 40 * 7402529 * 2
def baseEnd_7402529 : Nat := 3801055435846373304943895

theorem tailTrace_7402529 : CollatzResearch.WordTrace tailWord_7402529 prefixEnd_7402529 3801055435846373304943895 := by
  unfold tailWord_7402529
  simp only [CollatzResearch.WordTrace]
  refine ⟨269992413398909159146122641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179994942265939439430748427 269992413398909159146122641)
  ·
    refine ⟨202494310049181869359591981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269992413398909159146122641 202494310049181869359591981)
    ·
      refine ⟨75935366268443201009846993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202494310049181869359591981 75935366268443201009846993)
      ·
        refine ⟨56951524701332400757385245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75935366268443201009846993 56951524701332400757385245)
        ·
          refine ⟨21356821762999650284019467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56951524701332400757385245 21356821762999650284019467)
          ·
            refine ⟨32035232644499475426029201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21356821762999650284019467 32035232644499475426029201)
            ·
              refine ⟨24026424483374606569521901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32035232644499475426029201 24026424483374606569521901)
              ·
                refine ⟨9009909181265477463570713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24026424483374606569521901 9009909181265477463570713)
                ·
                  refine ⟨6757431885949108097678035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9009909181265477463570713 6757431885949108097678035)
                  ·
                    refine ⟨10136147828923662146517053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6757431885949108097678035 10136147828923662146517053)
                    ·
                      refine ⟨3801055435846373304943895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10136147828923662146517053 3801055435846373304943895)
                      ·
                        rfl

theorem cell23_7402529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_7402529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402529 prefixEnd_7402529 := by exact prefixLift 7402529
  have htrace : WordTrace (prefixWord ++ tailWord_7402529) baseStart_7402529 baseEnd_7402529 := by
    simpa [prefixWord, tailWord_7402529, baseEnd_7402529] using wordTrace_append hprefix tailTrace_7402529
  have hstable : (prefixWord ++ tailWord_7402529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402529).length < 2 ^ (prefixWord ++ tailWord_7402529).sum := by decide
  have hdescent : baseEnd_7402529 < baseStart_7402529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402556 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 1, 3, 2]
def baseStart_7402556 : Nat := 118140960795 + 7402556 * 2 ^ 59
def prefixEnd_7402556 : Nat := 4983230072969 + 3 ^ 40 * 7402556 * 2
def baseEnd_7402556 : Nat := 3801069299824044699306271

theorem tailTrace_7402556 : CollatzResearch.WordTrace tailWord_7402556 prefixEnd_7402556 3801069299824044699306271 := by
  unfold tailWord_7402556
  simp only [CollatzResearch.WordTrace]
  refine ⟨134996699084905671378677761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179995598779874228504903681 134996699084905671378677761)
  ·
    refine ⟨101247524313679253534008321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134996699084905671378677761 101247524313679253534008321)
    ·
      refine ⟨75935643235259440150506241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101247524313679253534008321 75935643235259440150506241)
      ·
        refine ⟨56951732426444580112879681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75935643235259440150506241 56951732426444580112879681)
        ·
          refine ⟨42713799319833435084659761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56951732426444580112879681 42713799319833435084659761)
          ·
            refine ⟨32035349489875076313494821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42713799319833435084659761 32035349489875076313494821)
            ·
              refine ⟨6006628029351576808780279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32035349489875076313494821 6006628029351576808780279)
              ·
                refine ⟨9009942044027365213170419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006628029351576808780279 9009942044027365213170419)
                ·
                  refine ⟨13514913066041047819755629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9009942044027365213170419 13514913066041047819755629)
                  ·
                    refine ⟨5068092399765392932408361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13514913066041047819755629 5068092399765392932408361)
                    ·
                      refine ⟨3801069299824044699306271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068092399765392932408361 3801069299824044699306271)
                      ·
                        rfl

theorem cell23_7402556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_7402556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402556 prefixEnd_7402556 := by exact prefixLift 7402556
  have htrace : WordTrace (prefixWord ++ tailWord_7402556) baseStart_7402556 baseEnd_7402556 := by
    simpa [prefixWord, tailWord_7402556, baseEnd_7402556] using wordTrace_append hprefix tailTrace_7402556
  have hstable : (prefixWord ++ tailWord_7402556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402556).length < 2 ^ (prefixWord ++ tailWord_7402556).sum := by decide
  have hdescent : baseEnd_7402556 < baseStart_7402556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402565 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_7402565 : Nat := 118140960795 + 7402565 * 2 ^ 59
def prefixEnd_7402565 : Nat := 4983230072969 + 3 ^ 40 * 7402565 * 2
def baseEnd_7402565 : Nat := 3801073921149935164093729

theorem tailTrace_7402565 : CollatzResearch.WordTrace tailWord_7402565 prefixEnd_7402565 3801073921149935164093729 := by
  unfold tailWord_7402565
  simp only [CollatzResearch.WordTrace]
  refine ⟨269993726426778737294433149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179995817617852491529622099 269993726426778737294433149)
  ·
    refine ⟨101247647410042026485412431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269993726426778737294433149 101247647410042026485412431)
    ·
      refine ⟨151871471115063039728118647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101247647410042026485412431 151871471115063039728118647)
      ·
        refine ⟨227807206672594559592177971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151871471115063039728118647 227807206672594559592177971)
        ·
          refine ⟨341710810008891839388266957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227807206672594559592177971 341710810008891839388266957)
          ·
            refine ⟨128141553753334439770600109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341710810008891839388266957 128141553753334439770600109)
            ·
              refine ⟨48053082657500414913975041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128141553753334439770600109 48053082657500414913975041)
              ·
                refine ⟨36039811993125311185481281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48053082657500414913975041 36039811993125311185481281)
                ·
                  refine ⟨27029858994843983389110961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36039811993125311185481281 27029858994843983389110961)
                  ·
                    refine ⟨20272394246132987541833221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27029858994843983389110961 20272394246132987541833221)
                    ·
                      refine ⟨3801073921149935164093729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20272394246132987541833221 3801073921149935164093729)
                      ·
                        rfl

theorem cell23_7402565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_7402565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402565 prefixEnd_7402565 := by exact prefixLift 7402565
  have htrace : WordTrace (prefixWord ++ tailWord_7402565) baseStart_7402565 baseEnd_7402565 := by
    simpa [prefixWord, tailWord_7402565, baseEnd_7402565] using wordTrace_append hprefix tailTrace_7402565
  have hstable : (prefixWord ++ tailWord_7402565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402565).length < 2 ^ (prefixWord ++ tailWord_7402565).sum := by decide
  have hdescent : baseEnd_7402565 < baseStart_7402565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402569 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 2, 2, 2]
def baseStart_7402569 : Nat := 118140960795 + 7402569 * 2 ^ 59
def prefixEnd_7402569 : Nat := 4983230072969 + 3 ^ 40 * 7402569 * 2
def baseEnd_7402569 : Nat := 3801075975072553148443711

theorem tailTrace_7402569 : CollatzResearch.WordTrace tailWord_7402569 prefixEnd_7402569 3801075975072553148443711 := by
  unfold tailWord_7402569
  simp only [CollatzResearch.WordTrace]
  refine ⟨269993872318764245977578761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179995914879176163985052507 269993872318764245977578761)
  ·
    refine ⟨202495404239073184483184071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269993872318764245977578761 202495404239073184483184071)
    ·
      refine ⟨303743106358609776724776107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202495404239073184483184071 303743106358609776724776107)
      ·
        refine ⟨455614659537914665087164161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303743106358609776724776107 455614659537914665087164161)
        ·
          refine ⟨341710994653435998815373121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455614659537914665087164161 341710994653435998815373121)
          ·
            refine ⟨256283245990076999111529841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341710994653435998815373121 256283245990076999111529841)
            ·
              refine ⟨192212434492557749333647381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256283245990076999111529841 192212434492557749333647381)
              ·
                refine ⟨9009957866838644500014721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 192212434492557749333647381 9009957866838644500014721)
                ·
                  refine ⟨6757468400128983375011041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9009957866838644500014721 6757468400128983375011041)
                  ·
                    refine ⟨5068101300096737531258281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6757468400128983375011041 5068101300096737531258281)
                    ·
                      refine ⟨3801075975072553148443711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068101300096737531258281 3801075975072553148443711)
                      ·
                        rfl

theorem cell23_7402569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 2, 2].length) (baseStart_7402569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402569 prefixEnd_7402569 := by exact prefixLift 7402569
  have htrace : WordTrace (prefixWord ++ tailWord_7402569) baseStart_7402569 baseEnd_7402569 := by
    simpa [prefixWord, tailWord_7402569, baseEnd_7402569] using wordTrace_append hprefix tailTrace_7402569
  have hstable : (prefixWord ++ tailWord_7402569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402569).length < 2 ^ (prefixWord ++ tailWord_7402569).sum := by decide
  have hdescent : baseEnd_7402569 < baseStart_7402569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402585 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 1, 5, 3]
def baseStart_7402585 : Nat := 118140960795 + 7402585 * 2 ^ 59
def prefixEnd_7402585 : Nat := 4983230072969 + 3 ^ 40 * 7402585 * 2
def baseEnd_7402585 : Nat := 3801084190763025085843637

theorem tailTrace_7402585 : CollatzResearch.WordTrace tailWord_7402585 prefixEnd_7402585 3801084190763025085843637 := by
  unfold tailWord_7402585
  simp only [CollatzResearch.WordTrace]
  refine ⟨269994455886706280710161209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179996303924470853806774139 269994455886706280710161209)
  ·
    refine ⟨202495841915029710532620907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269994455886706280710161209 202495841915029710532620907)
    ·
      refine ⟨303743762872544565798931361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202495841915029710532620907 303743762872544565798931361)
      ·
        refine ⟨227807822154408424349198521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303743762872544565798931361 227807822154408424349198521)
        ·
          refine ⟨170855866615806318261898891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227807822154408424349198521 170855866615806318261898891)
          ·
            refine ⟨256283799923709477392848337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170855866615806318261898891 256283799923709477392848337)
            ·
              refine ⟨192212849942782108044636253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256283799923709477392848337 192212849942782108044636253)
              ·
                refine ⟨72079818728543290516738595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192212849942782108044636253 72079818728543290516738595)
                ·
                  refine ⟨108119728092814935775107893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72079818728543290516738595 108119728092814935775107893)
                  ·
                    refine ⟨10136224508701400228916365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108119728092814935775107893 10136224508701400228916365)
                    ·
                      refine ⟨3801084190763025085843637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10136224508701400228916365 3801084190763025085843637)
                      ·
                        rfl

theorem cell23_7402585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_7402585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402585 prefixEnd_7402585 := by exact prefixLift 7402585
  have htrace : WordTrace (prefixWord ++ tailWord_7402585) baseStart_7402585 baseEnd_7402585 := by
    simpa [prefixWord, tailWord_7402585, baseEnd_7402585] using wordTrace_append hprefix tailTrace_7402585
  have hstable : (prefixWord ++ tailWord_7402585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402585).length < 2 ^ (prefixWord ++ tailWord_7402585).sum := by decide
  have hdescent : baseEnd_7402585 < baseStart_7402585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402590 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_7402590 : Nat := 118140960795 + 7402590 * 2 ^ 59
def prefixEnd_7402590 : Nat := 4983230072969 + 3 ^ 40 * 7402590 * 2
def baseEnd_7402590 : Nat := 3801086758166297566281115

theorem tailTrace_7402590 : CollatzResearch.WordTrace tailWord_7402590 prefixEnd_7402590 3801086758166297566281115 := by
  unfold tailWord_7402590
  simp only [CollatzResearch.WordTrace]
  refine ⟨33749329781461020820511653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179996425501125444376062149 33749329781461020820511653)
  ·
    refine ⟨6327999334023941403845935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33749329781461020820511653 6327999334023941403845935)
    ·
      refine ⟨9491999001035912105768903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6327999334023941403845935 9491999001035912105768903)
      ·
        refine ⟨14237998501553868158653355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9491999001035912105768903 14237998501553868158653355)
        ·
          refine ⟨21356997752330802237980033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14237998501553868158653355 21356997752330802237980033)
          ·
            refine ⟨16017748314248101678485025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21356997752330802237980033 16017748314248101678485025)
            ·
              refine ⟨12013311235686076258863769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16017748314248101678485025 12013311235686076258863769)
              ·
                refine ⟨9009983426764557194147827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12013311235686076258863769 9009983426764557194147827)
                ·
                  refine ⟨13514975140146835791221741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9009983426764557194147827 13514975140146835791221741)
                  ·
                    refine ⟨5068115677555063421708153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13514975140146835791221741 5068115677555063421708153)
                    ·
                      refine ⟨3801086758166297566281115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068115677555063421708153 3801086758166297566281115)
                      ·
                        rfl

theorem cell23_7402590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_7402590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402590 prefixEnd_7402590 := by exact prefixLift 7402590
  have htrace : WordTrace (prefixWord ++ tailWord_7402590) baseStart_7402590 baseEnd_7402590 := by
    simpa [prefixWord, tailWord_7402590, baseEnd_7402590] using wordTrace_append hprefix tailTrace_7402590
  have hstable : (prefixWord ++ tailWord_7402590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402590).length < 2 ^ (prefixWord ++ tailWord_7402590).sum := by decide
  have hdescent : baseEnd_7402590 < baseStart_7402590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402615 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_7402615 : Nat := 118140960795 + 7402615 * 2 ^ 59
def prefixEnd_7402615 : Nat := 4983230072969 + 3 ^ 40 * 7402615 * 2
def baseEnd_7402615 : Nat := 3801099595182659968468499

theorem tailTrace_7402615 : CollatzResearch.WordTrace tailWord_7402615 prefixEnd_7402615 3801099595182659968468499 := by
  unfold tailWord_7402615
  simp only [CollatzResearch.WordTrace]
  refine ⟨269995550076597595833753299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179997033384398397222502199 269995550076597595833753299)
  ·
    refine ⟨404993325114896393750629949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269995550076597595833753299 404993325114896393750629949)
    ·
      refine ⟨151872496918086147656486231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404993325114896393750629949 151872496918086147656486231)
      ·
        refine ⟨227808745377129221484729347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151872496918086147656486231 227808745377129221484729347)
        ·
          refine ⟨341713118065693832227094021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227808745377129221484729347 341713118065693832227094021)
          ·
            refine ⟨64071209637317593542580129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341713118065693832227094021 64071209637317593542580129)
            ·
              refine ⟨48053407227988195156935097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64071209637317593542580129 48053407227988195156935097)
              ·
                refine ⟨36040055420991146367701323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48053407227988195156935097 36040055420991146367701323)
                ·
                  refine ⟨54060083131486719551551985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36040055420991146367701323 54060083131486719551551985)
                  ·
                    refine ⟨40545062348615039663663989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54060083131486719551551985 40545062348615039663663989)
                    ·
                      refine ⟨3801099595182659968468499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40545062348615039663663989 3801099595182659968468499)
                      ·
                        rfl

theorem cell23_7402615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_7402615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402615 prefixEnd_7402615 := by exact prefixLift 7402615
  have htrace : WordTrace (prefixWord ++ tailWord_7402615) baseStart_7402615 baseEnd_7402615 := by
    simpa [prefixWord, tailWord_7402615, baseEnd_7402615] using wordTrace_append hprefix tailTrace_7402615
  have hstable : (prefixWord ++ tailWord_7402615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402615).length < 2 ^ (prefixWord ++ tailWord_7402615).sum := by decide
  have hdescent : baseEnd_7402615 < baseStart_7402615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402705 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_7402705 : Nat := 118140960795 + 7402705 * 2 ^ 59
def prefixEnd_7402705 : Nat := 4983230072969 + 3 ^ 40 * 7402705 * 2
def baseEnd_7402705 : Nat := 3801145808441564616343085

theorem tailTrace_7402705 : CollatzResearch.WordTrace tailWord_7402705 prefixEnd_7402705 3801145808441564616343085 := by
  unfold tailWord_7402705
  simp only [CollatzResearch.WordTrace]
  refine ⟨269998832646271541204529569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179999221764181027469686379 269998832646271541204529569)
  ·
    refine ⟨202499124484703655903397177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269998832646271541204529569 202499124484703655903397177)
    ·
      refine ⟨151874343363527741927547883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202499124484703655903397177 151874343363527741927547883)
      ·
        refine ⟨227811515045291612891321825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151874343363527741927547883 227811515045291612891321825)
        ·
          refine ⟨170858636283968709668491369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227811515045291612891321825 170858636283968709668491369)
          ·
            refine ⟨128143977212976532251368527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170858636283968709668491369 128143977212976532251368527)
            ·
              refine ⟨192215965819464798377052791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128143977212976532251368527 192215965819464798377052791)
              ·
                refine ⟨288323948729197197565579187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192215965819464798377052791 288323948729197197565579187)
                ·
                  refine ⟨432485923093795796348368781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288323948729197197565579187 432485923093795796348368781)
                  ·
                    refine ⟨162182221160173423630638293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 432485923093795796348368781 162182221160173423630638293)
                    ·
                      refine ⟨3801145808441564616343085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162182221160173423630638293 3801145808441564616343085)
                      ·
                        rfl

theorem cell23_7402705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_7402705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402705 prefixEnd_7402705 := by exact prefixLift 7402705
  have htrace : WordTrace (prefixWord ++ tailWord_7402705) baseStart_7402705 baseEnd_7402705 := by
    simpa [prefixWord, tailWord_7402705, baseEnd_7402705] using wordTrace_append hprefix tailTrace_7402705
  have hstable : (prefixWord ++ tailWord_7402705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402705).length < 2 ^ (prefixWord ++ tailWord_7402705).sum := by decide
  have hdescent : baseEnd_7402705 < baseStart_7402705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402710 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_7402710 : Nat := 118140960795 + 7402710 * 2 ^ 59
def prefixEnd_7402710 : Nat := 4983230072969 + 3 ^ 40 * 7402710 * 2
def baseEnd_7402710 : Nat := 3801148375844837096780563

theorem tailTrace_7402710 : CollatzResearch.WordTrace tailWord_7402710 prefixEnd_7402710 3801148375844837096780563 := by
  unfold tailWord_7402710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16874938438203339191153849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179999343340835618038974389 16874938438203339191153849)
  ·
    refine ⟨12656203828652504393365387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16874938438203339191153849 12656203828652504393365387)
    ·
      refine ⟨18984305742978756590048081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12656203828652504393365387 18984305742978756590048081)
      ·
        refine ⟨14238229307234067442536061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18984305742978756590048081 14238229307234067442536061)
        ·
          refine ⟨5339335990212775290951023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14238229307234067442536061 5339335990212775290951023)
          ·
            refine ⟨8009003985319162936426535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339335990212775290951023 8009003985319162936426535)
            ·
              refine ⟨12013505977978744404639803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009003985319162936426535 12013505977978744404639803)
              ·
                refine ⟨18020258966968116606959705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12013505977978744404639803 18020258966968116606959705)
                ·
                  refine ⟨13515194225226087455219779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18020258966968116606959705 13515194225226087455219779)
                  ·
                    refine ⟨20272791337839131182829669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13515194225226087455219779 20272791337839131182829669)
                    ·
                      refine ⟨3801148375844837096780563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20272791337839131182829669 3801148375844837096780563)
                      ·
                        rfl

theorem cell23_7402710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_7402710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402710 prefixEnd_7402710 := by exact prefixLift 7402710
  have htrace : WordTrace (prefixWord ++ tailWord_7402710) baseStart_7402710 baseEnd_7402710 := by
    simpa [prefixWord, tailWord_7402710, baseEnd_7402710] using wordTrace_append hprefix tailTrace_7402710
  have hstable : (prefixWord ++ tailWord_7402710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402710).length < 2 ^ (prefixWord ++ tailWord_7402710).sum := by decide
  have hdescent : baseEnd_7402710 < baseStart_7402710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402766 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_7402766 : Nat := 118140960795 + 7402766 * 2 ^ 59
def prefixEnd_7402766 : Nat := 4983230072969 + 3 ^ 40 * 7402766 * 2
def baseEnd_7402766 : Nat := 3801177130761488877680305

theorem tailTrace_7402766 : CollatzResearch.WordTrace tailWord_7402766 prefixEnd_7402766 3801177130761488877680305 := by
  unfold tailWord_7402766
  simp only [CollatzResearch.WordTrace]
  refine ⟨33750132187381318577812519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180000704999367032415000101 33750132187381318577812519)
  ·
    refine ⟨50625198281071977866718779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33750132187381318577812519 50625198281071977866718779)
    ·
      refine ⟨75937797421607966800078169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50625198281071977866718779 75937797421607966800078169)
      ·
        refine ⟨56953348066205975100058627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75937797421607966800078169 56953348066205975100058627)
        ·
          refine ⟨85430022099308962650087941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56953348066205975100058627 85430022099308962650087941)
          ·
            refine ⟨16018129143620430496891489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85430022099308962650087941 16018129143620430496891489)
            ·
              refine ⟨12013596857715322872668617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16018129143620430496891489 12013596857715322872668617)
              ·
                refine ⟨9010197643286492154501463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12013596857715322872668617 9010197643286492154501463)
                ·
                  refine ⟨13515296464929738231752195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9010197643286492154501463 13515296464929738231752195)
                  ·
                    refine ⟨20272944697394607347628293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13515296464929738231752195 20272944697394607347628293)
                    ·
                      refine ⟨3801177130761488877680305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20272944697394607347628293 3801177130761488877680305)
                      ·
                        rfl

theorem cell23_7402766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_7402766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402766 prefixEnd_7402766 := by exact prefixLift 7402766
  have htrace : WordTrace (prefixWord ++ tailWord_7402766) baseStart_7402766 baseEnd_7402766 := by
    simpa [prefixWord, tailWord_7402766, baseEnd_7402766] using wordTrace_append hprefix tailTrace_7402766
  have hstable : (prefixWord ++ tailWord_7402766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402766).length < 2 ^ (prefixWord ++ tailWord_7402766).sum := by decide
  have hdescent : baseEnd_7402766 < baseStart_7402766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402786 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_7402786 : Nat := 118140960795 + 7402786 * 2 ^ 59
def prefixEnd_7402786 : Nat := 4983230072969 + 3 ^ 40 * 7402786 * 2
def baseEnd_7402786 : Nat := 3801187400374578799430213

theorem tailTrace_7402786 : CollatzResearch.WordTrace tailWord_7402786 prefixEnd_7402786 3801187400374578799430213 := by
  unfold tailWord_7402786
  simp only [CollatzResearch.WordTrace]
  refine ⟨67500446739744523009557053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180001191305985394692152141 67500446739744523009557053)
  ·
    refine ⟨25312667527404196128583895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67500446739744523009557053 25312667527404196128583895)
    ·
      refine ⟨37969001291106294192875843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25312667527404196128583895 37969001291106294192875843)
      ·
        refine ⟨56953501936659441289313765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37969001291106294192875843 56953501936659441289313765)
        ·
          refine ⟨10678781613123645241746331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56953501936659441289313765 10678781613123645241746331)
          ·
            refine ⟨16018172419685467862619497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10678781613123645241746331 16018172419685467862619497)
            ·
              refine ⟨12013629314764100896964623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16018172419685467862619497 12013629314764100896964623)
              ·
                refine ⟨18020443972146151345446935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12013629314764100896964623 18020443972146151345446935)
                ·
                  refine ⟨27030665958219227018170403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18020443972146151345446935 27030665958219227018170403)
                  ·
                    refine ⟨40545998937328840527255605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27030665958219227018170403 40545998937328840527255605)
                    ·
                      refine ⟨3801187400374578799430213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40545998937328840527255605 3801187400374578799430213)
                      ·
                        rfl

theorem cell23_7402786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_7402786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402786 prefixEnd_7402786 := by exact prefixLift 7402786
  have htrace : WordTrace (prefixWord ++ tailWord_7402786) baseStart_7402786 baseEnd_7402786 := by
    simpa [prefixWord, tailWord_7402786, baseEnd_7402786] using wordTrace_append hprefix tailTrace_7402786
  have hstable : (prefixWord ++ tailWord_7402786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402786).length < 2 ^ (prefixWord ++ tailWord_7402786).sum := by decide
  have hdescent : baseEnd_7402786 < baseStart_7402786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402800 : List Nat := [2, 1, 1, 1, 2, 2, 7, 2, 1, 2, 2]
def baseStart_7402800 : Nat := 118140960795 + 7402800 * 2 ^ 59
def prefixEnd_7402800 : Nat := 4983230072969 + 3 ^ 40 * 7402800 * 2
def baseEnd_7402800 : Nat := 3801194589103741744655149

theorem tailTrace_7402800 : CollatzResearch.WordTrace tailWord_7402800 prefixEnd_7402800 3801194589103741744655149 := by
  unfold tailWord_7402800
  simp only [CollatzResearch.WordTrace]
  refine ⟨135001148790463686214618927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180001531720618248286158569 135001148790463686214618927)
  ·
    refine ⟨202501723185695529321928391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135001148790463686214618927 202501723185695529321928391)
    ·
      refine ⟨303752584778543293982892587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202501723185695529321928391 303752584778543293982892587)
      ·
        refine ⟨455628877167814940974338881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303752584778543293982892587 455628877167814940974338881)
        ·
          refine ⟨341721657875861205730754161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455628877167814940974338881 341721657875861205730754161)
          ·
            refine ⟨256291243406895904298065621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341721657875861205730754161 256291243406895904298065621)
            ·
              refine ⟨6006826017349122756985913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 256291243406895904298065621 6006826017349122756985913)
              ·
                refine ⟨4505119513011842067739435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6006826017349122756985913 4505119513011842067739435)
                ·
                  refine ⟨6757679269517763101609153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505119513011842067739435 6757679269517763101609153)
                  ·
                    refine ⟨5068259452138322326206865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6757679269517763101609153 5068259452138322326206865)
                    ·
                      refine ⟨3801194589103741744655149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068259452138322326206865 3801194589103741744655149)
                      ·
                        rfl

theorem cell23_7402800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 1, 2, 2].length) (baseStart_7402800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402800 prefixEnd_7402800 := by exact prefixLift 7402800
  have htrace : WordTrace (prefixWord ++ tailWord_7402800) baseStart_7402800 baseEnd_7402800 := by
    simpa [prefixWord, tailWord_7402800, baseEnd_7402800] using wordTrace_append hprefix tailTrace_7402800
  have hstable : (prefixWord ++ tailWord_7402800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402800).length < 2 ^ (prefixWord ++ tailWord_7402800).sum := by decide
  have hdescent : baseEnd_7402800 < baseStart_7402800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402816 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 2, 1, 3]
def baseStart_7402816 : Nat := 118140960795 + 7402816 * 2 ^ 59
def prefixEnd_7402816 : Nat := 4983230072969 + 3 ^ 40 * 7402816 * 2
def baseEnd_7402816 : Nat := 3801202804794213682055075

theorem tailTrace_7402816 : CollatzResearch.WordTrace tailWord_7402816 prefixEnd_7402816 3801202804794213682055075 := by
  unfold tailWord_7402816
  simp only [CollatzResearch.WordTrace]
  refine ⟨135001440574434703580910151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180001920765912938107880201 135001440574434703580910151)
  ·
    refine ⟨202502160861652055371365227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135001440574434703580910151 202502160861652055371365227)
    ·
      refine ⟨303753241292478083057047841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202502160861652055371365227 303753241292478083057047841)
      ·
        refine ⟨227814930969358562292785881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303753241292478083057047841 227814930969358562292785881)
        ·
          refine ⟨170861198227018921719589411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227814930969358562292785881 170861198227018921719589411)
          ·
            refine ⟨256291797340528382579384117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170861198227018921719589411 256291797340528382579384117)
            ·
              refine ⟨24027356000674535866817261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256291797340528382579384117 24027356000674535866817261)
              ·
                refine ⟨9010258500252950950056473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24027356000674535866817261 9010258500252950950056473)
                ·
                  refine ⟨6757693875189713212542355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9010258500252950950056473 6757693875189713212542355)
                  ·
                    refine ⟨10136540812784569818813533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6757693875189713212542355 10136540812784569818813533)
                    ·
                      refine ⟨3801202804794213682055075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10136540812784569818813533 3801202804794213682055075)
                      ·
                        rfl

theorem cell23_7402816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_7402816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402816 prefixEnd_7402816 := by exact prefixLift 7402816
  have htrace : WordTrace (prefixWord ++ tailWord_7402816) baseStart_7402816 baseEnd_7402816 := by
    simpa [prefixWord, tailWord_7402816, baseEnd_7402816] using wordTrace_append hprefix tailTrace_7402816
  have hstable : (prefixWord ++ tailWord_7402816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402816).length < 2 ^ (prefixWord ++ tailWord_7402816).sum := by decide
  have hdescent : baseEnd_7402816 < baseStart_7402816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402820 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_7402820 : Nat := 118140960795 + 7402820 * 2 ^ 59
def prefixEnd_7402820 : Nat := 4983230072969 + 3 ^ 40 * 7402820 * 2
def baseEnd_7402820 : Nat := 3801204858716831666405057

theorem tailTrace_7402820 : CollatzResearch.WordTrace tailWord_7402820 prefixEnd_7402820 3801204858716831666405057 := by
  unfold tailWord_7402820
  simp only [CollatzResearch.WordTrace]
  refine ⟨135001513520427457922482957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180002018027236610563310609 135001513520427457922482957)
  ·
    refine ⟨50625567570160296720931109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135001513520427457922482957 50625567570160296720931109)
    ·
      refine ⟨9492293919405055635174583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50625567570160296720931109 9492293919405055635174583)
      ·
        refine ⟨14238440879107583452761875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9492293919405055635174583 14238440879107583452761875)
        ·
          refine ⟨21357661318661375179142813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14238440879107583452761875 21357661318661375179142813)
          ·
            refine ⟨8009122994498015692178555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21357661318661375179142813 8009122994498015692178555)
            ·
              refine ⟨12013684491747023538267833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009122994498015692178555 12013684491747023538267833)
              ·
                refine ⟨9010263368810267653700875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12013684491747023538267833 9010263368810267653700875)
                ·
                  refine ⟨13515395053215401480551313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9010263368810267653700875 13515395053215401480551313)
                  ·
                    refine ⟨10136546289911551110413485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13515395053215401480551313 10136546289911551110413485)
                    ·
                      refine ⟨3801204858716831666405057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10136546289911551110413485 3801204858716831666405057)
                      ·
                        rfl

theorem cell23_7402820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_7402820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402820 prefixEnd_7402820 := by exact prefixLift 7402820
  have htrace : WordTrace (prefixWord ++ tailWord_7402820) baseStart_7402820 baseEnd_7402820 := by
    simpa [prefixWord, tailWord_7402820, baseEnd_7402820] using wordTrace_append hprefix tailTrace_7402820
  have hstable : (prefixWord ++ tailWord_7402820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402820).length < 2 ^ (prefixWord ++ tailWord_7402820).sum := by decide
  have hdescent : baseEnd_7402820 < baseStart_7402820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402873 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 2, 2, 2]
def baseStart_7402873 : Nat := 118140960795 + 7402873 * 2 ^ 59
def prefixEnd_7402873 : Nat := 4983230072969 + 3 ^ 40 * 7402873 * 2
def baseEnd_7402873 : Nat := 3801232073191519959042313

theorem tailTrace_7402873 : CollatzResearch.WordTrace tailWord_7402873 prefixEnd_7402873 3801232073191519959042313 := by
  unfold tailWord_7402873
  simp only [CollatzResearch.WordTrace]
  refine ⟨270004960109662905896645273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180003306739775270597763515 270004960109662905896645273)
  ·
    refine ⟨202503720082247179422483955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270004960109662905896645273 202503720082247179422483955)
    ·
      refine ⟨303755580123370769133725933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202503720082247179422483955 303755580123370769133725933)
      ·
        refine ⟨113908342546264038425147225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303755580123370769133725933 113908342546264038425147225)
        ·
          refine ⟨85431256909698028818860419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113908342546264038425147225 85431256909698028818860419)
          ·
            refine ⟨128146885364547043228290629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85431256909698028818860419 128146885364547043228290629)
            ·
              refine ⟨24027541005852570605304493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128146885364547043228290629 24027541005852570605304493)
              ·
                refine ⟨9010327877194713976989185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24027541005852570605304493 9010327877194713976989185)
                ·
                  refine ⟨6757745907896035482741889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9010327877194713976989185 6757745907896035482741889)
                  ·
                    refine ⟨5068309430922026612056417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6757745907896035482741889 5068309430922026612056417)
                    ·
                      refine ⟨3801232073191519959042313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068309430922026612056417 3801232073191519959042313)
                      ·
                        rfl

theorem cell23_7402873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_7402873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402873 prefixEnd_7402873 := by exact prefixLift 7402873
  have htrace : WordTrace (prefixWord ++ tailWord_7402873) baseStart_7402873 baseEnd_7402873 := by
    simpa [prefixWord, tailWord_7402873, baseEnd_7402873] using wordTrace_append hprefix tailTrace_7402873
  have hstable : (prefixWord ++ tailWord_7402873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402873).length < 2 ^ (prefixWord ++ tailWord_7402873).sum := by decide
  have hdescent : baseEnd_7402873 < baseStart_7402873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402894 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7402894 : Nat := 118140960795 + 7402894 * 2 ^ 59
def prefixEnd_7402894 : Nat := 4983230072969 + 3 ^ 40 * 7402894 * 2
def baseEnd_7402894 : Nat := 3801242856285264376879717

theorem tailTrace_7402894 : CollatzResearch.WordTrace tailWord_7402894 prefixEnd_7402894 3801242856285264376879717 := by
  unfold tailWord_7402894
  simp only [CollatzResearch.WordTrace]
  refine ⟨33750715755323353310394967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180003817361724550988773157 33750715755323353310394967)
  ·
    refine ⟨50626073632985029965592451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33750715755323353310394967 50626073632985029965592451)
    ·
      refine ⟨75939110449477544948388677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50626073632985029965592451 75939110449477544948388677)
      ·
        refine ⟨14238583209277039677822877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75939110449477544948388677 14238583209277039677822877)
        ·
          refine ⟨5339468703478889879183579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14238583209277039677822877 5339468703478889879183579)
          ·
            refine ⟨8009203055218334818775369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339468703478889879183579 8009203055218334818775369)
            ·
              refine ⟨6006902291413751114081527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8009203055218334818775369 6006902291413751114081527)
              ·
                refine ⟨9010353437120626671122291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006902291413751114081527 9010353437120626671122291)
                ·
                  refine ⟨13515530155680940006683437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9010353437120626671122291 13515530155680940006683437)
                  ·
                    refine ⟨5068323808380352502506289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13515530155680940006683437 5068323808380352502506289)
                    ·
                      refine ⟨3801242856285264376879717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068323808380352502506289 3801242856285264376879717)
                      ·
                        rfl

theorem cell23_7402894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7402894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402894 prefixEnd_7402894 := by exact prefixLift 7402894
  have htrace : WordTrace (prefixWord ++ tailWord_7402894) baseStart_7402894 baseEnd_7402894 := by
    simpa [prefixWord, tailWord_7402894, baseEnd_7402894] using wordTrace_append hprefix tailTrace_7402894
  have hstable : (prefixWord ++ tailWord_7402894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402894).length < 2 ^ (prefixWord ++ tailWord_7402894).sum := by decide
  have hdescent : baseEnd_7402894 < baseStart_7402894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402919 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_7402919 : Nat := 118140960795 + 7402919 * 2 ^ 59
def prefixEnd_7402919 : Nat := 4983230072969 + 3 ^ 40 * 7402919 * 2
def baseEnd_7402919 : Nat := 3801255693301626779067101

theorem tailTrace_7402919 : CollatzResearch.WordTrace tailWord_7402919 prefixEnd_7402919 3801255693301626779067101 := by
  unfold tailWord_7402919
  simp only [CollatzResearch.WordTrace]
  refine ⟨270006637867496255752819811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180004425244997503835213207 270006637867496255752819811)
  ·
    refine ⟨405009956801244383629229717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270006637867496255752819811 405009956801244383629229717)
    ·
      refine ⟨18984841725058330482620143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 405009956801244383629229717 18984841725058330482620143)
      ·
        refine ⟨28477262587587495723930215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18984841725058330482620143 28477262587587495723930215)
        ·
          refine ⟨42715893881381243585895323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28477262587587495723930215 42715893881381243585895323)
          ·
            refine ⟨64073840822071865378842985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42715893881381243585895323 64073840822071865378842985)
            ·
              refine ⟨48055380616553899034132239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64073840822071865378842985 48055380616553899034132239)
              ·
                refine ⟨72083070924830848551198359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48055380616553899034132239 72083070924830848551198359)
                ·
                  refine ⟨108124606387246272826797539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72083070924830848551198359 108124606387246272826797539)
                  ·
                    refine ⟨162186909580869409240196309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108124606387246272826797539 162186909580869409240196309)
                    ·
                      refine ⟨3801255693301626779067101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162186909580869409240196309 3801255693301626779067101)
                      ·
                        rfl

theorem cell23_7402919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_7402919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402919 prefixEnd_7402919 := by exact prefixLift 7402919
  have htrace : WordTrace (prefixWord ++ tailWord_7402919) baseStart_7402919 baseEnd_7402919 := by
    simpa [prefixWord, tailWord_7402919, baseEnd_7402919] using wordTrace_append hprefix tailTrace_7402919
  have hstable : (prefixWord ++ tailWord_7402919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402919).length < 2 ^ (prefixWord ++ tailWord_7402919).sum := by decide
  have hdescent : baseEnd_7402919 < baseStart_7402919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402929 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7402929 : Nat := 118140960795 + 7402929 * 2 ^ 59
def prefixEnd_7402929 : Nat := 4983230072969 + 3 ^ 40 * 7402929 * 2
def baseEnd_7402929 : Nat := 3801260828108171739942055

theorem tailTrace_7402929 : CollatzResearch.WordTrace tailWord_7402929 prefixEnd_7402929 3801260828108171739942055 := by
  unfold tailWord_7402929
  simp only [CollatzResearch.WordTrace]
  refine ⟨270007002597460027460683841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180004668398306684973789227 270007002597460027460683841)
  ·
    refine ⟨202505251948095020595512881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270007002597460027460683841 202505251948095020595512881)
    ·
      refine ⟨151878938961071265446634661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202505251948095020595512881 151878938961071265446634661)
      ·
        refine ⟨28477301055200862271243999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151878938961071265446634661 28477301055200862271243999)
        ·
          refine ⟨42715951582801293406865999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28477301055200862271243999 42715951582801293406865999)
          ·
            refine ⟨64073927374201940110298999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42715951582801293406865999 64073927374201940110298999)
            ·
              refine ⟨96110891061302910165448499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64073927374201940110298999 96110891061302910165448499)
              ·
                refine ⟨144166336591954365248172749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96110891061302910165448499 144166336591954365248172749)
                ·
                  refine ⟨54062376221982886968064781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144166336591954365248172749 54062376221982886968064781)
                  ·
                    refine ⟨20273391083243582613024293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54062376221982886968064781 20273391083243582613024293)
                    ·
                      refine ⟨3801260828108171739942055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20273391083243582613024293 3801260828108171739942055)
                      ·
                        rfl

theorem cell23_7402929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7402929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402929 prefixEnd_7402929 := by exact prefixLift 7402929
  have htrace : WordTrace (prefixWord ++ tailWord_7402929) baseStart_7402929 baseEnd_7402929 := by
    simpa [prefixWord, tailWord_7402929, baseEnd_7402929] using wordTrace_append hprefix tailTrace_7402929
  have hstable : (prefixWord ++ tailWord_7402929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402929).length < 2 ^ (prefixWord ++ tailWord_7402929).sum := by decide
  have hdescent : baseEnd_7402929 < baseStart_7402929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402969 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 8]
def baseStart_7402969 : Nat := 118140960795 + 7402969 * 2 ^ 59
def prefixEnd_7402969 : Nat := 4983230072969 + 3 ^ 40 * 7402969 * 2
def baseEnd_7402969 : Nat := 422364596370483509271319

theorem tailTrace_7402969 : CollatzResearch.WordTrace tailWord_7402969 prefixEnd_7402969 422364596370483509271319 := by
  unfold tailWord_7402969
  simp only [CollatzResearch.WordTrace]
  refine ⟨270008461517315114292139961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180005641011543409528093307 270008461517315114292139961)
  ·
    refine ⟨202506346137986335719104971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270008461517315114292139961 202506346137986335719104971)
    ·
      refine ⟨303759519206979503578657457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202506346137986335719104971 303759519206979503578657457)
      ·
        refine ⟨227819639405234627683993093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303759519206979503578657457 227819639405234627683993093)
        ·
          refine ⟨42716182388481492690748705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227819639405234627683993093 42716182388481492690748705)
          ·
            refine ⟨32037136791361119518061529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42716182388481492690748705 32037136791361119518061529)
            ·
              refine ⟨24027852593520839638546147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32037136791361119518061529 24027852593520839638546147)
              ·
                refine ⟨36041778890281259457819221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24027852593520839638546147 36041778890281259457819221)
                ·
                  refine ⟨422364596370483509271319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36041778890281259457819221 422364596370483509271319)
                  ·
                    rfl

theorem cell23_7402969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 8].length) (baseStart_7402969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402969 prefixEnd_7402969 := by exact prefixLift 7402969
  have htrace : WordTrace (prefixWord ++ tailWord_7402969) baseStart_7402969 baseEnd_7402969 := by
    simpa [prefixWord, tailWord_7402969, baseEnd_7402969] using wordTrace_append hprefix tailTrace_7402969
  have hstable : (prefixWord ++ tailWord_7402969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402969).length < 2 ^ (prefixWord ++ tailWord_7402969).sum := by decide
  have hdescent : baseEnd_7402969 < baseStart_7402969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402973 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_7402973 : Nat := 118140960795 + 7402973 * 2 ^ 59
def prefixEnd_7402973 : Nat := 4983230072969 + 3 ^ 40 * 7402973 * 2
def baseEnd_7402973 : Nat := 1267094473752323189263951

theorem tailTrace_7402973 : CollatzResearch.WordTrace tailWord_7402973 prefixEnd_7402973 1267094473752323189263951 := by
  unfold tailWord_7402973
  simp only [CollatzResearch.WordTrace]
  refine ⟨270008607409300622975285573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180005738272867081983523715 270008607409300622975285573)
  ·
    refine ⟨50626613889243866807866045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270008607409300622975285573 50626613889243866807866045)
    ·
      refine ⟨18984980208466450052949767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50626613889243866807866045 18984980208466450052949767)
      ·
        refine ⟨28477470312699675079424651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18984980208466450052949767 28477470312699675079424651)
        ·
          refine ⟨42716205469049512619136977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28477470312699675079424651 42716205469049512619136977)
          ·
            refine ⟨32037154101787134464352733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42716205469049512619136977 32037154101787134464352733)
            ·
              refine ⟨12013932788170175424132275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32037154101787134464352733 12013932788170175424132275)
              ·
                refine ⟨18020899182255263136198413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12013932788170175424132275 18020899182255263136198413)
                ·
                  refine ⟨6757837193345723676074405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18020899182255263136198413 6757837193345723676074405)
                  ·
                    refine ⟨1267094473752323189263951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6757837193345723676074405 1267094473752323189263951)
                    ·
                      rfl

theorem cell23_7402973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_7402973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402973 prefixEnd_7402973 := by exact prefixLift 7402973
  have htrace : WordTrace (prefixWord ++ tailWord_7402973) baseStart_7402973 baseEnd_7402973 := by
    simpa [prefixWord, tailWord_7402973, baseEnd_7402973] using wordTrace_append hprefix tailTrace_7402973
  have hstable : (prefixWord ++ tailWord_7402973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402973).length < 2 ^ (prefixWord ++ tailWord_7402973).sum := by decide
  have hdescent : baseEnd_7402973 < baseStart_7402973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403016 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 1, 5]
def baseStart_7403016 : Nat := 118140960795 + 7403016 * 2 ^ 59
def prefixEnd_7403016 : Nat := 4983230072969 + 3 ^ 40 * 7403016 * 2
def baseEnd_7403016 : Nat := 1267101833641704299851385

theorem tailTrace_7403016 : CollatzResearch.WordTrace tailWord_7403016 prefixEnd_7403016 1267101833641704299851385 := by
  unfold tailWord_7403016
  simp only [CollatzResearch.WordTrace]
  refine ⟨135005087874072420659550451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180006783832096560879400601 135005087874072420659550451)
  ·
    refine ⟨202507631811108630989325677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135005087874072420659550451 202507631811108630989325677)
    ·
      refine ⟨75940361929165736620997129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202507631811108630989325677 75940361929165736620997129)
      ·
        refine ⟨56955271446874302465747847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75940361929165736620997129 56955271446874302465747847)
        ·
          refine ⟨85432907170311453698621771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56955271446874302465747847 85432907170311453698621771)
          ·
            refine ⟨128149360755467180547932657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85432907170311453698621771 128149360755467180547932657)
            ·
              refine ⟨96112020566600385410949493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128149360755467180547932657 96112020566600385410949493)
              ·
                refine ⟨9010501928118786132276515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96112020566600385410949493 9010501928118786132276515)
                ·
                  refine ⟨13515752892178179198414773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9010501928118786132276515 13515752892178179198414773)
                  ·
                    refine ⟨1267101833641704299851385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13515752892178179198414773 1267101833641704299851385)
                    ·
                      rfl

theorem cell23_7403016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_7403016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403016 prefixEnd_7403016 := by exact prefixLift 7403016
  have htrace : WordTrace (prefixWord ++ tailWord_7403016) baseStart_7403016 baseEnd_7403016 := by
    simpa [prefixWord, tailWord_7403016, baseEnd_7403016] using wordTrace_append hprefix tailTrace_7403016
  have hstable : (prefixWord ++ tailWord_7403016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403016).length < 2 ^ (prefixWord ++ tailWord_7403016).sum := by decide
  have hdescent : baseEnd_7403016 < baseStart_7403016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403036 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_7403036 : Nat := 118140960795 + 7403036 * 2 ^ 59
def prefixEnd_7403036 : Nat := 4983230072969 + 3 ^ 40 * 7403036 * 2
def baseEnd_7403036 : Nat := 3801315770538202821304063

theorem tailTrace_7403036 : CollatzResearch.WordTrace tailWord_7403036 prefixEnd_7403036 3801315770538202821304063 := by
  unfold tailWord_7403036
  simp only [CollatzResearch.WordTrace]
  refine ⟨135005452604036192367414481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180007270138714923156552641 135005452604036192367414481)
  ·
    refine ⟨101254089453027144275560861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135005452604036192367414481 101254089453027144275560861)
    ·
      refine ⟨37970283544885179103335323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101254089453027144275560861 37970283544885179103335323)
      ·
        refine ⟨56955425317327768655002985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37970283544885179103335323 56955425317327768655002985)
        ·
          refine ⟨42716568987995826491252239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56955425317327768655002985 42716568987995826491252239)
          ·
            refine ⟨64074853481993739736878359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42716568987995826491252239 64074853481993739736878359)
            ·
              refine ⟨96112280222990609605317539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64074853481993739736878359 96112280222990609605317539)
              ·
                refine ⟨144168420334485914407976309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96112280222990609605317539 144168420334485914407976309)
                ·
                  refine ⟨13515789406358054475747779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144168420334485914407976309 13515789406358054475747779)
                  ·
                    refine ⟨20273684109537081713621669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13515789406358054475747779 20273684109537081713621669)
                    ·
                      refine ⟨3801315770538202821304063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20273684109537081713621669 3801315770538202821304063)
                      ·
                        rfl

theorem cell23_7403036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_7403036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403036 prefixEnd_7403036 := by exact prefixLift 7403036
  have htrace : WordTrace (prefixWord ++ tailWord_7403036) baseStart_7403036 baseEnd_7403036 := by
    simpa [prefixWord, tailWord_7403036, baseEnd_7403036] using wordTrace_append hprefix tailTrace_7403036
  have hstable : (prefixWord ++ tailWord_7403036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403036).length < 2 ^ (prefixWord ++ tailWord_7403036).sum := by decide
  have hdescent : baseEnd_7403036 < baseStart_7403036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403066 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_7403066 : Nat := 118140960795 + 7403066 * 2 ^ 59
def prefixEnd_7403066 : Nat := 4983230072969 + 3 ^ 40 * 7403066 * 2
def baseEnd_7403066 : Nat := 3801331174957837703928925

theorem tailTrace_7403066 : CollatzResearch.WordTrace tailWord_7403066 prefixEnd_7403066 3801331174957837703928925 := by
  unfold tailWord_7403066
  simp only [CollatzResearch.WordTrace]
  refine ⟨67502999849490924964605263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180007999598642466572280701 67502999849490924964605263)
  ·
    refine ⟨101254499774236387446907895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67502999849490924964605263 101254499774236387446907895)
    ·
      refine ⟨151881749661354581170361843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101254499774236387446907895 151881749661354581170361843)
      ·
        refine ⟨227822624492031871755542765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151881749661354581170361843 227822624492031871755542765)
        ·
          refine ⟨85433484184511951908328537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227822624492031871755542765 85433484184511951908328537)
          ·
            refine ⟨64075113138383963931246403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85433484184511951908328537 64075113138383963931246403)
            ·
              refine ⟨96112669707575945896869605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64075113138383963931246403 96112669707575945896869605)
              ·
                refine ⟨18021125570170489855663051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96112669707575945896869605 18021125570170489855663051)
                ·
                  refine ⟨27031688355255734783494577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18021125570170489855663051 27031688355255734783494577)
                  ·
                    refine ⟨20273766266441801087620933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27031688355255734783494577 20273766266441801087620933)
                    ·
                      refine ⟨3801331174957837703928925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20273766266441801087620933 3801331174957837703928925)
                      ·
                        rfl

theorem cell23_7403066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_7403066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403066 prefixEnd_7403066 := by exact prefixLift 7403066
  have htrace : WordTrace (prefixWord ++ tailWord_7403066) baseStart_7403066 baseEnd_7403066 := by
    simpa [prefixWord, tailWord_7403066, baseEnd_7403066] using wordTrace_append hprefix tailTrace_7403066
  have hstable : (prefixWord ++ tailWord_7403066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403066).length < 2 ^ (prefixWord ++ tailWord_7403066).sum := by decide
  have hdescent : baseEnd_7403066 < baseStart_7403066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403100 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_7403100 : Nat := 118140960795 + 7403100 * 2 ^ 59
def prefixEnd_7403100 : Nat := 4983230072969 + 3 ^ 40 * 7403100 * 2
def baseEnd_7403100 : Nat := 3801348633300090570903769

theorem tailTrace_7403100 : CollatzResearch.WordTrace tailWord_7403100 prefixEnd_7403100 3801348633300090570903769 := by
  unfold tailWord_7403100
  simp only [CollatzResearch.WordTrace]
  refine ⟨135006619739920261832579377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180008826319893682443439169 135006619739920261832579377)
  ·
    refine ⟨101254964804940196374434533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135006619739920261832579377 101254964804940196374434533)
    ·
      refine ⟨18985305900926286820206475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101254964804940196374434533 18985305900926286820206475)
      ·
        refine ⟨28477958851389430230309713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18985305900926286820206475 28477958851389430230309713)
        ·
          refine ⟨21358469138542072672732285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28477958851389430230309713 21358469138542072672732285)
          ·
            refine ⟨8009425926953277252274607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21358469138542072672732285 8009425926953277252274607)
            ·
              refine ⟨12014138890429915878411911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009425926953277252274607 12014138890429915878411911)
              ·
                refine ⟨18021208335644873817617867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12014138890429915878411911 18021208335644873817617867)
                ·
                  refine ⟨27031812503467310726426801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18021208335644873817617867 27031812503467310726426801)
                  ·
                    refine ⟨20273859377600483044820101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27031812503467310726426801 20273859377600483044820101)
                    ·
                      refine ⟨3801348633300090570903769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20273859377600483044820101 3801348633300090570903769)
                      ·
                        rfl

theorem cell23_7403100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_7403100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403100 prefixEnd_7403100 := by exact prefixLift 7403100
  have htrace : WordTrace (prefixWord ++ tailWord_7403100) baseStart_7403100 baseEnd_7403100 := by
    simpa [prefixWord, tailWord_7403100, baseEnd_7403100] using wordTrace_append hprefix tailTrace_7403100
  have hstable : (prefixWord ++ tailWord_7403100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403100).length < 2 ^ (prefixWord ++ tailWord_7403100).sum := by decide
  have hdescent : baseEnd_7403100 < baseStart_7403100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403113 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 3, 3, 2]
def baseStart_7403113 : Nat := 118140960795 + 7403113 * 2 ^ 59
def prefixEnd_7403113 : Nat := 4983230072969 + 3 ^ 40 * 7403113 * 2
def baseEnd_7403113 : Nat := 3801355308548599020041209

theorem tailTrace_7403113 : CollatzResearch.WordTrace tailWord_7403113 prefixEnd_7403113 3801355308548599020041209 := by
  unfold tailWord_7403113
  simp only [CollatzResearch.WordTrace]
  refine ⟨270013713628793426885381993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180009142419195617923587995 270013713628793426885381993)
  ·
    refine ⟨202510285221595070164036495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270013713628793426885381993 202510285221595070164036495)
    ·
      refine ⟨303765427832392605246054743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202510285221595070164036495 303765427832392605246054743)
      ·
        refine ⟨455648141748588907869082115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303765427832392605246054743 455648141748588907869082115)
        ·
          refine ⟨683472212622883361803623173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455648141748588907869082115 683472212622883361803623173)
          ·
            refine ⟨128151039866790630338179345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 683472212622883361803623173 128151039866790630338179345)
            ·
              refine ⟨96113279900092972753634509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128151039866790630338179345 96113279900092972753634509)
              ·
                refine ⟨36042479962534864782612941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96113279900092972753634509 36042479962534864782612941)
                ·
                  refine ⟨13515929985950574293479853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36042479962534864782612941 13515929985950574293479853)
                  ·
                    refine ⟨5068473744731465360054945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13515929985950574293479853 5068473744731465360054945)
                    ·
                      refine ⟨3801355308548599020041209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068473744731465360054945 3801355308548599020041209)
                      ·
                        rfl

theorem cell23_7403113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 3, 2].length) (baseStart_7403113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403113 prefixEnd_7403113 := by exact prefixLift 7403113
  have htrace : WordTrace (prefixWord ++ tailWord_7403113) baseStart_7403113 baseEnd_7403113 := by
    simpa [prefixWord, tailWord_7403113, baseEnd_7403113] using wordTrace_append hprefix tailTrace_7403113
  have hstable : (prefixWord ++ tailWord_7403113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403113).length < 2 ^ (prefixWord ++ tailWord_7403113).sum := by decide
  have hdescent : baseEnd_7403113 < baseStart_7403113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403164 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_7403164 : Nat := 118140960795 + 7403164 * 2 ^ 59
def prefixEnd_7403164 : Nat := 4983230072969 + 3 ^ 40 * 7403164 * 2
def baseEnd_7403164 : Nat := 3801381496061978320503475

theorem tailTrace_7403164 : CollatzResearch.WordTrace tailWord_7403164 prefixEnd_7403164 3801381496061978320503475 := by
  unfold tailWord_7403164
  simp only [CollatzResearch.WordTrace]
  refine ⟨135007786875804331297744273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180010382501072441730325697 135007786875804331297744273)
  ·
    refine ⟨101255840156853248473308205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135007786875804331297744273 101255840156853248473308205)
    ·
      refine ⟨37970940058819968177490577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101255840156853248473308205 37970940058819968177490577)
      ·
        refine ⟨28478205044114976133117933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37970940058819968177490577 28478205044114976133117933)
        ·
          refine ⟨10679326891543116049919225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28478205044114976133117933 10679326891543116049919225)
          ·
            refine ⟨8009495168657337037439419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10679326891543116049919225 8009495168657337037439419)
            ·
              refine ⟨12014242752986005556159129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009495168657337037439419 12014242752986005556159129)
              ·
                refine ⟨9010682064739504167119347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12014242752986005556159129 9010682064739504167119347)
                ·
                  refine ⟨13516023097109256250679021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9010682064739504167119347 13516023097109256250679021)
                  ·
                    refine ⟨5068508661415971094004633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13516023097109256250679021 5068508661415971094004633)
                    ·
                      refine ⟨3801381496061978320503475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068508661415971094004633 3801381496061978320503475)
                      ·
                        rfl

theorem cell23_7403164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_7403164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403164 prefixEnd_7403164 := by exact prefixLift 7403164
  have htrace : WordTrace (prefixWord ++ tailWord_7403164) baseStart_7403164 baseEnd_7403164 := by
    simpa [prefixWord, tailWord_7403164, baseEnd_7403164] using wordTrace_append hprefix tailTrace_7403164
  have hstable : (prefixWord ++ tailWord_7403164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403164).length < 2 ^ (prefixWord ++ tailWord_7403164).sum := by decide
  have hdescent : baseEnd_7403164 < baseStart_7403164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403183 : List Nat := [1, 1, 2, 1, 2, 4, 2, 5, 5]
def baseStart_7403183 : Nat := 118140960795 + 7403183 * 2 ^ 59
def prefixEnd_7403183 : Nat := 4983230072969 + 3 ^ 40 * 7403183 * 2
def baseEnd_7403183 : Nat := 422376805799379305129543

theorem tailTrace_7403183 : CollatzResearch.WordTrace tailWord_7403183 prefixEnd_7403183 422376805799379305129543 := by
  unfold tailWord_7403183
  simp only [CollatzResearch.WordTrace]
  refine ⟨270016266738539828840430203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180010844492359885893620135 270016266738539828840430203)
  ·
    refine ⟨405024400107809743260645305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270016266738539828840430203 405024400107809743260645305)
    ·
      refine ⟨303768300080857307445483979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405024400107809743260645305 303768300080857307445483979)
      ·
        refine ⟨455652450121285961168225969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303768300080857307445483979 455652450121285961168225969)
        ·
          refine ⟨341739337590964470876169477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455652450121285961168225969 341739337590964470876169477)
          ·
            refine ⟨64076125798305838289281777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341739337590964470876169477 64076125798305838289281777)
            ·
              refine ⟨48057094348729378716961333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64076125798305838289281777 48057094348729378716961333)
              ·
                refine ⟨4505352595193379254715125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48057094348729378716961333 4505352595193379254715125)
                ·
                  refine ⟨422376805799379305129543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4505352595193379254715125 422376805799379305129543)
                  ·
                    rfl

theorem cell23_7403183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 5].length) (baseStart_7403183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403183 prefixEnd_7403183 := by exact prefixLift 7403183
  have htrace : WordTrace (prefixWord ++ tailWord_7403183) baseStart_7403183 baseEnd_7403183 := by
    simpa [prefixWord, tailWord_7403183, baseEnd_7403183] using wordTrace_append hprefix tailTrace_7403183
  have hstable : (prefixWord ++ tailWord_7403183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403183).length < 2 ^ (prefixWord ++ tailWord_7403183).sum := by decide
  have hdescent : baseEnd_7403183 < baseStart_7403183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403210 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_7403210 : Nat := 118140960795 + 7403210 * 2 ^ 59
def prefixEnd_7403210 : Nat := 4983230072969 + 3 ^ 40 * 7403210 * 2
def baseEnd_7403210 : Nat := 3801405116172085140528263

theorem tailTrace_7403210 : CollatzResearch.WordTrace tailWord_7403210 prefixEnd_7403210 3801405116172085140528263 := by
  unfold tailWord_7403210
  simp only [CollatzResearch.WordTrace]
  refine ⟨67504312877360503112915771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180011501006294674967775389 67504312877360503112915771)
  ·
    refine ⟨101256469316040754669373657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67504312877360503112915771 101256469316040754669373657)
    ·
      refine ⟨75942351987030566002030243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101256469316040754669373657 75942351987030566002030243)
      ·
        refine ⟨113913527980545849003045365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75942351987030566002030243 113913527980545849003045365)
        ·
          refine ⟨10679393248176173344035503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113913527980545849003045365 10679393248176173344035503)
          ·
            refine ⟨16019089872264260016053255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10679393248176173344035503 16019089872264260016053255)
            ·
              refine ⟨24028634808396390024079883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16019089872264260016053255 24028634808396390024079883)
              ·
                refine ⟨36042952212594585036119825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24028634808396390024079883 36042952212594585036119825)
                ·
                  refine ⟨27032214159445938777089869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36042952212594585036119825 27032214159445938777089869)
                  ·
                    refine ⟨10137080309792227041408701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27032214159445938777089869 10137080309792227041408701)
                    ·
                      refine ⟨3801405116172085140528263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10137080309792227041408701 3801405116172085140528263)
                      ·
                        rfl

theorem cell23_7403210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_7403210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403210 prefixEnd_7403210 := by exact prefixLift 7403210
  have htrace : WordTrace (prefixWord ++ tailWord_7403210) baseStart_7403210 baseEnd_7403210 := by
    simpa [prefixWord, tailWord_7403210, baseEnd_7403210] using wordTrace_append hprefix tailTrace_7403210
  have hstable : (prefixWord ++ tailWord_7403210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403210).length < 2 ^ (prefixWord ++ tailWord_7403210).sum := by decide
  have hdescent : baseEnd_7403210 < baseStart_7403210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403250 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 4, 4, 2]
def baseStart_7403250 : Nat := 118140960795 + 7403250 * 2 ^ 59
def prefixEnd_7403250 : Nat := 4983230072969 + 3 ^ 40 * 7403250 * 2
def baseEnd_7403250 : Nat := 3801425655398264984028079

theorem tailTrace_7403250 : CollatzResearch.WordTrace tailWord_7403250 prefixEnd_7403250 3801425655398264984028079 := by
  unfold tailWord_7403250
  simp only [CollatzResearch.WordTrace]
  refine ⟨67504677607324274820779801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180012473619531399522079469 67504677607324274820779801)
  ·
    refine ⟨50628508205493206115584851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67504677607324274820779801 50628508205493206115584851)
    ·
      refine ⟨75942762308239809173377277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50628508205493206115584851 75942762308239809173377277)
      ·
        refine ⟨28478535865589928440016479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75942762308239809173377277 28478535865589928440016479)
        ·
          refine ⟨42717803798384892660024719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28478535865589928440016479 42717803798384892660024719)
          ·
            refine ⟨64076705697577338990037079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42717803798384892660024719 64076705697577338990037079)
            ·
              refine ⟨96115058546366008485055619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64076705697577338990037079 96115058546366008485055619)
              ·
                refine ⟨144172587819549012727583429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96115058546366008485055619 144172587819549012727583429)
                ·
                  refine ⟨27032360216165439886421893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144172587819549012727583429 27032360216165439886421893)
                  ·
                    refine ⟨5068567540531019978704105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27032360216165439886421893 5068567540531019978704105)
                    ·
                      refine ⟨3801425655398264984028079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068567540531019978704105 3801425655398264984028079)
                      ·
                        rfl

theorem cell23_7403250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_7403250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403250 prefixEnd_7403250 := by exact prefixLift 7403250
  have htrace : WordTrace (prefixWord ++ tailWord_7403250) baseStart_7403250 baseEnd_7403250 := by
    simpa [prefixWord, tailWord_7403250, baseEnd_7403250] using wordTrace_append hprefix tailTrace_7403250
  have hstable : (prefixWord ++ tailWord_7403250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403250).length < 2 ^ (prefixWord ++ tailWord_7403250).sum := by decide
  have hdescent : baseEnd_7403250 < baseStart_7403250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403260 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 3, 4]
def baseStart_7403260 : Nat := 118140960795 + 7403260 * 2 ^ 59
def prefixEnd_7403260 : Nat := 4983230072969 + 3 ^ 40 * 7403260 * 2
def baseEnd_7403260 : Nat := 1267143596734936648301011

theorem tailTrace_7403260 : CollatzResearch.WordTrace tailWord_7403260 prefixEnd_7403260 1267143596734936648301011 := by
  unfold tailWord_7403260
  simp only [CollatzResearch.WordTrace]
  refine ⟨135009537579630435495491617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180012716772840580660655489 135009537579630435495491617)
  ·
    refine ⟨101257153184722826621618713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135009537579630435495491617 101257153184722826621618713)
    ·
      refine ⟨75942864888542119966214035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101257153184722826621618713 75942864888542119966214035)
      ·
        refine ⟨113914297332813179949321053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75942864888542119966214035 113914297332813179949321053)
        ·
          refine ⟨42717861499804942480995395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113914297332813179949321053 42717861499804942480995395)
          ·
            refine ⟨64076792249707413721493093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42717861499804942480995395 64076792249707413721493093)
            ·
              refine ⟨12014398546820140072779955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64076792249707413721493093 12014398546820140072779955)
              ·
                refine ⟨18021597820230210109169933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12014398546820140072779955 18021597820230210109169933)
                ·
                  refine ⟨6758099182586328790938725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18021597820230210109169933 6758099182586328790938725)
                  ·
                    refine ⟨1267143596734936648301011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6758099182586328790938725 1267143596734936648301011)
                    ·
                      rfl

theorem cell23_7403260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_7403260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403260 prefixEnd_7403260 := by exact prefixLift 7403260
  have htrace : WordTrace (prefixWord ++ tailWord_7403260) baseStart_7403260 baseEnd_7403260 := by
    simpa [prefixWord, tailWord_7403260, baseEnd_7403260] using wordTrace_append hprefix tailTrace_7403260
  have hstable : (prefixWord ++ tailWord_7403260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403260).length < 2 ^ (prefixWord ++ tailWord_7403260).sum := by decide
  have hdescent : baseEnd_7403260 < baseStart_7403260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403333 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_7403333 : Nat := 118140960795 + 7403333 * 2 ^ 59
def prefixEnd_7403333 : Nat := 4983230072969 + 3 ^ 40 * 7403333 * 2
def baseEnd_7403333 : Nat := 1267156091430862719763399

theorem tailTrace_7403333 : CollatzResearch.WordTrace tailWord_7403333 prefixEnd_7403333 1267156091430862719763399 := by
  unfold tailWord_7403333
  simp only [CollatzResearch.WordTrace]
  refine ⟨270021737687996404458390653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180014491791997602972260435 270021737687996404458390653)
  ·
    refine ⟨101258151632998651671896495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270021737687996404458390653 101258151632998651671896495)
    ·
      refine ⟨151887227449497977507844743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101258151632998651671896495 151887227449497977507844743)
      ·
        refine ⟨227830841174246966261767115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151887227449497977507844743 227830841174246966261767115)
        ·
          refine ⟨341746261761370449392650673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227830841174246966261767115 341746261761370449392650673)
          ·
            refine ⟨256309696321027837044488005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341746261761370449392650673 256309696321027837044488005)
            ·
              refine ⟨48058068060192719445841501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256309696321027837044488005 48058068060192719445841501)
              ·
                refine ⟨18021775522572269792190563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48058068060192719445841501 18021775522572269792190563)
                ·
                  refine ⟨27032663283858404688285845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18021775522572269792190563 27032663283858404688285845)
                  ·
                    refine ⟨1267156091430862719763399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27032663283858404688285845 1267156091430862719763399)
                    ·
                      rfl

theorem cell23_7403333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_7403333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403333 prefixEnd_7403333 := by exact prefixLift 7403333
  have htrace : WordTrace (prefixWord ++ tailWord_7403333) baseStart_7403333 baseEnd_7403333 := by
    simpa [prefixWord, tailWord_7403333, baseEnd_7403333] using wordTrace_append hprefix tailTrace_7403333
  have hstable : (prefixWord ++ tailWord_7403333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403333).length < 2 ^ (prefixWord ++ tailWord_7403333).sum := by decide
  have hdescent : baseEnd_7403333 < baseStart_7403333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403360 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 5]
def baseStart_7403360 : Nat := 118140960795 + 7403360 * 2 ^ 59
def prefixEnd_7403360 : Nat := 4983230072969 + 3 ^ 40 * 7403360 * 2
def baseEnd_7403360 : Nat := 3801482138270259553652573

theorem tailTrace_7403360 : CollatzResearch.WordTrace tailWord_7403360 prefixEnd_7403360 3801482138270259553652573 := by
  unfold tailWord_7403360
  simp only [CollatzResearch.WordTrace]
  refine ⟨135011361229449294034811767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180015148305932392046415689 135011361229449294034811767)
  ·
    refine ⟨202517041844173941052217651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135011361229449294034811767 202517041844173941052217651)
    ·
      refine ⟨303775562766260911578326477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202517041844173941052217651 303775562766260911578326477)
      ·
        refine ⟨113915836037347841841872429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303775562766260911578326477 113915836037347841841872429)
        ·
          refine ⟨42718438514005440690702161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113915836037347841841872429 42718438514005440690702161)
          ·
            refine ⟨32038828885504080518026621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42718438514005440690702161 32038828885504080518026621)
            ·
              refine ⟨12014560832064030194259983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32038828885504080518026621 12014560832064030194259983)
              ·
                refine ⟨18021841248096045291389975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12014560832064030194259983 18021841248096045291389975)
                ·
                  refine ⟨27032761872144067937084963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18021841248096045291389975 27032761872144067937084963)
                  ·
                    refine ⟨40549142808216101905627445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27032761872144067937084963 40549142808216101905627445)
                    ·
                      refine ⟨3801482138270259553652573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40549142808216101905627445 3801482138270259553652573)
                      ·
                        rfl

theorem cell23_7403360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_7403360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403360 prefixEnd_7403360 := by exact prefixLift 7403360
  have htrace : WordTrace (prefixWord ++ tailWord_7403360) baseStart_7403360 baseEnd_7403360 := by
    simpa [prefixWord, tailWord_7403360, baseEnd_7403360] using wordTrace_append hprefix tailTrace_7403360
  have hstable : (prefixWord ++ tailWord_7403360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403360).length < 2 ^ (prefixWord ++ tailWord_7403360).sum := by decide
  have hdescent : baseEnd_7403360 < baseStart_7403360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403363 : List Nat := [1, 1, 1, 5, 4, 11]
def baseStart_7403363 : Nat := 118140960795 + 7403363 * 2 ^ 59
def prefixEnd_7403363 : Nat := 4983230072969 + 3 ^ 40 * 7403363 * 2
def baseEnd_7403363 : Nat := 15643965756017378773313

theorem tailTrace_7403363 : CollatzResearch.WordTrace tailWord_7403363 prefixEnd_7403363 15643965756017378773313 := by
  unfold tailWord_7403363
  simp only [CollatzResearch.WordTrace]
  refine ⟨270022831877887719581982743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180015221251925146387988495 270022831877887719581982743)
  ·
    refine ⟨405034247816831579372974115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270022831877887719581982743 405034247816831579372974115)
    ·
      refine ⟨607551371725247369059461173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405034247816831579372974115 607551371725247369059461173)
      ·
        refine ⟨56957941099241940849324485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 607551371725247369059461173 56957941099241940849324485)
        ·
          refine ⟨10679613956107863909248341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56957941099241940849324485 10679613956107863909248341)
          ·
            refine ⟨15643965756017378773313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10679613956107863909248341 15643965756017378773313)
            ·
              rfl

theorem cell23_7403363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 11].length) (baseStart_7403363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403363 prefixEnd_7403363 := by exact prefixLift 7403363
  have htrace : WordTrace (prefixWord ++ tailWord_7403363) baseStart_7403363 baseEnd_7403363 := by
    simpa [prefixWord, tailWord_7403363, baseEnd_7403363] using wordTrace_append hprefix tailTrace_7403363
  have hstable : (prefixWord ++ tailWord_7403363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403363).length < 2 ^ (prefixWord ++ tailWord_7403363).sum := by decide
  have hdescent : baseEnd_7403363 < baseStart_7403363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403367 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 2, 4]
def baseStart_7403367 : Nat := 118140960795 + 7403367 * 2 ^ 59
def prefixEnd_7403367 : Nat := 4983230072969 + 3 ^ 40 * 7403367 * 2
def baseEnd_7403367 : Nat := 1267161910878280342088347

theorem tailTrace_7403367 : CollatzResearch.WordTrace tailWord_7403367 prefixEnd_7403367 1267161910878280342088347 := by
  unfold tailWord_7403367
  simp only [CollatzResearch.WordTrace]
  refine ⟨270022977769873228265128355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180015318513248818843418903 270022977769873228265128355)
  ·
    refine ⟨405034466654809842397692533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270022977769873228265128355 405034466654809842397692533)
    ·
      refine ⟨37971981248888422724783675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 405034466654809842397692533 37971981248888422724783675)
      ·
        refine ⟨56957971873332634087175513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37971981248888422724783675 56957971873332634087175513)
        ·
          refine ⟨42718478904999475565381635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56957971873332634087175513 42718478904999475565381635)
          ·
            refine ⟨64077718357499213348072453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42718478904999475565381635 64077718357499213348072453)
            ·
              refine ⟨12014572192031102502763585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64077718357499213348072453 12014572192031102502763585)
              ·
                refine ⟨9010929144023326877072689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12014572192031102502763585 9010929144023326877072689)
                ·
                  refine ⟨6758196858017495157804517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9010929144023326877072689 6758196858017495157804517)
                  ·
                    refine ⟨1267161910878280342088347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6758196858017495157804517 1267161910878280342088347)
                    ·
                      rfl

theorem cell23_7403367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_7403367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403367 prefixEnd_7403367 := by exact prefixLift 7403367
  have htrace : WordTrace (prefixWord ++ tailWord_7403367) baseStart_7403367 baseEnd_7403367 := by
    simpa [prefixWord, tailWord_7403367, baseEnd_7403367] using wordTrace_append hprefix tailTrace_7403367
  have hstable : (prefixWord ++ tailWord_7403367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403367).length < 2 ^ (prefixWord ++ tailWord_7403367).sum := by decide
  have hdescent : baseEnd_7403367 < baseStart_7403367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403403 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 5]
def baseStart_7403403 : Nat := 118140960795 + 7403403 * 2 ^ 59
def prefixEnd_7403403 : Nat := 4983230072969 + 3 ^ 40 * 7403403 * 2
def baseEnd_7403403 : Nat := 3801504217938402885414875

theorem tailTrace_7403403 : CollatzResearch.WordTrace tailWord_7403403 prefixEnd_7403403 3801504217938402885414875 := by
  unfold tailWord_7403403
  simp only [CollatzResearch.WordTrace]
  refine ⟨270024290797742806413438863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180016193865161870942292575 270024290797742806413438863)
  ·
    refine ⟨405036436196614209620158295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270024290797742806413438863 405036436196614209620158295)
    ·
      refine ⟨607554654294921314430237443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405036436196614209620158295 607554654294921314430237443)
      ·
        refine ⟨911331981442381971645356165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607554654294921314430237443 911331981442381971645356165)
        ·
          refine ⟨170874746520446619683504281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 911331981442381971645356165 170874746520446619683504281)
          ·
            refine ⟨128156059890334964762628211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170874746520446619683504281 128156059890334964762628211)
            ·
              refine ⟨192234089835502447143942317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128156059890334964762628211 192234089835502447143942317)
              ·
                refine ⟨72087783688313417678978369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192234089835502447143942317 72087783688313417678978369)
                ·
                  refine ⟨54065837766235063259233777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72087783688313417678978369 54065837766235063259233777)
                  ·
                    refine ⟨40549378324676297444425333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54065837766235063259233777 40549378324676297444425333)
                    ·
                      refine ⟨3801504217938402885414875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40549378324676297444425333 3801504217938402885414875)
                      ·
                        rfl

theorem cell23_7403403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_7403403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403403 prefixEnd_7403403 := by exact prefixLift 7403403
  have htrace : WordTrace (prefixWord ++ tailWord_7403403) baseStart_7403403 baseEnd_7403403 := by
    simpa [prefixWord, tailWord_7403403, baseEnd_7403403] using wordTrace_append hprefix tailTrace_7403403
  have hstable : (prefixWord ++ tailWord_7403403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403403).length < 2 ^ (prefixWord ++ tailWord_7403403).sum := by decide
  have hdescent : baseEnd_7403403 < baseStart_7403403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403414 : List Nat := [5, 3, 1, 1, 2, 1, 10]
def baseStart_7403414 : Nat := 118140960795 + 7403414 * 2 ^ 59
def prefixEnd_7403414 : Nat := 4983230072969 + 3 ^ 40 * 7403414 * 2
def baseEnd_7403414 : Nat := 46932220570686448671325

theorem tailTrace_7403414 : CollatzResearch.WordTrace tailWord_7403414 prefixEnd_7403414 46932220570686448671325 := by
  unfold tailWord_7403414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16876543250043934705755581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180016461333801970194726197 16876543250043934705755581)
  ·
    refine ⟨6328703718766475514658343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16876543250043934705755581 6328703718766475514658343)
    ·
      refine ⟨9493055578149713271987515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6328703718766475514658343 9493055578149713271987515)
      ·
        refine ⟨14239583367224569907981273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9493055578149713271987515 14239583367224569907981273)
        ·
          refine ⟨10679687525418427430985955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14239583367224569907981273 10679687525418427430985955)
          ·
            refine ⟨16019531288127641146478933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10679687525418427430985955 16019531288127641146478933)
            ·
              refine ⟨46932220570686448671325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16019531288127641146478933 46932220570686448671325)
              ·
                rfl

theorem cell23_7403414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 10].length) (baseStart_7403414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403414 prefixEnd_7403414 := by exact prefixLift 7403414
  have htrace : WordTrace (prefixWord ++ tailWord_7403414) baseStart_7403414 baseEnd_7403414 := by
    simpa [prefixWord, tailWord_7403414, baseEnd_7403414] using wordTrace_append hprefix tailTrace_7403414
  have hstable : (prefixWord ++ tailWord_7403414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403414).length < 2 ^ (prefixWord ++ tailWord_7403414).sum := by decide
  have hdescent : baseEnd_7403414 < baseStart_7403414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403433 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_7403433 : Nat := 118140960795 + 7403433 * 2 ^ 59
def prefixEnd_7403433 : Nat := 4983230072969 + 3 ^ 40 * 7403433 * 2
def baseEnd_7403433 : Nat := 3801519622358037768039737

theorem tailTrace_7403433 : CollatzResearch.WordTrace tailWord_7403433 prefixEnd_7403433 3801519622358037768039737 := by
  unfold tailWord_7403433
  simp only [CollatzResearch.WordTrace]
  refine ⟨270025384987634121537030953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180016923325089414358020635 270025384987634121537030953)
  ·
    refine ⟨202519038740725591152773215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270025384987634121537030953 202519038740725591152773215)
    ·
      refine ⟨303778558111088386729159823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202519038740725591152773215 303778558111088386729159823)
      ·
        refine ⟨455667837166632580093739735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303778558111088386729159823 455667837166632580093739735)
        ·
          refine ⟨683501755749948870140609603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455667837166632580093739735 683501755749948870140609603)
          ·
            refine ⟨1025252633624923305210914405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683501755749948870140609603 1025252633624923305210914405)
            ·
              refine ⟨192234868804673119727046451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1025252633624923305210914405 192234868804673119727046451)
              ·
                refine ⟨288352303207009679590569677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192234868804673119727046451 288352303207009679590569677)
                ·
                  refine ⟨108132113702628629846463629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288352303207009679590569677 108132113702628629846463629)
                  ·
                    refine ⟨40549542638485736192423861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108132113702628629846463629 40549542638485736192423861)
                    ·
                      refine ⟨3801519622358037768039737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40549542638485736192423861 3801519622358037768039737)
                      ·
                        rfl

theorem cell23_7403433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_7403433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403433 prefixEnd_7403433 := by exact prefixLift 7403433
  have htrace : WordTrace (prefixWord ++ tailWord_7403433) baseStart_7403433 baseEnd_7403433 := by
    simpa [prefixWord, tailWord_7403433, baseEnd_7403433] using wordTrace_append hprefix tailTrace_7403433
  have hstable : (prefixWord ++ tailWord_7403433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403433).length < 2 ^ (prefixWord ++ tailWord_7403433).sum := by decide
  have hdescent : baseEnd_7403433 < baseStart_7403433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403438 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7403438 : Nat := 118140960795 + 7403438 * 2 ^ 59
def prefixEnd_7403438 : Nat := 4983230072969 + 3 ^ 40 * 7403438 * 2
def baseEnd_7403438 : Nat := 3801522189761310248477215

theorem tailTrace_7403438 : CollatzResearch.WordTrace tailWord_7403438 prefixEnd_7403438 3801522189761310248477215 := by
  unfold tailWord_7403438
  simp only [CollatzResearch.WordTrace]
  refine ⟨33753195919077000923870371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180017044901744004927308645 33753195919077000923870371)
  ·
    refine ⟨50629793878615501385805557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33753195919077000923870371 50629793878615501385805557)
    ·
      refine ⟨4746543176120203254919271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50629793878615501385805557 4746543176120203254919271)
      ·
        refine ⟨7119814764180304882378907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4746543176120203254919271 7119814764180304882378907)
        ·
          refine ⟨10679722146270457323568361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7119814764180304882378907 10679722146270457323568361)
          ·
            refine ⟨8009791609702842992676271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10679722146270457323568361 8009791609702842992676271)
            ·
              refine ⟨12014687414554264489014407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009791609702842992676271 12014687414554264489014407)
              ·
                refine ⟨18022031121831396733521611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12014687414554264489014407 18022031121831396733521611)
                ·
                  refine ⟨27033046682747095100282417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18022031121831396733521611 27033046682747095100282417)
                  ·
                    refine ⟨20274785012060321325211813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27033046682747095100282417 20274785012060321325211813)
                    ·
                      refine ⟨3801522189761310248477215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20274785012060321325211813 3801522189761310248477215)
                      ·
                        rfl

theorem cell23_7403438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7403438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403438 prefixEnd_7403438 := by exact prefixLift 7403438
  have htrace : WordTrace (prefixWord ++ tailWord_7403438) baseStart_7403438 baseEnd_7403438 := by
    simpa [prefixWord, tailWord_7403438, baseEnd_7403438] using wordTrace_append hprefix tailTrace_7403438
  have hstable : (prefixWord ++ tailWord_7403438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403438).length < 2 ^ (prefixWord ++ tailWord_7403438).sum := by decide
  have hdescent : baseEnd_7403438 < baseStart_7403438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403441 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 2, 1, 3]
def baseStart_7403441 : Nat := 118140960795 + 7403441 * 2 ^ 59
def prefixEnd_7403441 : Nat := 4983230072969 + 3 ^ 40 * 7403441 * 2
def baseEnd_7403441 : Nat := 3801523730203273736739701

theorem tailTrace_7403441 : CollatzResearch.WordTrace tailWord_7403441 prefixEnd_7403441 3801523730203273736739701 := by
  unfold tailWord_7403441
  simp only [CollatzResearch.WordTrace]
  refine ⟨270025676771605138903322177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180017117847736759268881451 270025676771605138903322177)
  ·
    refine ⟨202519257578703854177491633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270025676771605138903322177 202519257578703854177491633)
    ·
      refine ⟨151889443184027890633118725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202519257578703854177491633 151889443184027890633118725)
      ·
        refine ⟨28479270597005229493709761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151889443184027890633118725 28479270597005229493709761)
        ·
          refine ⟨21359452947753922120282321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28479270597005229493709761 21359452947753922120282321)
          ·
            refine ⟨16019589710815441590211741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21359452947753922120282321 16019589710815441590211741)
            ·
              refine ⟨6007346141555790596329403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16019589710815441590211741 6007346141555790596329403)
              ·
                refine ⟨9011019212333685894494105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6007346141555790596329403 9011019212333685894494105)
                ·
                  refine ⟨6758264409250264420870579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9011019212333685894494105 6758264409250264420870579)
                  ·
                    refine ⟨10137396613875396631305869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6758264409250264420870579 10137396613875396631305869)
                    ·
                      refine ⟨3801523730203273736739701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10137396613875396631305869 3801523730203273736739701)
                      ·
                        rfl

theorem cell23_7403441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_7403441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403441 prefixEnd_7403441 := by exact prefixLift 7403441
  have htrace : WordTrace (prefixWord ++ tailWord_7403441) baseStart_7403441 baseEnd_7403441 := by
    simpa [prefixWord, tailWord_7403441, baseEnd_7403441] using wordTrace_append hprefix tailTrace_7403441
  have hstable : (prefixWord ++ tailWord_7403441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403441).length < 2 ^ (prefixWord ++ tailWord_7403441).sum := by decide
  have hdescent : baseEnd_7403441 < baseStart_7403441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403464 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 4, 2, 2]
def baseStart_7403464 : Nat := 118140960795 + 7403464 * 2 ^ 59
def prefixEnd_7403464 : Nat := 4983230072969 + 3 ^ 40 * 7403464 * 2
def baseEnd_7403464 : Nat := 3801535540258327146752095

theorem tailTrace_7403464 : CollatzResearch.WordTrace tailWord_7403464 prefixEnd_7403464 3801535540258327146752095 := by
  unfold tailWord_7403464
  simp only [CollatzResearch.WordTrace]
  refine ⟨135013257825260906915704723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180017677100347875887606297 135013257825260906915704723)
  ·
    refine ⟨202519886737891360373557085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135013257825260906915704723 202519886737891360373557085)
    ·
      refine ⟨75944957526709260140083907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202519886737891360373557085 75944957526709260140083907)
      ·
        refine ⟨113917436290063890210125861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75944957526709260140083907 113917436290063890210125861)
        ·
          refine ⟨21359519304386979414398599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113917436290063890210125861 21359519304386979414398599)
          ·
            refine ⟨32039278956580469121597899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21359519304386979414398599 32039278956580469121597899)
            ·
              refine ⟨48058918434870703682396849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32039278956580469121597899 48058918434870703682396849)
              ·
                refine ⟨36044188826153027761797637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48058918434870703682396849 36044188826153027761797637)
                ·
                  refine ⟨6758285404903692705337057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36044188826153027761797637 6758285404903692705337057)
                  ·
                    refine ⟨5068714053677769529002793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6758285404903692705337057 5068714053677769529002793)
                    ·
                      refine ⟨3801535540258327146752095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068714053677769529002793 3801535540258327146752095)
                      ·
                        rfl

theorem cell23_7403464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_7403464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403464 prefixEnd_7403464 := by exact prefixLift 7403464
  have htrace : WordTrace (prefixWord ++ tailWord_7403464) baseStart_7403464 baseEnd_7403464 := by
    simpa [prefixWord, tailWord_7403464, baseEnd_7403464] using wordTrace_append hprefix tailTrace_7403464
  have hstable : (prefixWord ++ tailWord_7403464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403464).length < 2 ^ (prefixWord ++ tailWord_7403464).sum := by decide
  have hdescent : baseEnd_7403464 < baseStart_7403464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403487 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 7]
def baseStart_7403487 : Nat := 118140960795 + 7403487 * 2 ^ 59
def prefixEnd_7403487 : Nat := 4983230072969 + 3 ^ 40 * 7403487 * 2
def baseEnd_7403487 : Nat := 422394150034820061862721

theorem tailTrace_7403487 : CollatzResearch.WordTrace tailWord_7403487 prefixEnd_7403487 422394150034820061862721 := by
  unfold tailWord_7403487
  simp only [CollatzResearch.WordTrace]
  refine ⟨270027354529438488759496715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180018236352958992506331143 270027354529438488759496715)
  ·
    refine ⟨405041031794157733139245073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270027354529438488759496715 405041031794157733139245073)
    ·
      refine ⟨303780773845618299854433805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405041031794157733139245073 303780773845618299854433805)
      ·
        refine ⟨113917790192106862445412677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303780773845618299854433805 113917790192106862445412677)
        ·
          refine ⟨21359585661020036708514877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113917790192106862445412677 21359585661020036708514877)
          ·
            refine ⟨8009844622882513765693079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21359585661020036708514877 8009844622882513765693079)
            ·
              refine ⟨12014766934323770648539619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009844622882513765693079 12014766934323770648539619)
              ·
                refine ⟨18022150401485655972809429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12014766934323770648539619 18022150401485655972809429)
                ·
                  refine ⟨422394150034820061862721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18022150401485655972809429 422394150034820061862721)
                  ·
                    rfl

theorem cell23_7403487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 7].length) (baseStart_7403487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403487 prefixEnd_7403487 := by exact prefixLift 7403487
  have htrace : WordTrace (prefixWord ++ tailWord_7403487) baseStart_7403487 baseEnd_7403487 := by
    simpa [prefixWord, tailWord_7403487, baseEnd_7403487] using wordTrace_append hprefix tailTrace_7403487
  have hstable : (prefixWord ++ tailWord_7403487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403487).length < 2 ^ (prefixWord ++ tailWord_7403487).sum := by decide
  have hdescent : baseEnd_7403487 < baseStart_7403487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403554 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_7403554 : Nat := 118140960795 + 7403554 * 2 ^ 59
def prefixEnd_7403554 : Nat := 4983230072969 + 3 ^ 40 * 7403554 * 2
def baseEnd_7403554 : Nat := 3801581753517231794626681

theorem tailTrace_7403554 : CollatzResearch.WordTrace tailWord_7403554 prefixEnd_7403554 3801581753517231794626681 := by
  unfold tailWord_7403554
  simp only [CollatzResearch.WordTrace]
  refine ⟨67507449555048939800546429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180019865480130506134790477 67507449555048939800546429)
  ·
    refine ⟨25315293583143352425204911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67507449555048939800546429 25315293583143352425204911)
    ·
      refine ⟨37972940374715028637807367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25315293583143352425204911 37972940374715028637807367)
      ·
        refine ⟨56959410562072542956711051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37972940374715028637807367 56959410562072542956711051)
        ·
          refine ⟨85439115843108814435066577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56959410562072542956711051 85439115843108814435066577)
          ·
            refine ⟨64079336882331610826299933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85439115843108814435066577 64079336882331610826299933)
            ·
              refine ⟨24029751330874354059862475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64079336882331610826299933 24029751330874354059862475)
              ·
                refine ⟨36044626996311531089793713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24029751330874354059862475 36044626996311531089793713)
                ·
                  refine ⟨27033470247233648317345285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36044626996311531089793713 27033470247233648317345285)
                  ·
                    refine ⟨5068775671356309059502241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27033470247233648317345285 5068775671356309059502241)
                    ·
                      refine ⟨3801581753517231794626681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068775671356309059502241 3801581753517231794626681)
                      ·
                        rfl

theorem cell23_7403554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_7403554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403554 prefixEnd_7403554 := by exact prefixLift 7403554
  have htrace : WordTrace (prefixWord ++ tailWord_7403554) baseStart_7403554 baseEnd_7403554 := by
    simpa [prefixWord, tailWord_7403554, baseEnd_7403554] using wordTrace_append hprefix tailTrace_7403554
  have hstable : (prefixWord ++ tailWord_7403554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403554).length < 2 ^ (prefixWord ++ tailWord_7403554).sum := by decide
  have hdescent : baseEnd_7403554 < baseStart_7403554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403574 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_7403574 : Nat := 118140960795 + 7403574 * 2 ^ 59
def prefixEnd_7403574 : Nat := 4983230072969 + 3 ^ 40 * 7403574 * 2
def baseEnd_7403574 : Nat := 3801592023130321716376589

theorem tailTrace_7403574 : CollatzResearch.WordTrace tailWord_7403574 prefixEnd_7403574 3801592023130321716376589 := by
  unfold tailWord_7403574
  simp only [CollatzResearch.WordTrace]
  refine ⟨16876907980007706413619611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180020351786748868411942517 16876907980007706413619611)
  ·
    refine ⟨25315361970011559620429417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16876907980007706413619611 25315361970011559620429417)
    ·
      refine ⟨18986521477508669715322063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25315361970011559620429417 18986521477508669715322063)
      ·
        refine ⟨28479782216263004572983095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18986521477508669715322063 28479782216263004572983095)
        ·
          refine ⟨42719673324394506859474643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28479782216263004572983095 42719673324394506859474643)
          ·
            refine ⟨64079509986591760289211965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42719673324394506859474643 64079509986591760289211965)
            ·
              refine ⟨24029816244971910108454487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64079509986591760289211965 24029816244971910108454487)
              ·
                refine ⟨36044724367457865162681731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24029816244971910108454487 36044724367457865162681731)
                ·
                  refine ⟨54067086551186797744022597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36044724367457865162681731 54067086551186797744022597)
                  ·
                    refine ⟨10137578728347524577004237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54067086551186797744022597 10137578728347524577004237)
                    ·
                      refine ⟨3801592023130321716376589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10137578728347524577004237 3801592023130321716376589)
                      ·
                        rfl

theorem cell23_7403574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_7403574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403574 prefixEnd_7403574 := by exact prefixLift 7403574
  have htrace : WordTrace (prefixWord ++ tailWord_7403574) baseStart_7403574 baseEnd_7403574 := by
    simpa [prefixWord, tailWord_7403574, baseEnd_7403574] using wordTrace_append hprefix tailTrace_7403574
  have hstable : (prefixWord ++ tailWord_7403574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403574).length < 2 ^ (prefixWord ++ tailWord_7403574).sum := by decide
  have hdescent : baseEnd_7403574 < baseStart_7403574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403581 : List Nat := [1, 4, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_7403581 : Nat := 118140960795 + 7403581 * 2 ^ 59
def prefixEnd_7403581 : Nat := 4983230072969 + 3 ^ 40 * 7403581 * 2
def baseEnd_7403581 : Nat := 1267198539164967729663019

theorem tailTrace_7403581 : CollatzResearch.WordTrace tailWord_7403581 prefixEnd_7403581 1267198539164967729663019 := by
  unfold tailWord_7403581
  simp only [CollatzResearch.WordTrace]
  refine ⟨270030782991097942813418597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180020521994065295208945731 270030782991097942813418597)
  ·
    refine ⟨50630771810830864277515987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270030782991097942813418597 50630771810830864277515987)
    ·
      refine ⟨75946157716246296416273981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50630771810830864277515987 75946157716246296416273981)
      ·
        refine ⟨28479809143592361156102743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75946157716246296416273981 28479809143592361156102743)
        ·
          refine ⟨42719713715388541734154115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28479809143592361156102743 42719713715388541734154115)
          ·
            refine ⟨64079570573082812601231173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42719713715388541734154115 64079570573082812601231173)
            ·
              refine ⟨12014919482453027362730845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64079570573082812601231173 12014919482453027362730845)
              ·
                refine ⟨4505594805919885261024067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12014919482453027362730845 4505594805919885261024067)
                ·
                  refine ⟨6758392208879827891536101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505594805919885261024067 6758392208879827891536101)
                  ·
                    refine ⟨1267198539164967729663019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6758392208879827891536101 1267198539164967729663019)
                    ·
                      rfl

theorem cell23_7403581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_7403581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403581 prefixEnd_7403581 := by exact prefixLift 7403581
  have htrace : WordTrace (prefixWord ++ tailWord_7403581) baseStart_7403581 baseEnd_7403581 := by
    simpa [prefixWord, tailWord_7403581, baseEnd_7403581] using wordTrace_append hprefix tailTrace_7403581
  have hstable : (prefixWord ++ tailWord_7403581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403581).length < 2 ^ (prefixWord ++ tailWord_7403581).sum := by decide
  have hdescent : baseEnd_7403581 < baseStart_7403581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403597 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_7403597 : Nat := 118140960795 + 7403597 * 2 ^ 59
def prefixEnd_7403597 : Nat := 4983230072969 + 3 ^ 40 * 7403597 * 2
def baseEnd_7403597 : Nat := 3801603833185375126388983

theorem tailTrace_7403597 : CollatzResearch.WordTrace tailWord_7403597 prefixEnd_7403597 3801603833185375126388983 := by
  unfold tailWord_7403597
  simp only [CollatzResearch.WordTrace]
  refine ⟨270031366559039977546001045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180020911039359985030667363 270031366559039977546001045)
  ·
    refine ⟨12657720307454998947468799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 270031366559039977546001045 12657720307454998947468799)
    ·
      refine ⟨18986580461182498421203199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12657720307454998947468799 18986580461182498421203199)
      ·
        refine ⟨28479870691773747631804799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18986580461182498421203199 28479870691773747631804799)
        ·
          refine ⟨42719806037660621447707199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28479870691773747631804799 42719806037660621447707199)
          ·
            refine ⟨64079709056490932171560799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42719806037660621447707199 64079709056490932171560799)
            ·
              refine ⟨96119563584736398257341199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64079709056490932171560799 96119563584736398257341199)
              ·
                refine ⟨144179345377104597386011799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96119563584736398257341199 144179345377104597386011799)
                ·
                  refine ⟨216269018065656896079017699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144179345377104597386011799 216269018065656896079017699)
                  ·
                    refine ⟨324403527098485344118526549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216269018065656896079017699 324403527098485344118526549)
                    ·
                      refine ⟨3801603833185375126388983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 324403527098485344118526549 3801603833185375126388983)
                      ·
                        rfl

theorem cell23_7403597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_7403597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403597 prefixEnd_7403597 := by exact prefixLift 7403597
  have htrace : WordTrace (prefixWord ++ tailWord_7403597) baseStart_7403597 baseEnd_7403597 := by
    simpa [prefixWord, tailWord_7403597, baseEnd_7403597] using wordTrace_append hprefix tailTrace_7403597
  have hstable : (prefixWord ++ tailWord_7403597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403597).length < 2 ^ (prefixWord ++ tailWord_7403597).sum := by decide
  have hdescent : baseEnd_7403597 < baseStart_7403597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403644 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_7403644 : Nat := 118140960795 + 7403644 * 2 ^ 59
def prefixEnd_7403644 : Nat := 4983230072969 + 3 ^ 40 * 7403644 * 2
def baseEnd_7403644 : Nat := 3801627966776136442501267

theorem tailTrace_7403644 : CollatzResearch.WordTrace tailWord_7403644 prefixEnd_7403644 3801627966776136442501267 := by
  unfold tailWord_7403644
  simp only [CollatzResearch.WordTrace]
  refine ⟨135016540394934852286480993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180022053859913136381974657 135016540394934852286480993)
  ·
    refine ⟨101262405296201139214860745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135016540394934852286480993 101262405296201139214860745)
    ·
      refine ⟨75946803972150854411145559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101262405296201139214860745 75946803972150854411145559)
      ·
        refine ⟨113920205958226281616718339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75946803972150854411145559 113920205958226281616718339)
        ·
          refine ⟨170880308937339422425077509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113920205958226281616718339 170880308937339422425077509)
          ·
            refine ⟨32040057925751141704702033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170880308937339422425077509 32040057925751141704702033)
            ·
              refine ⟨24030043444313356278526525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32040057925751141704702033 24030043444313356278526525)
              ·
                refine ⟨9011266291617508604447447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24030043444313356278526525 9011266291617508604447447)
                ·
                  refine ⟨13516899437426262906671171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9011266291617508604447447 13516899437426262906671171)
                  ·
                    refine ⟨20275349156139394360006757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13516899437426262906671171 20275349156139394360006757)
                    ·
                      refine ⟨3801627966776136442501267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20275349156139394360006757 3801627966776136442501267)
                      ·
                        rfl

theorem cell23_7403644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_7403644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403644 prefixEnd_7403644 := by exact prefixLift 7403644
  have htrace : WordTrace (prefixWord ++ tailWord_7403644) baseStart_7403644 baseEnd_7403644 := by
    simpa [prefixWord, tailWord_7403644, baseEnd_7403644] using wordTrace_append hprefix tailTrace_7403644
  have hstable : (prefixWord ++ tailWord_7403644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403644).length < 2 ^ (prefixWord ++ tailWord_7403644).sum := by decide
  have hdescent : baseEnd_7403644 < baseStart_7403644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403671 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 2, 4]
def baseStart_7403671 : Nat := 118140960795 + 7403671 * 2 ^ 59
def prefixEnd_7403671 : Nat := 4983230072969 + 3 ^ 40 * 7403671 * 2
def baseEnd_7403671 : Nat := 1267213943584602612287881

theorem tailTrace_7403671 : CollatzResearch.WordTrace tailWord_7403671 prefixEnd_7403671 1267213943584602612287881 := by
  unfold tailWord_7403671
  simp only [CollatzResearch.WordTrace]
  refine ⟨270034065560771888184194867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180022710373847925456129911 270034065560771888184194867)
  ·
    refine ⟨405051098341157832276292301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270034065560771888184194867 405051098341157832276292301)
    ·
      refine ⟨151894161877934187103609613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405051098341157832276292301 151894161877934187103609613)
      ·
        refine ⟨56960310704225320163853605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151894161877934187103609613 56960310704225320163853605)
        ·
          refine ⟨10680058257042247530722551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56960310704225320163853605 10680058257042247530722551)
          ·
            refine ⟨16020087385563371296083827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10680058257042247530722551 16020087385563371296083827)
            ·
              refine ⟨24030131078345056944125741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16020087385563371296083827 24030131078345056944125741)
              ·
                refine ⟨9011299154379396354047153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24030131078345056944125741 9011299154379396354047153)
                ·
                  refine ⟨6758474365784547265535365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9011299154379396354047153 6758474365784547265535365)
                  ·
                    refine ⟨1267213943584602612287881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6758474365784547265535365 1267213943584602612287881)
                    ·
                      rfl

theorem cell23_7403671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_7403671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403671 prefixEnd_7403671 := by exact prefixLift 7403671
  have htrace : WordTrace (prefixWord ++ tailWord_7403671) baseStart_7403671 baseEnd_7403671 := by
    simpa [prefixWord, tailWord_7403671, baseEnd_7403671] using wordTrace_append hprefix tailTrace_7403671
  have hstable : (prefixWord ++ tailWord_7403671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403671).length < 2 ^ (prefixWord ++ tailWord_7403671).sum := by decide
  have hdescent : baseEnd_7403671 < baseStart_7403671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403681 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_7403681 : Nat := 118140960795 + 7403681 * 2 ^ 59
def prefixEnd_7403681 : Nat := 4983230072969 + 3 ^ 40 * 7403681 * 2
def baseEnd_7403681 : Nat := 3801646965560352797738597

theorem tailTrace_7403681 : CollatzResearch.WordTrace tailWord_7403681 prefixEnd_7403681 3801646965560352797738597 := by
  unfold tailWord_7403681
  simp only [CollatzResearch.WordTrace]
  refine ⟨270034430290735659892058897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180022953527157106594705931 270034430290735659892058897)
  ·
    refine ⟨202525822718051744919044173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270034430290735659892058897 202525822718051744919044173)
    ·
      refine ⟨75947183519269404344641565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202525822718051744919044173 75947183519269404344641565)
      ·
        refine ⟨28480193819726026629240587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75947183519269404344641565 28480193819726026629240587)
        ·
          refine ⟨42720290729589039943860881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28480193819726026629240587 42720290729589039943860881)
          ·
            refine ⟨32040218047191779957895661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42720290729589039943860881 32040218047191779957895661)
            ·
              refine ⟨12015081767696917484210873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32040218047191779957895661 12015081767696917484210873)
              ·
                refine ⟨9011311325772688113158155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12015081767696917484210873 9011311325772688113158155)
                ·
                  refine ⟨13516966988659032169737233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9011311325772688113158155 13516966988659032169737233)
                  ·
                    refine ⟨10137725241494274127302925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13516966988659032169737233 10137725241494274127302925)
                    ·
                      refine ⟨3801646965560352797738597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10137725241494274127302925 3801646965560352797738597)
                      ·
                        rfl

theorem cell23_7403681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_7403681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403681 prefixEnd_7403681 := by exact prefixLift 7403681
  have htrace : WordTrace (prefixWord ++ tailWord_7403681) baseStart_7403681 baseEnd_7403681 := by
    simpa [prefixWord, tailWord_7403681, baseEnd_7403681] using wordTrace_append hprefix tailTrace_7403681
  have hstable : (prefixWord ++ tailWord_7403681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403681).length < 2 ^ (prefixWord ++ tailWord_7403681).sum := by decide
  have hdescent : baseEnd_7403681 < baseStart_7403681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403712 : List Nat := [2, 1, 1, 2, 5, 3, 2, 2, 1, 2, 2]
def baseStart_7403712 : Nat := 118140960795 + 7403712 * 2 ^ 59
def prefixEnd_7403712 : Nat := 4983230072969 + 3 ^ 40 * 7403712 * 2
def baseEnd_7403712 : Nat := 3801662883460642176450955

theorem tailTrace_7403712 : CollatzResearch.WordTrace tailWord_7403712 prefixEnd_7403712 3801662883460642176450955 := by
  unfold tailWord_7403712
  simp only [CollatzResearch.WordTrace]
  refine ⟨135017780476811676093218695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180023707302415568124291593 135017780476811676093218695)
  ·
    refine ⟨202526670715217514139828043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135017780476811676093218695 202526670715217514139828043)
    ·
      refine ⟨303790006072826271209742065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202526670715217514139828043 303790006072826271209742065)
      ·
        refine ⟨227842504554619703407306549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303790006072826271209742065 227842504554619703407306549)
        ·
          refine ⟨21360234801995597194434989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227842504554619703407306549 21360234801995597194434989)
          ·
            refine ⟨8010088050748348947913121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21360234801995597194434989 8010088050748348947913121)
            ·
              refine ⟨6007566038061261710934841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8010088050748348947913121 6007566038061261710934841)
              ·
                refine ⟨4505674528545946283201131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6007566038061261710934841 4505674528545946283201131)
                ·
                  refine ⟨6758511792818919424801697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505674528545946283201131 6758511792818919424801697)
                  ·
                    refine ⟨5068883844614189568601273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6758511792818919424801697 5068883844614189568601273)
                    ·
                      refine ⟨3801662883460642176450955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068883844614189568601273 3801662883460642176450955)
                      ·
                        rfl

theorem cell23_7403712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 1, 2, 2].length) (baseStart_7403712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403712 prefixEnd_7403712 := by exact prefixLift 7403712
  have htrace : WordTrace (prefixWord ++ tailWord_7403712) baseStart_7403712 baseEnd_7403712 := by
    simpa [prefixWord, tailWord_7403712, baseEnd_7403712] using wordTrace_append hprefix tailTrace_7403712
  have hstable : (prefixWord ++ tailWord_7403712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403712).length < 2 ^ (prefixWord ++ tailWord_7403712).sum := by decide
  have hdescent : baseEnd_7403712 < baseStart_7403712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403717 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_7403717 : Nat := 118140960795 + 7403717 * 2 ^ 59
def prefixEnd_7403717 : Nat := 4983230072969 + 3 ^ 40 * 7403717 * 2
def baseEnd_7403717 : Nat := 3801665450863914656888431

theorem tailTrace_7403717 : CollatzResearch.WordTrace tailWord_7403717 prefixEnd_7403717 3801665450863914656888431 := by
  unfold tailWord_7403717
  simp only [CollatzResearch.WordTrace]
  refine ⟨270035743318605238040369405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180023828879070158693579603 270035743318605238040369405)
  ·
    refine ⟨101263403744476964265138527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270035743318605238040369405 101263403744476964265138527)
    ·
      refine ⟨151895105616715446397707791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101263403744476964265138527 151895105616715446397707791)
      ·
        refine ⟨227842658425073169596561687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151895105616715446397707791 227842658425073169596561687)
        ·
          refine ⟨341763987637609754394842531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227842658425073169596561687 341763987637609754394842531)
          ·
            refine ⟨512645981456414631592263797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341763987637609754394842531 512645981456414631592263797)
            ·
              refine ⟨48060560761538871711774731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 512645981456414631592263797 48060560761538871711774731)
              ·
                refine ⟨72090841142308307567662097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48060560761538871711774731 72090841142308307567662097)
                ·
                  refine ⟨54068130856731230675746573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72090841142308307567662097 54068130856731230675746573)
                  ·
                    refine ⟨20275549071274211503404965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54068130856731230675746573 20275549071274211503404965)
                    ·
                      refine ⟨3801665450863914656888431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20275549071274211503404965 3801665450863914656888431)
                      ·
                        rfl

theorem cell23_7403717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_7403717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403717 prefixEnd_7403717 := by exact prefixLift 7403717
  have htrace : WordTrace (prefixWord ++ tailWord_7403717) baseStart_7403717 baseEnd_7403717 := by
    simpa [prefixWord, tailWord_7403717, baseEnd_7403717] using wordTrace_append hprefix tailTrace_7403717
  have hstable : (prefixWord ++ tailWord_7403717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403717).length < 2 ^ (prefixWord ++ tailWord_7403717).sum := by decide
  have hdescent : baseEnd_7403717 < baseStart_7403717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403727 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 2, 6]
def baseStart_7403727 : Nat := 118140960795 + 7403727 * 2 ^ 59
def prefixEnd_7403727 : Nat := 4983230072969 + 3 ^ 40 * 7403727 * 2
def baseEnd_7403727 : Nat := 1267223528556819872587795

theorem tailTrace_7403727 : CollatzResearch.WordTrace tailWord_7403727 prefixEnd_7403727 1267223528556819872587795 := by
  unfold tailWord_7403727
  simp only [CollatzResearch.WordTrace]
  refine ⟨270036108048569009748233435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180024072032379339832155623 270036108048569009748233435)
  ·
    refine ⟨405054162072853514622350153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270036108048569009748233435 405054162072853514622350153)
    ·
      refine ⟨303790621554640135966762615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405054162072853514622350153 303790621554640135966762615)
      ·
        refine ⟨455685932331960203950143923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303790621554640135966762615 455685932331960203950143923)
        ·
          refine ⟨683528898497940305925215885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455685932331960203950143923 683528898497940305925215885)
          ·
            refine ⟨256323336936727614721955957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 683528898497940305925215885 256323336936727614721955957)
            ·
              refine ⟨24030312837818213880183371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256323336936727614721955957 24030312837818213880183371)
              ·
                refine ⟨36045469256727320820275057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24030312837818213880183371 36045469256727320820275057)
                ·
                  refine ⟨27034101942545490615206293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36045469256727320820275057 27034101942545490615206293)
                  ·
                    refine ⟨1267223528556819872587795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27034101942545490615206293 1267223528556819872587795)
                    ·
                      rfl

theorem cell23_7403727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_7403727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403727 prefixEnd_7403727 := by exact prefixLift 7403727
  have htrace : WordTrace (prefixWord ++ tailWord_7403727) baseStart_7403727 baseEnd_7403727 := by
    simpa [prefixWord, tailWord_7403727, baseEnd_7403727] using wordTrace_append hprefix tailTrace_7403727
  have hstable : (prefixWord ++ tailWord_7403727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403727).length < 2 ^ (prefixWord ++ tailWord_7403727).sum := by decide
  have hdescent : baseEnd_7403727 < baseStart_7403727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403737 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 5]
def baseStart_7403737 : Nat := 118140960795 + 7403737 * 2 ^ 59
def prefixEnd_7403737 : Nat := 4983230072969 + 3 ^ 40 * 7403737 * 2
def baseEnd_7403737 : Nat := 3801675720477004578638339

theorem tailTrace_7403737 : CollatzResearch.WordTrace tailWord_7403737 prefixEnd_7403737 3801675720477004578638339 := by
  unfold tailWord_7403737
  simp only [CollatzResearch.WordTrace]
  refine ⟨270036472778532781456097465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180024315185688520970731643 270036472778532781456097465)
  ·
    refine ⟨202527354583899586092073099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270036472778532781456097465 202527354583899586092073099)
    ·
      refine ⟨303791031875849379138109649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202527354583899586092073099 303791031875849379138109649)
      ·
        refine ⟨227843273906887034353582237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303791031875849379138109649 227843273906887034353582237)
        ·
          refine ⟨85441227715082637882593339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227843273906887034353582237 85441227715082637882593339)
          ·
            refine ⟨128161841572623956823890009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85441227715082637882593339 128161841572623956823890009)
            ·
              refine ⟨96121381179467967617917507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128161841572623956823890009 96121381179467967617917507)
              ·
                refine ⟨144182071769201951426876261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96121381179467967617917507 144182071769201951426876261)
                ·
                  refine ⟨27034138456725365892539299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144182071769201951426876261 27034138456725365892539299)
                  ·
                    refine ⟨40551207685088048838808949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27034138456725365892539299 40551207685088048838808949)
                    ·
                      refine ⟨3801675720477004578638339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40551207685088048838808949 3801675720477004578638339)
                      ·
                        rfl

theorem cell23_7403737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_7403737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403737 prefixEnd_7403737 := by exact prefixLift 7403737
  have htrace : WordTrace (prefixWord ++ tailWord_7403737) baseStart_7403737 baseEnd_7403737 := by
    simpa [prefixWord, tailWord_7403737, baseEnd_7403737] using wordTrace_append hprefix tailTrace_7403737
  have hstable : (prefixWord ++ tailWord_7403737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403737).length < 2 ^ (prefixWord ++ tailWord_7403737).sum := by decide
  have hdescent : baseEnd_7403737 < baseStart_7403737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403746 : List Nat := [3, 3, 4, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7403746 : Nat := 118140960795 + 7403746 * 2 ^ 59
def prefixEnd_7403746 : Nat := 4983230072969 + 3 ^ 40 * 7403746 * 2
def baseEnd_7403746 : Nat := 3801680341802895043425799

theorem tailTrace_7403746 : CollatzResearch.WordTrace tailWord_7403746 prefixEnd_7403746 3801680341802895043425799 := by
  unfold tailWord_7403746
  simp only [CollatzResearch.WordTrace]
  refine ⟨67509200258875043998293773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180024534023666783995450061 67509200258875043998293773)
  ·
    refine ⟨25315950097078141499360165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67509200258875043998293773 25315950097078141499360165)
    ·
      refine ⟨4746740643202151531130031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25315950097078141499360165 4746740643202151531130031)
      ·
        refine ⟨7120110964803227296695047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4746740643202151531130031 7120110964803227296695047)
        ·
          refine ⟨10680166447204840945042571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7120110964803227296695047 10680166447204840945042571)
          ·
            refine ⟨16020249670807261417563857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10680166447204840945042571 16020249670807261417563857)
            ·
              refine ⟨12015187253105446063172893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16020249670807261417563857 12015187253105446063172893)
              ·
                refine ⟨4505695219914542273689835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12015187253105446063172893 4505695219914542273689835)
                ·
                  refine ⟨6758542829871813410534753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505695219914542273689835 6758542829871813410534753)
                  ·
                    refine ⟨5068907122403860057901065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6758542829871813410534753 5068907122403860057901065)
                    ·
                      refine ⟨3801680341802895043425799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068907122403860057901065 3801680341802895043425799)
                      ·
                        rfl

theorem cell23_7403746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7403746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403746 prefixEnd_7403746 := by exact prefixLift 7403746
  have htrace : WordTrace (prefixWord ++ tailWord_7403746) baseStart_7403746 baseEnd_7403746 := by
    simpa [prefixWord, tailWord_7403746, baseEnd_7403746] using wordTrace_append hprefix tailTrace_7403746
  have hstable : (prefixWord ++ tailWord_7403746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403746).length < 2 ^ (prefixWord ++ tailWord_7403746).sum := by decide
  have hdescent : baseEnd_7403746 < baseStart_7403746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403785 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 2, 2, 2]
def baseStart_7403785 : Nat := 118140960795 + 7403785 * 2 ^ 59
def prefixEnd_7403785 : Nat := 4983230072969 + 3 ^ 40 * 7403785 * 2
def baseEnd_7403785 : Nat := 3801700367548420390838119

theorem tailTrace_7403785 : CollatzResearch.WordTrace tailWord_7403785 prefixEnd_7403785 3801700367548420390838119 := by
  unfold tailWord_7403785
  simp only [CollatzResearch.WordTrace]
  refine ⟨270038223482358885653844809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180025482321572590435896539 270038223482358885653844809)
  ·
    refine ⟨202528667611769164240383607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270038223482358885653844809 202528667611769164240383607)
    ·
      refine ⟨303793001417653746360575411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202528667611769164240383607 303793001417653746360575411)
      ·
        refine ⟨455689502126480619540863117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303793001417653746360575411 455689502126480619540863117)
        ·
          refine ⟨170883563297430232327823669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455689502126480619540863117 170883563297430232327823669)
          ·
            refine ⟨16020334059134084280733469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170883563297430232327823669 16020334059134084280733469)
            ·
              refine ⟨6007625272175281605275051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16020334059134084280733469 6007625272175281605275051)
              ·
                refine ⟨9011437908262922407912577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6007625272175281605275051 9011437908262922407912577)
                ·
                  refine ⟨6758578431197191805934433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9011437908262922407912577 6758578431197191805934433)
                  ·
                    refine ⟨5068933823397893854450825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6758578431197191805934433 5068933823397893854450825)
                    ·
                      refine ⟨3801700367548420390838119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5068933823397893854450825 3801700367548420390838119)
                      ·
                        rfl

theorem cell23_7403785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 2, 2, 2].length) (baseStart_7403785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403785 prefixEnd_7403785 := by exact prefixLift 7403785
  have htrace : WordTrace (prefixWord ++ tailWord_7403785) baseStart_7403785 baseEnd_7403785 := by
    simpa [prefixWord, tailWord_7403785, baseEnd_7403785] using wordTrace_append hprefix tailTrace_7403785
  have hstable : (prefixWord ++ tailWord_7403785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403785).length < 2 ^ (prefixWord ++ tailWord_7403785).sum := by decide
  have hdescent : baseEnd_7403785 < baseStart_7403785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403787 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 3, 7]
def baseStart_7403787 : Nat := 118140960795 + 7403787 * 2 ^ 59
def prefixEnd_7403787 : Nat := 4983230072969 + 3 ^ 40 * 7403787 * 2
def baseEnd_7403787 : Nat := 1267233798169909794337703

theorem tailTrace_7403787 : CollatzResearch.WordTrace tailWord_7403787 prefixEnd_7403787 1267233798169909794337703 := by
  unfold tailWord_7403787
  simp only [CollatzResearch.WordTrace]
  refine ⟨270038296428351639995417615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180025530952234426663611743 270038296428351639995417615)
  ·
    refine ⟨405057444642527459993126423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270038296428351639995417615 405057444642527459993126423)
    ·
      refine ⟨607586166963791189989689635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405057444642527459993126423 607586166963791189989689635)
      ·
        refine ⟨911379250445686784984534453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607586166963791189989689635 911379250445686784984534453)
        ·
          refine ⟨85441804729283136092300105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 911379250445686784984534453 85441804729283136092300105)
          ·
            refine ⟨64081353546962352069225079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85441804729283136092300105 64081353546962352069225079)
            ·
              refine ⟨96122030320443528103837619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64081353546962352069225079 96122030320443528103837619)
              ·
                refine ⟨144183045480665292155756429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96122030320443528103837619 144183045480665292155756429)
                ·
                  refine ⟨54068642055249484558408661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144183045480665292155756429 54068642055249484558408661)
                  ·
                    refine ⟨1267233798169909794337703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54068642055249484558408661 1267233798169909794337703)
                    ·
                      rfl

theorem cell23_7403787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 7].length) (baseStart_7403787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403787 prefixEnd_7403787 := by exact prefixLift 7403787
  have htrace : WordTrace (prefixWord ++ tailWord_7403787) baseStart_7403787 baseEnd_7403787 := by
    simpa [prefixWord, tailWord_7403787, baseEnd_7403787] using wordTrace_append hprefix tailTrace_7403787
  have hstable : (prefixWord ++ tailWord_7403787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403787).length < 2 ^ (prefixWord ++ tailWord_7403787).sum := by decide
  have hdescent : baseEnd_7403787 < baseStart_7403787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403804 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_7403804 : Nat := 118140960795 + 7403804 * 2 ^ 59
def prefixEnd_7403804 : Nat := 4983230072969 + 3 ^ 40 * 7403804 * 2
def baseEnd_7403804 : Nat := 1267236707893618605500177

theorem tailTrace_7403804 : CollatzResearch.WordTrace tailWord_7403804 prefixEnd_7403804 1267236707893618605500177 := by
  unfold tailWord_7403804
  simp only [CollatzResearch.WordTrace]
  refine ⟨135019458234645025949393233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180025944312860034599190977 135019458234645025949393233)
  ·
    refine ⟨101264593675983769462044925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135019458234645025949393233 101264593675983769462044925)
    ·
      refine ⟨37974222628493913548266847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101264593675983769462044925 37974222628493913548266847)
      ·
        refine ⟨56961333942740870322400271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37974222628493913548266847 56961333942740870322400271)
        ·
          refine ⟨85442000914111305483600407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56961333942740870322400271 85442000914111305483600407)
          ·
            refine ⟨128163001371166958225400611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85442000914111305483600407 128163001371166958225400611)
            ·
              refine ⟨192244502056750437338100917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128163001371166958225400611 192244502056750437338100917)
              ·
                refine ⟨18022922067820353500446961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192244502056750437338100917 18022922067820353500446961)
                ·
                  refine ⟨13517191550865265125335221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18022922067820353500446961 13517191550865265125335221)
                  ·
                    refine ⟨1267236707893618605500177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13517191550865265125335221 1267236707893618605500177)
                    ·
                      rfl

theorem cell23_7403804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_7403804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403804 prefixEnd_7403804 := by exact prefixLift 7403804
  have htrace : WordTrace (prefixWord ++ tailWord_7403804) baseStart_7403804 baseEnd_7403804 := by
    simpa [prefixWord, tailWord_7403804, baseEnd_7403804] using wordTrace_append hprefix tailTrace_7403804
  have hstable : (prefixWord ++ tailWord_7403804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403804).length < 2 ^ (prefixWord ++ tailWord_7403804).sum := by decide
  have hdescent : baseEnd_7403804 < baseStart_7403804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403808 : List Nat := [2, 1, 1, 5, 2, 3, 1, 3, 5]
def baseStart_7403808 : Nat := 118140960795 + 7403808 * 2 ^ 59
def prefixEnd_7403808 : Nat := 4983230072969 + 3 ^ 40 * 7403808 * 2
def baseEnd_7403808 : Nat := 422412464178163755650057

theorem tailTrace_7403808 : CollatzResearch.WordTrace tailWord_7403808 prefixEnd_7403808 422412464178163755650057 := by
  unfold tailWord_7403808
  simp only [CollatzResearch.WordTrace]
  refine ⟨135019531180637780290966039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180026041574183707054621385 135019531180637780290966039)
  ·
    refine ⟨202529296770956670436449059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135019531180637780290966039 202529296770956670436449059)
    ·
      refine ⟨303793945156435005654673589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202529296770956670436449059 303793945156435005654673589)
      ·
        refine ⟨28480682358415781780125649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 303793945156435005654673589 28480682358415781780125649)
        ·
          refine ⟨21360511768811836335094237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28480682358415781780125649 21360511768811836335094237)
          ·
            refine ⟨8010191913304438625660339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21360511768811836335094237 8010191913304438625660339)
            ·
              refine ⟨12015287869956657938490509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8010191913304438625660339 12015287869956657938490509)
              ·
                refine ⟨4505732951233746726933941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12015287869956657938490509 4505732951233746726933941)
                ·
                  refine ⟨422412464178163755650057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4505732951233746726933941 422412464178163755650057)
                  ·
                    rfl

theorem cell23_7403808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 5].length) (baseStart_7403808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403808 prefixEnd_7403808 := by exact prefixLift 7403808
  have htrace : WordTrace (prefixWord ++ tailWord_7403808) baseStart_7403808 baseEnd_7403808 := by
    simpa [prefixWord, tailWord_7403808, baseEnd_7403808] using wordTrace_append hprefix tailTrace_7403808
  have hstable : (prefixWord ++ tailWord_7403808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403808).length < 2 ^ (prefixWord ++ tailWord_7403808).sum := by decide
  have hdescent : baseEnd_7403808 < baseStart_7403808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403908 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_7403908 : Nat := 118140960795 + 7403908 * 2 ^ 59
def prefixEnd_7403908 : Nat := 4983230072969 + 3 ^ 40 * 7403908 * 2
def baseEnd_7403908 : Nat := 3801763525668923409600053

theorem tailTrace_7403908 : CollatzResearch.WordTrace tailWord_7403908 prefixEnd_7403908 3801763525668923409600053 := by
  unfold tailWord_7403908
  simp only [CollatzResearch.WordTrace]
  refine ⟨135021354830456638830286189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180028473107275518440381585 135021354830456638830286189)
  ·
    refine ⟨50633008061421239561357321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135021354830456638830286189 50633008061421239561357321)
    ·
      refine ⟨37974756046065929671017991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50633008061421239561357321 37974756046065929671017991)
      ·
        refine ⟨56962134069098894506526987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37974756046065929671017991 56962134069098894506526987)
        ·
          refine ⟨85443201103648341759790481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56962134069098894506526987 85443201103648341759790481)
          ·
            refine ⟨64082400827736256319842861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85443201103648341759790481 64082400827736256319842861)
            ·
              refine ⟨24030900310401096119941073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64082400827736256319842861 24030900310401096119941073)
              ·
                refine ⟨18023175232800822089955805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24030900310401096119941073 18023175232800822089955805)
                ·
                  refine ⟨6758690712300308283733427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18023175232800822089955805 6758690712300308283733427)
                  ·
                    refine ⟨10138036068450462425600141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6758690712300308283733427 10138036068450462425600141)
                    ·
                      refine ⟨3801763525668923409600053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10138036068450462425600141 3801763525668923409600053)
                      ·
                        rfl

theorem cell23_7403908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_7403908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403908 prefixEnd_7403908 := by exact prefixLift 7403908
  have htrace : WordTrace (prefixWord ++ tailWord_7403908) baseStart_7403908 baseEnd_7403908 := by
    simpa [prefixWord, tailWord_7403908, baseEnd_7403908] using wordTrace_append hprefix tailTrace_7403908
  have hstable : (prefixWord ++ tailWord_7403908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403908).length < 2 ^ (prefixWord ++ tailWord_7403908).sum := by decide
  have hdescent : baseEnd_7403908 < baseStart_7403908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403911 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 1, 5]
def baseStart_7403911 : Nat := 118140960795 + 7403911 * 2 ^ 59
def prefixEnd_7403911 : Nat := 4983230072969 + 3 ^ 40 * 7403911 * 2
def baseEnd_7403911 : Nat := 1267255022036962299287513

theorem tailTrace_7403911 : CollatzResearch.WordTrace tailWord_7403911 prefixEnd_7403911 1267255022036962299287513 := by
  unfold tailWord_7403911
  simp only [CollatzResearch.WordTrace]
  refine ⟨270042819079902409172931587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180028546053268272781954391 270042819079902409172931587)
  ·
    refine ⟨405064228619853613759397381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270042819079902409172931587 405064228619853613759397381)
    ·
      refine ⟨75949542866222552579887009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 405064228619853613759397381 75949542866222552579887009)
      ·
        refine ⟨56962157149666914434915257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75949542866222552579887009 56962157149666914434915257)
        ·
          refine ⟨42721617862250185826186443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56962157149666914434915257 42721617862250185826186443)
          ·
            refine ⟨64082426793375278739279665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42721617862250185826186443 64082426793375278739279665)
            ·
              refine ⟨48061820095031459054459749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64082426793375278739279665 48061820095031459054459749)
              ·
                refine ⟨9011591267818398572711203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48061820095031459054459749 9011591267818398572711203)
                ·
                  refine ⟨13517386901727597859066805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9011591267818398572711203 13517386901727597859066805)
                  ·
                    refine ⟨1267255022036962299287513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13517386901727597859066805 1267255022036962299287513)
                    ·
                      rfl

theorem cell23_7403911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_7403911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403911 prefixEnd_7403911 := by exact prefixLift 7403911
  have htrace : WordTrace (prefixWord ++ tailWord_7403911) baseStart_7403911 baseEnd_7403911 := by
    simpa [prefixWord, tailWord_7403911, baseEnd_7403911] using wordTrace_append hprefix tailTrace_7403911
  have hstable : (prefixWord ++ tailWord_7403911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403911).length < 2 ^ (prefixWord ++ tailWord_7403911).sum := by decide
  have hdescent : baseEnd_7403911 < baseStart_7403911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403928 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 1, 5]
def baseStart_7403928 : Nat := 118140960795 + 7403928 * 2 ^ 59
def prefixEnd_7403928 : Nat := 4983230072969 + 3 ^ 40 * 7403928 * 2
def baseEnd_7403928 : Nat := 1267257931760671110449987

theorem tailTrace_7403928 : CollatzResearch.WordTrace tailWord_7403928 prefixEnd_7403928 1267257931760671110449987 := by
  unfold tailWord_7403928
  simp only [CollatzResearch.WordTrace]
  refine ⟨135021719560420410538150219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180028959413893880717533625 135021719560420410538150219)
  ·
    refine ⟨202532579340630615807225329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135021719560420410538150219 202532579340630615807225329)
    ·
      refine ⟨151899434505472961855418997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202532579340630615807225329 151899434505472961855418997)
      ·
        refine ⟨14240571984888090173945531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151899434505472961855418997 14240571984888090173945531)
        ·
          refine ⟨21360857977332135260918297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14240571984888090173945531 21360857977332135260918297)
          ·
            refine ⟨16020643482999101445688723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21360857977332135260918297 16020643482999101445688723)
            ·
              refine ⟨24030965224498652168533085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16020643482999101445688723 24030965224498652168533085)
              ·
                refine ⟨9011611959186994563199907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24030965224498652168533085 9011611959186994563199907)
                ·
                  refine ⟨13517417938780491844799861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9011611959186994563199907 13517417938780491844799861)
                  ·
                    refine ⟨1267257931760671110449987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13517417938780491844799861 1267257931760671110449987)
                    ·
                      rfl

theorem cell23_7403928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_7403928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403928 prefixEnd_7403928 := by exact prefixLift 7403928
  have htrace : WordTrace (prefixWord ++ tailWord_7403928) baseStart_7403928 baseEnd_7403928 := by
    simpa [prefixWord, tailWord_7403928, baseEnd_7403928] using wordTrace_append hprefix tailTrace_7403928
  have hstable : (prefixWord ++ tailWord_7403928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403928).length < 2 ^ (prefixWord ++ tailWord_7403928).sum := by decide
  have hdescent : baseEnd_7403928 < baseStart_7403928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403941 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 4, 4]
def baseStart_7403941 : Nat := 118140960795 + 7403941 * 2 ^ 59
def prefixEnd_7403941 : Nat := 4983230072969 + 3 ^ 40 * 7403941 * 2
def baseEnd_7403941 : Nat := 1267260156843507260162467

theorem tailTrace_7403941 : CollatzResearch.WordTrace tailWord_7403941 prefixEnd_7403941 1267260156843507260162467 := by
  unfold tailWord_7403941
  simp only [CollatzResearch.WordTrace]
  refine ⟨270043913269793724296523677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180029275513195816197682451 270043913269793724296523677)
  ·
    refine ⟨101266467476172646611196379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270043913269793724296523677 101266467476172646611196379)
    ·
      refine ⟨151899701214258969916794569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101266467476172646611196379 151899701214258969916794569)
      ·
        refine ⟨113924775910694227437595927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151899701214258969916794569 113924775910694227437595927)
        ·
          refine ⟨170887163866041341156393891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113924775910694227437595927 170887163866041341156393891)
          ·
            refine ⟨256330745799062011734590837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170887163866041341156393891 256330745799062011734590837)
            ·
              refine ⟨24031007418662063600117891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256330745799062011734590837 24031007418662063600117891)
              ·
                refine ⟨36046511127993095400176837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24031007418662063600117891 36046511127993095400176837)
                ·
                  refine ⟨6758720836498705387533157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36046511127993095400176837 6758720836498705387533157)
                  ·
                    refine ⟨1267260156843507260162467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6758720836498705387533157 1267260156843507260162467)
                    ·
                      rfl

theorem cell23_7403941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_7403941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403941 prefixEnd_7403941 := by exact prefixLift 7403941
  have htrace : WordTrace (prefixWord ++ tailWord_7403941) baseStart_7403941 baseEnd_7403941 := by
    simpa [prefixWord, tailWord_7403941, baseEnd_7403941] using wordTrace_append hprefix tailTrace_7403941
  have hstable : (prefixWord ++ tailWord_7403941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403941).length < 2 ^ (prefixWord ++ tailWord_7403941).sum := by decide
  have hdescent : baseEnd_7403941 < baseStart_7403941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403954 : List Nat := [3, 2, 1, 1, 1, 1, 4, 10]
def baseStart_7403954 : Nat := 118140960795 + 7403954 * 2 ^ 59
def prefixEnd_7403954 : Nat := 4983230072969 + 3 ^ 40 * 7403954 * 2
def baseEnd_7403954 : Nat := 140806931325149267763883

theorem tailTrace_7403954 : CollatzResearch.WordTrace tailWord_7403954 prefixEnd_7403954 140806931325149267763883 := by
  unfold tailWord_7403954
  simp only [CollatzResearch.WordTrace]
  refine ⟨67511096854686656879186729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180029591612497751677831277 67511096854686656879186729)
  ·
    refine ⟨50633322641014992659390047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67511096854686656879186729 50633322641014992659390047)
    ·
      refine ⟨75949983961522488989085071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50633322641014992659390047 75949983961522488989085071)
      ·
        refine ⟨113924975942283733483627607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75949983961522488989085071 113924975942283733483627607)
        ·
          refine ⟨170887463913425600225441411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113924975942283733483627607 170887463913425600225441411)
          ·
            refine ⟨256331195870138400338162117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170887463913425600225441411 256331195870138400338162117)
            ·
              refine ⟨48062099225650950063405397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256331195870138400338162117 48062099225650950063405397)
              ·
                refine ⟨140806931325149267763883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48062099225650950063405397 140806931325149267763883)
                ·
                  rfl

theorem cell23_7403954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 10].length) (baseStart_7403954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403954 prefixEnd_7403954 := by exact prefixLift 7403954
  have htrace : WordTrace (prefixWord ++ tailWord_7403954) baseStart_7403954 baseEnd_7403954 := by
    simpa [prefixWord, tailWord_7403954, baseEnd_7403954] using wordTrace_append hprefix tailTrace_7403954
  have hstable : (prefixWord ++ tailWord_7403954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403954).length < 2 ^ (prefixWord ++ tailWord_7403954).sum := by decide
  have hdescent : baseEnd_7403954 < baseStart_7403954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403961 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 6]
def baseStart_7403961 : Nat := 118140960795 + 7403961 * 2 ^ 59
def prefixEnd_7403961 : Nat := 4983230072969 + 3 ^ 40 * 7403961 * 2
def baseEnd_7403961 : Nat := 3801790740143611702237309

theorem tailTrace_7403961 : CollatzResearch.WordTrace tailWord_7403961 prefixEnd_7403961 3801790740143611702237309 := by
  unfold tailWord_7403961
  simp only [CollatzResearch.WordTrace]
  refine ⟨270044642729721267712251737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180029761819814178474834491 270044642729721267712251737)
  ·
    refine ⟨202533482047290950784188803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270044642729721267712251737 202533482047290950784188803)
    ·
      refine ⟨303800223070936426176283205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202533482047290950784188803 303800223070936426176283205)
      ·
        refine ⟨56962541825800579908053101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303800223070936426176283205 56962541825800579908053101)
        ·
          refine ⟨21360953184675217465519913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56962541825800579908053101 21360953184675217465519913)
          ·
            refine ⟨16020714888506413099139935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21360953184675217465519913 16020714888506413099139935)
            ·
              refine ⟨24031072332759619648709903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16020714888506413099139935 24031072332759619648709903)
              ·
                refine ⟨36046608499139429473064855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24031072332759619648709903 36046608499139429473064855)
                ·
                  refine ⟨54069912748709144209597283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36046608499139429473064855 54069912748709144209597283)
                  ·
                    refine ⟨81104869123063716314395925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54069912748709144209597283 81104869123063716314395925)
                    ·
                      refine ⟨3801790740143611702237309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81104869123063716314395925 3801790740143611702237309)
                      ·
                        rfl

theorem cell23_7403961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_7403961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403961 prefixEnd_7403961 := by exact prefixLift 7403961
  have htrace : WordTrace (prefixWord ++ tailWord_7403961) baseStart_7403961 baseEnd_7403961 := by
    simpa [prefixWord, tailWord_7403961, baseEnd_7403961] using wordTrace_append hprefix tailTrace_7403961
  have hstable : (prefixWord ++ tailWord_7403961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403961).length < 2 ^ (prefixWord ++ tailWord_7403961).sum := by decide
  have hdescent : baseEnd_7403961 < baseStart_7403961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403965 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 3, 2, 2]
def baseStart_7403965 : Nat := 118140960795 + 7403965 * 2 ^ 59
def prefixEnd_7403965 : Nat := 4983230072969 + 3 ^ 40 * 7403965 * 2
def baseEnd_7403965 : Nat := 3801792794066229686587291

theorem tailTrace_7403965 : CollatzResearch.WordTrace tailWord_7403965 prefixEnd_7403965 3801792794066229686587291 := by
  unfold tailWord_7403965
  simp only [CollatzResearch.WordTrace]
  refine ⟨270044788621706776395397349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180029859081137850930264899 270044788621706776395397349)
  ·
    refine ⟨50633397866570020574137003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270044788621706776395397349 50633397866570020574137003)
    ·
      refine ⟨75950096799855030861205505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50633397866570020574137003 75950096799855030861205505)
      ·
        refine ⟨56962572599891273145904129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75950096799855030861205505 56962572599891273145904129)
        ·
          refine ⟨42721929449918454859428097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56962572599891273145904129 42721929449918454859428097)
          ·
            refine ⟨32041447087438841144571073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42721929449918454859428097 32041447087438841144571073)
            ·
              refine ⟨24031085315579130858428305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32041447087438841144571073 24031085315579130858428305)
              ·
                refine ⟨18023313986684348143821229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24031085315579130858428305 18023313986684348143821229)
                ·
                  refine ⟨6758742745006630553932961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18023313986684348143821229 6758742745006630553932961)
                  ·
                    refine ⟨5069057058754972915449721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6758742745006630553932961 5069057058754972915449721)
                    ·
                      refine ⟨3801792794066229686587291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069057058754972915449721 3801792794066229686587291)
                      ·
                        rfl

theorem cell23_7403965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_7403965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403965 prefixEnd_7403965 := by exact prefixLift 7403965
  have htrace : WordTrace (prefixWord ++ tailWord_7403965) baseStart_7403965 baseEnd_7403965 := by
    simpa [prefixWord, tailWord_7403965, baseEnd_7403965] using wordTrace_append hprefix tailTrace_7403965
  have hstable : (prefixWord ++ tailWord_7403965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403965).length < 2 ^ (prefixWord ++ tailWord_7403965).sum := by decide
  have hdescent : baseEnd_7403965 < baseStart_7403965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7403999 : List Nat := [1, 1, 2, 3, 3, 3, 3, 2, 1, 2, 2]
def baseStart_7403999 : Nat := 118140960795 + 7403999 * 2 ^ 59
def prefixEnd_7403999 : Nat := 4983230072969 + 3 ^ 40 * 7403999 * 2
def baseEnd_7403999 : Nat := 3801810252408482553562135

theorem tailTrace_7403999 : CollatzResearch.WordTrace tailWord_7403999 prefixEnd_7403999 3801810252408482553562135 := by
  unfold tailWord_7403999
  simp only [CollatzResearch.WordTrace]
  refine ⟨270046028703583600202135051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180030685802389066801423367 270046028703583600202135051)
  ·
    refine ⟨405069043055375400303202577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270046028703583600202135051 405069043055375400303202577)
    ·
      refine ⟨303801782291531550227401933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405069043055375400303202577 303801782291531550227401933)
      ·
        refine ⟨113925668359324331335275725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303801782291531550227401933 113925668359324331335275725)
        ·
          refine ⟨42722125634746624250728397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113925668359324331335275725 42722125634746624250728397)
          ·
            refine ⟨16020797113029984094023149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42722125634746624250728397 16020797113029984094023149)
            ·
              refine ⟨6007798917386244035258681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16020797113029984094023149 6007798917386244035258681)
              ·
                refine ⟨4505849188039683026444011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6007798917386244035258681 4505849188039683026444011)
                ·
                  refine ⟨6758773782059524539666017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505849188039683026444011 6758773782059524539666017)
                  ·
                    refine ⟨5069080336544643404749513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6758773782059524539666017 5069080336544643404749513)
                    ·
                      refine ⟨3801810252408482553562135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069080336544643404749513 3801810252408482553562135)
                      ·
                        rfl

theorem cell23_7403999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_7403999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7403999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7403999 prefixEnd_7403999 := by exact prefixLift 7403999
  have htrace : WordTrace (prefixWord ++ tailWord_7403999) baseStart_7403999 baseEnd_7403999 := by
    simpa [prefixWord, tailWord_7403999, baseEnd_7403999] using wordTrace_append hprefix tailTrace_7403999
  have hstable : (prefixWord ++ tailWord_7403999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7403999).length < 2 ^ (prefixWord ++ tailWord_7403999).sum := by decide
  have hdescent : baseEnd_7403999 < baseStart_7403999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7403999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404025 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 1, 3, 2]
def baseStart_7404025 : Nat := 118140960795 + 7404025 * 2 ^ 59
def prefixEnd_7404025 : Nat := 4983230072969 + 3 ^ 40 * 7404025 * 2
def baseEnd_7404025 : Nat := 3801823602905499451837015

theorem tailTrace_7404025 : CollatzResearch.WordTrace tailWord_7404025 prefixEnd_7404025 3801823602905499451837015 := by
  unfold tailWord_7404025
  simp only [CollatzResearch.WordTrace]
  refine ⟨270046977001489406642581529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180031318000992937761721019 270046977001489406642581529)
  ·
    refine ⟨202535232751117054981936147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270046977001489406642581529 202535232751117054981936147)
    ·
      refine ⟨303802849126675582472904221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202535232751117054981936147 303802849126675582472904221)
      ·
        refine ⟨113926068422503343427339083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303802849126675582472904221 113926068422503343427339083)
        ·
          refine ⟨170889102633755015141008625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113926068422503343427339083 170889102633755015141008625)
          ·
            refine ⟨128166826975316261355756469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170889102633755015141008625 128166826975316261355756469)
            ·
              refine ⟨12015640028935899502102169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128166826975316261355756469 12015640028935899502102169)
              ·
                refine ⟨9011730021701924626576627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12015640028935899502102169 9011730021701924626576627)
                ·
                  refine ⟨13517595032552886939864941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9011730021701924626576627 13517595032552886939864941)
                  ·
                    refine ⟨5069098137207332602449353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13517595032552886939864941 5069098137207332602449353)
                    ·
                      refine ⟨3801823602905499451837015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069098137207332602449353 3801823602905499451837015)
                      ·
                        rfl

theorem cell23_7404025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_7404025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404025 prefixEnd_7404025 := by exact prefixLift 7404025
  have htrace : WordTrace (prefixWord ++ tailWord_7404025) baseStart_7404025 baseEnd_7404025 := by
    simpa [prefixWord, tailWord_7404025, baseEnd_7404025] using wordTrace_append hprefix tailTrace_7404025
  have hstable : (prefixWord ++ tailWord_7404025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404025).length < 2 ^ (prefixWord ++ tailWord_7404025).sum := by decide
  have hdescent : baseEnd_7404025 < baseStart_7404025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
