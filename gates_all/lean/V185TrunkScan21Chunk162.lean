import V185TrunkScan21Chunk161

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1975954 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 5]
def baseStart_1975954 : Nat := 118140960795 + 1975954 * 2 ^ 59
def prefixEnd_1975954 : Nat := 4983230072969 + 3 ^ 40 * 1975954 * 2
def baseEnd_1975954 : Nat := 450939623633007690927893

theorem tailTrace_1975954 : CollatzResearch.WordTrace tailWord_1975954 prefixEnd_1975954 450939623633007690927893 := by
  unfold tailWord_1975954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18017240770865899730315729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48045975388975732614175277 18017240770865899730315729)
  ·
    refine ⟨13512930578149424797736797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18017240770865899730315729 13512930578149424797736797)
    ·
      refine ⟨5067348966806034299151299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13512930578149424797736797 5067348966806034299151299)
      ·
        refine ⟨7601023450209051448726949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5067348966806034299151299 7601023450209051448726949)
        ·
          refine ⟨1425191896914197146636303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7601023450209051448726949 1425191896914197146636303)
          ·
            refine ⟨2137787845371295719954455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425191896914197146636303 2137787845371295719954455)
            ·
              refine ⟨3206681768056943579931683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137787845371295719954455 3206681768056943579931683)
              ·
                refine ⟨4810022652085415369897525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206681768056943579931683 4810022652085415369897525)
                ·
                  refine ⟨450939623633007690927893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4810022652085415369897525 450939623633007690927893)
                  ·
                    rfl

theorem cell21_1975954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_1975954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975954 prefixEnd_1975954 := by exact prefixLift 1975954
  have htrace : WordTrace (prefixWord ++ tailWord_1975954) baseStart_1975954 baseEnd_1975954 := by
    simpa [prefixWord, tailWord_1975954, baseEnd_1975954] using wordTrace_append hprefix tailTrace_1975954
  have hstable : (prefixWord ++ tailWord_1975954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975954).length < 2 ^ (prefixWord ++ tailWord_1975954).sum := by decide
  have hdescent : baseEnd_1975954 < baseStart_1975954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975968 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 4]
def baseStart_1975968 : Nat := 118140960795 + 1975968 * 2 ^ 59
def prefixEnd_1975968 : Nat := 4983230072969 + 3 ^ 40 * 1975968 * 2
def baseEnd_1975968 : Nat := 450942818623746777694531

theorem tailTrace_1975968 : CollatzResearch.WordTrace tailWord_1975968 prefixEnd_1975968 450942818623746777694531 := by
  unfold tailWord_1975968
  simp only [CollatzResearch.WordTrace]
  refine ⟨36034736852706439656136279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48046315803608586208181705 36034736852706439656136279)
  ·
    refine ⟨54052105279059659484204419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36034736852706439656136279 54052105279059659484204419)
    ·
      refine ⟨81078157918589489226306629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54052105279059659484204419 81078157918589489226306629)
      ·
        refine ⟨15202154609735529229932493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81078157918589489226306629 15202154609735529229932493)
        ·
          refine ⟨5700807978650823461224685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15202154609735529229932493 5700807978650823461224685)
          ·
            refine ⟨2137802991994058797959257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5700807978650823461224685 2137802991994058797959257)
            ·
              refine ⟨1603352243995544098469443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137802991994058797959257 1603352243995544098469443)
              ·
                refine ⟨2405028365993316147704165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603352243995544098469443 2405028365993316147704165)
                ·
                  refine ⟨450942818623746777694531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2405028365993316147704165 450942818623746777694531)
                  ·
                    rfl

theorem cell21_1975968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_1975968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975968 prefixEnd_1975968 := by exact prefixLift 1975968
  have htrace : WordTrace (prefixWord ++ tailWord_1975968) baseStart_1975968 baseEnd_1975968 := by
    simpa [prefixWord, tailWord_1975968, baseEnd_1975968] using wordTrace_append hprefix tailTrace_1975968
  have hstable : (prefixWord ++ tailWord_1975968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975968).length < 2 ^ (prefixWord ++ tailWord_1975968).sum := by decide
  have hdescent : baseEnd_1975968 < baseStart_1975968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975993 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 8]
def baseStart_1975993 : Nat := 118140960795 + 1975993 * 2 ^ 59
def prefixEnd_1975993 : Nat := 4983230072969 + 3 ^ 40 * 1975993 * 2
def baseEnd_1975993 : Nat := 450948523964352289777813

theorem tailTrace_1975993 : CollatzResearch.WordTrace tailWord_1975993 prefixEnd_1975993 450948523964352289777813 := by
  unfold tailWord_1975993
  simp only [CollatzResearch.WordTrace]
  refine ⟨72070385530322308581932633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48046923686881539054621755 72070385530322308581932633)
  ·
    refine ⟨54052789147741731436449475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72070385530322308581932633 54052789147741731436449475)
    ·
      refine ⟨81079183721612597154674213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54052789147741731436449475 81079183721612597154674213)
      ·
        refine ⟨15202346947802361966501415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81079183721612597154674213 15202346947802361966501415)
        ·
          refine ⟨22803520421703542949752123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15202346947802361966501415 22803520421703542949752123)
          ·
            refine ⟨34205280632555314424628185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22803520421703542949752123 34205280632555314424628185)
            ·
              refine ⟨25653960474416485818471139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34205280632555314424628185 25653960474416485818471139)
              ·
                refine ⟨38480940711624728727706709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25653960474416485818471139 38480940711624728727706709)
                ·
                  refine ⟨450948523964352289777813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38480940711624728727706709 450948523964352289777813)
                  ·
                    rfl

theorem cell21_1975993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_1975993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975993 prefixEnd_1975993 := by exact prefixLift 1975993
  have htrace : WordTrace (prefixWord ++ tailWord_1975993) baseStart_1975993 baseEnd_1975993 := by
    simpa [prefixWord, tailWord_1975993, baseEnd_1975993] using wordTrace_append hprefix tailTrace_1975993
  have hstable : (prefixWord ++ tailWord_1975993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975993).length < 2 ^ (prefixWord ++ tailWord_1975993).sum := by decide
  have hdescent : baseEnd_1975993 < baseStart_1975993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976002 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1976002 : Nat := 118140960795 + 1976002 * 2 ^ 59
def prefixEnd_1976002 : Nat := 4983230072969 + 3 ^ 40 * 1976002 * 2
def baseEnd_1976002 : Nat := 450950577886970274127795

theorem tailTrace_1976002 : CollatzResearch.WordTrace tailWord_1976002 prefixEnd_1976002 450950577886970274127795 := by
  unfold tailWord_1976002
  simp only [CollatzResearch.WordTrace]
  refine ⟨18017678446822425779752565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48047142524859802079340173 18017678446822425779752565)
  ·
    refine ⟨1689157354389602416851803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18017678446822425779752565 1689157354389602416851803)
    ·
      refine ⟨2533736031584403625277705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1689157354389602416851803 2533736031584403625277705)
      ·
        refine ⟨1900302023688302718958279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2533736031584403625277705 1900302023688302718958279)
        ·
          refine ⟨2850453035532454078437419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900302023688302718958279 2850453035532454078437419)
          ·
            refine ⟨4275679553298681117656129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850453035532454078437419 4275679553298681117656129)
            ·
              refine ⟨3206759664974010838242097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4275679553298681117656129 3206759664974010838242097)
              ·
                refine ⟨2405069748730508128681573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206759664974010838242097 2405069748730508128681573)
                ·
                  refine ⟨450950577886970274127795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2405069748730508128681573 450950577886970274127795)
                  ·
                    rfl

theorem cell21_1976002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1976002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976002 prefixEnd_1976002 := by exact prefixLift 1976002
  have htrace : WordTrace (prefixWord ++ tailWord_1976002) baseStart_1976002 baseEnd_1976002 := by
    simpa [prefixWord, tailWord_1976002, baseEnd_1976002] using wordTrace_append hprefix tailTrace_1976002
  have hstable : (prefixWord ++ tailWord_1976002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976002).length < 2 ^ (prefixWord ++ tailWord_1976002).sum := by decide
  have hdescent : baseEnd_1976002 < baseStart_1976002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976072 : List Nat := [2, 1, 3, 2, 2, 1, 1, 6, 3]
def baseStart_1976072 : Nat := 118140960795 + 1976072 * 2 ^ 59
def prefixEnd_1976072 : Nat := 4983230072969 + 3 ^ 40 * 1976072 * 2
def baseEnd_1976072 : Nat := 450966552840665707960985

theorem tailTrace_1976072 : CollatzResearch.WordTrace tailWord_1976072 prefixEnd_1976072 450966552840665707960985 := by
  unfold tailWord_1976072
  simp only [CollatzResearch.WordTrace]
  refine ⟨36036633448518052537029235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48048844598024070049372313 36036633448518052537029235)
  ·
    refine ⟨54054950172777078805543853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36036633448518052537029235 54054950172777078805543853)
    ·
      refine ⟨20270606314791404552078945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54054950172777078805543853 20270606314791404552078945)
      ·
        refine ⟨15202954736093553414059209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20270606314791404552078945 15202954736093553414059209)
        ·
          refine ⟨11402216052070165060544407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15202954736093553414059209 11402216052070165060544407)
          ·
            refine ⟨17103324078105247590816611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11402216052070165060544407 17103324078105247590816611)
            ·
              refine ⟨25654986117157871386224917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17103324078105247590816611 25654986117157871386224917)
              ·
                refine ⟨1202577474241775221229293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25654986117157871386224917 1202577474241775221229293)
                ·
                  refine ⟨450966552840665707960985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202577474241775221229293 450966552840665707960985)
                  ·
                    rfl

theorem cell21_1976072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 3].length) (baseStart_1976072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976072 prefixEnd_1976072 := by exact prefixLift 1976072
  have htrace : WordTrace (prefixWord ++ tailWord_1976072) baseStart_1976072 baseEnd_1976072 := by
    simpa [prefixWord, tailWord_1976072, baseEnd_1976072] using wordTrace_append hprefix tailTrace_1976072
  have hstable : (prefixWord ++ tailWord_1976072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976072).length < 2 ^ (prefixWord ++ tailWord_1976072).sum := by decide
  have hdescent : baseEnd_1976072 < baseStart_1976072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976117 : List Nat := [1, 3, 3, 1, 4, 2, 7]
def baseStart_1976117 : Nat := 118140960795 + 1976117 * 2 ^ 59
def prefixEnd_1976117 : Nat := 4983230072969 + 3 ^ 40 * 1976117 * 2
def baseEnd_1976117 : Nat := 50108535828195069967877

theorem tailTrace_1976117 : CollatzResearch.WordTrace tailWord_1976117 prefixEnd_1976117 50108535828195069967877 := by
  unfold tailWord_1976117
  simp only [CollatzResearch.WordTrace]
  refine ⟨72074908181873077759446605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48049938787915385172964403 72074908181873077759446605)
  ·
    refine ⟨27028090568202404159792477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72074908181873077759446605 27028090568202404159792477)
    ·
      refine ⟨10135533963075901559922179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27028090568202404159792477 10135533963075901559922179)
      ·
        refine ⟨15203300944613852339883269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10135533963075901559922179 15203300944613852339883269)
        ·
          refine ⟨2850618927115097313728113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15203300944613852339883269 2850618927115097313728113)
          ·
            refine ⟨2137964195336322985296085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2850618927115097313728113 2137964195336322985296085)
            ·
              refine ⟨50108535828195069967877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2137964195336322985296085 50108535828195069967877)
              ·
                rfl

theorem cell21_1976117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 7].length) (baseStart_1976117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976117 prefixEnd_1976117 := by exact prefixLift 1976117
  have htrace : WordTrace (prefixWord ++ tailWord_1976117) baseStart_1976117 baseEnd_1976117 := by
    simpa [prefixWord, tailWord_1976117, baseEnd_1976117] using wordTrace_append hprefix tailTrace_1976117
  have hstable : (prefixWord ++ tailWord_1976117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976117).length < 2 ^ (prefixWord ++ tailWord_1976117).sum := by decide
  have hdescent : baseEnd_1976117 < baseStart_1976117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976131 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 5]
def baseStart_1976131 : Nat := 118140960795 + 1976131 * 2 ^ 59
def prefixEnd_1976131 : Nat := 4983230072969 + 3 ^ 40 * 1976131 * 2
def baseEnd_1976131 : Nat := 450980017444494716477531

theorem tailTrace_1976131 : CollatzResearch.WordTrace tailWord_1976131 prefixEnd_1976131 450980017444494716477531 := by
  unfold tailWord_1976131
  simp only [CollatzResearch.WordTrace]
  refine ⟨72075418803822358150456247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48050279202548238766970831 72075418803822358150456247)
  ·
    refine ⟨108113128205733537225684371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72075418803822358150456247 108113128205733537225684371)
    ·
      refine ⟨162169692308600305838526557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108113128205733537225684371 162169692308600305838526557)
      ·
        refine ⟨60813634615725114689447459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162169692308600305838526557 60813634615725114689447459)
        ·
          refine ⟨91220451923587672034171189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60813634615725114689447459 91220451923587672034171189)
          ·
            refine ⟨8551917367836344253203549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91220451923587672034171189 8551917367836344253203549)
            ·
              refine ⟨3206969012938629094951331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8551917367836344253203549 3206969012938629094951331)
              ·
                refine ⟨4810453519407943642426997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206969012938629094951331 4810453519407943642426997)
                ·
                  refine ⟨450980017444494716477531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4810453519407943642426997 450980017444494716477531)
                  ·
                    rfl

theorem cell21_1976131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 5].length) (baseStart_1976131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976131 prefixEnd_1976131 := by exact prefixLift 1976131
  have htrace : WordTrace (prefixWord ++ tailWord_1976131) baseStart_1976131 baseEnd_1976131 := by
    simpa [prefixWord, tailWord_1976131, baseEnd_1976131] using wordTrace_append hprefix tailTrace_1976131
  have hstable : (prefixWord ++ tailWord_1976131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976131).length < 2 ^ (prefixWord ++ tailWord_1976131).sum := by decide
  have hdescent : baseEnd_1976131 < baseStart_1976131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976134 : List Nat := [6, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1976134 : Nat := 118140960795 + 1976134 * 2 ^ 59
def prefixEnd_1976134 : Nat := 4983230072969 + 3 ^ 40 * 1976134 * 2
def baseEnd_1976134 : Nat := 150326900695122459309175

theorem tailTrace_1976134 : CollatzResearch.WordTrace tailWord_1976134 prefixEnd_1976134 150326900695122459309175 := by
  unfold tailWord_1976134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252360256962859051962983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48050352148540993108543637 2252360256962859051962983)
  ·
    refine ⟨3378540385444288577944475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2252360256962859051962983 3378540385444288577944475)
    ·
      refine ⟨5067810578166432866916713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3378540385444288577944475 5067810578166432866916713)
      ·
        refine ⟨3800857933624824650187535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5067810578166432866916713 3800857933624824650187535)
        ·
          refine ⟨5701286900437236975281303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800857933624824650187535 5701286900437236975281303)
          ·
            refine ⟨8551930350655855462921955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5701286900437236975281303 8551930350655855462921955)
            ·
              refine ⟨12827895525983783194382933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8551930350655855462921955 12827895525983783194382933)
              ·
                refine ⟨150326900695122459309175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12827895525983783194382933 150326900695122459309175)
                ·
                  rfl

theorem cell21_1976134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1976134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976134 prefixEnd_1976134 := by exact prefixLift 1976134
  have htrace : WordTrace (prefixWord ++ tailWord_1976134) baseStart_1976134 baseEnd_1976134 := by
    simpa [prefixWord, tailWord_1976134, baseEnd_1976134] using wordTrace_append hprefix tailTrace_1976134
  have hstable : (prefixWord ++ tailWord_1976134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976134).length < 2 ^ (prefixWord ++ tailWord_1976134).sum := by decide
  have hdescent : baseEnd_1976134 < baseStart_1976134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976182 : List Nat := [5, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_1976182 : Nat := 118140960795 + 1976182 * 2 ^ 59
def prefixEnd_1976182 : Nat := 4983230072969 + 3 ^ 40 * 1976182 * 2
def baseEnd_1976182 : Nat := 450991656339329961127427

theorem tailTrace_1976182 : CollatzResearch.WordTrace tailWord_1976182 prefixEnd_1976182 450991656339329961127427 := by
  unfold tailWord_1976182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4504829932914849616285175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48051519284425062573708533 4504829932914849616285175)
  ·
    refine ⟨6757244899372274424427763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4504829932914849616285175 6757244899372274424427763)
    ·
      refine ⟨10135867349058411636641645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6757244899372274424427763 10135867349058411636641645)
      ·
        refine ⟨3800950255896904363740617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10135867349058411636641645 3800950255896904363740617)
        ·
          refine ⟨2850712691922678272805463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3800950255896904363740617 2850712691922678272805463)
          ·
            refine ⟨4276069037884017409208195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850712691922678272805463 4276069037884017409208195)
            ·
              refine ⟨6414103556826026113812293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4276069037884017409208195 6414103556826026113812293)
              ·
                refine ⟨1202644416904879896339805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6414103556826026113812293 1202644416904879896339805)
                ·
                  refine ⟨450991656339329961127427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202644416904879896339805 450991656339329961127427)
                  ·
                    rfl

theorem cell21_1976182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_1976182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976182 prefixEnd_1976182 := by exact prefixLift 1976182
  have htrace : WordTrace (prefixWord ++ tailWord_1976182) baseStart_1976182 baseEnd_1976182 := by
    simpa [prefixWord, tailWord_1976182, baseEnd_1976182] using wordTrace_append hprefix tailTrace_1976182
  have hstable : (prefixWord ++ tailWord_1976182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976182).length < 2 ^ (prefixWord ++ tailWord_1976182).sum := by decide
  have hdescent : baseEnd_1976182 < baseStart_1976182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976210 : List Nat := [3, 2, 3, 2, 1, 2, 3, 5]
def baseStart_1976210 : Nat := 118140960795 + 1976210 * 2 ^ 59
def prefixEnd_1976210 : Nat := 4983230072969 + 3 ^ 40 * 1976210 * 2
def baseEnd_1976210 : Nat := 150332682106936044886901

theorem tailTrace_1976210 : CollatzResearch.WordTrace tailWord_1976210 prefixEnd_1976210 150332682106936044886901 := by
  unfold tailWord_1976210
  simp only [CollatzResearch.WordTrace]
  refine ⟨18019575042634038660645521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48052200113690769761721389 18019575042634038660645521)
  ·
    refine ⟨13514681281975528995484141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18019575042634038660645521 13514681281975528995484141)
    ·
      refine ⟨5068005480740823373306553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13514681281975528995484141 5068005480740823373306553)
      ·
        refine ⟨3801004110555617529979915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5068005480740823373306553 3801004110555617529979915)
        ·
          refine ⟨5701506165833426294969873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3801004110555617529979915 5701506165833426294969873)
          ·
            refine ⟨4276129624375069721227405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5701506165833426294969873 4276129624375069721227405)
            ·
              refine ⟨1603548609140651145460277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4276129624375069721227405 1603548609140651145460277)
              ·
                refine ⟨150332682106936044886901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1603548609140651145460277 150332682106936044886901)
                ·
                  rfl

theorem cell21_1976210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_1976210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976210 prefixEnd_1976210 := by exact prefixLift 1976210
  have htrace : WordTrace (prefixWord ++ tailWord_1976210) baseStart_1976210 baseEnd_1976210 := by
    simpa [prefixWord, tailWord_1976210, baseEnd_1976210] using wordTrace_append hprefix tailTrace_1976210
  have hstable : (prefixWord ++ tailWord_1976210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976210).length < 2 ^ (prefixWord ++ tailWord_1976210).sum := by decide
  have hdescent : baseEnd_1976210 < baseStart_1976210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976438 : List Nat := [5, 1, 1, 2, 1, 4, 2, 5]
def baseStart_1976438 : Nat := 118140960795 + 1976438 * 2 ^ 59
def prefixEnd_1976438 : Nat := 4983230072969 + 3 ^ 40 * 1976438 * 2
def baseEnd_1976438 : Nat := 150350026342376801620079

theorem tailTrace_1976438 : CollatzResearch.WordTrace tailWord_1976438 prefixEnd_1976438 150350026342376801620079 := by
  unfold tailWord_1976438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4505413500856884348867623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48057744009140099721254645 4505413500856884348867623)
  ·
    refine ⟨6758120251285326523301435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4505413500856884348867623 6758120251285326523301435)
    ·
      refine ⟨10137180376927989784952153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6758120251285326523301435 10137180376927989784952153)
      ·
        refine ⟨7602885282695992338714115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10137180376927989784952153 7602885282695992338714115)
        ·
          refine ⟨11404327924043988508071173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7602885282695992338714115 11404327924043988508071173)
          ·
            refine ⟨2138311485758247845263345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11404327924043988508071173 2138311485758247845263345)
            ·
              refine ⟨1603733614318685883947509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2138311485758247845263345 1603733614318685883947509)
              ·
                refine ⟨150350026342376801620079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1603733614318685883947509 150350026342376801620079)
                ·
                  rfl

theorem cell21_1976438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_1976438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976438 prefixEnd_1976438 := by exact prefixLift 1976438
  have htrace : WordTrace (prefixWord ++ tailWord_1976438) baseStart_1976438 baseEnd_1976438 := by
    simpa [prefixWord, tailWord_1976438, baseEnd_1976438] using wordTrace_append hprefix tailTrace_1976438
  have hstable : (prefixWord ++ tailWord_1976438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976438).length < 2 ^ (prefixWord ++ tailWord_1976438).sum := by decide
  have hdescent : baseEnd_1976438 < baseStart_1976438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976466 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1976466 : Nat := 118140960795 + 1976466 * 2 ^ 59
def prefixEnd_1976466 : Nat := 4983230072969 + 3 ^ 40 * 1976466 * 2
def baseEnd_1976466 : Nat := 451056469008608578393513

theorem tailTrace_1976466 : CollatzResearch.WordTrace tailWord_1976466 prefixEnd_1976466 451056469008608578393513 := by
  unfold tailWord_1976466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18021909314402177590975313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48058424838405806909267501 18021909314402177590975313)
  ·
    refine ⟨13516431985801633193231485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18021909314402177590975313 13516431985801633193231485)
    ·
      refine ⟨5068661994675612447461807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13516431985801633193231485 5068661994675612447461807)
      ·
        refine ⟨7602992992013418671192711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5068661994675612447461807 7602992992013418671192711)
        ·
          refine ⟨11404489488020128006789067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7602992992013418671192711 11404489488020128006789067)
          ·
            refine ⟨17106734232030192010183601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11404489488020128006789067 17106734232030192010183601)
            ·
              refine ⟨12830050674022644007637701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17106734232030192010183601 12830050674022644007637701)
              ·
                refine ⟨2405634501379245751432069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12830050674022644007637701 2405634501379245751432069)
                ·
                  refine ⟨451056469008608578393513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2405634501379245751432069 451056469008608578393513)
                  ·
                    rfl

theorem cell21_1976466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1976466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976466 prefixEnd_1976466 := by exact prefixLift 1976466
  have htrace : WordTrace (prefixWord ++ tailWord_1976466) baseStart_1976466 baseEnd_1976466 := by
    simpa [prefixWord, tailWord_1976466, baseEnd_1976466] using wordTrace_append hprefix tailTrace_1976466
  have hstable : (prefixWord ++ tailWord_1976466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976466).length < 2 ^ (prefixWord ++ tailWord_1976466).sum := by decide
  have hdescent : baseEnd_1976466 < baseStart_1976466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976480 : List Nat := [2, 1, 1, 4, 2, 3, 2, 6]
def baseStart_1976480 : Nat := 118140960795 + 1976480 * 2 ^ 59
def prefixEnd_1976480 : Nat := 4983230072969 + 3 ^ 40 * 1976480 * 2
def baseEnd_1976480 : Nat := 150353221333115888386717

theorem tailTrace_1976480 : CollatzResearch.WordTrace tailWord_1976480 prefixEnd_1976480 150353221333115888386717 := by
  unfold tailWord_1976480
  simp only [CollatzResearch.WordTrace]
  refine ⟨36044073939778995377455447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48058765253038660503273929 36044073939778995377455447)
  ·
    refine ⟨54066110909668493066183171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36044073939778995377455447 54066110909668493066183171)
    ·
      refine ⟨81099166364502739599274757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54066110909668493066183171 81099166364502739599274757)
      ·
        refine ⟨15206093693344263674864017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81099166364502739599274757 15206093693344263674864017)
        ·
          refine ⟨11404570270008197756148013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15206093693344263674864017 11404570270008197756148013)
          ·
            refine ⟨4276713851253074158555505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11404570270008197756148013 4276713851253074158555505)
            ·
              refine ⟨3207535388439805618916629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4276713851253074158555505 3207535388439805618916629)
              ·
                refine ⟨150353221333115888386717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3207535388439805618916629 150353221333115888386717)
                ·
                  rfl

theorem cell21_1976480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_1976480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976480 prefixEnd_1976480 := by exact prefixLift 1976480
  have htrace : WordTrace (prefixWord ++ tailWord_1976480) baseStart_1976480 baseEnd_1976480 := by
    simpa [prefixWord, tailWord_1976480, baseEnd_1976480] using wordTrace_append hprefix tailTrace_1976480
  have hstable : (prefixWord ++ tailWord_1976480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976480).length < 2 ^ (prefixWord ++ tailWord_1976480).sum := by decide
  have hdescent : baseEnd_1976480 < baseStart_1976480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976511 : List Nat := [1, 1, 2, 2, 2, 2, 1, 7, 3]
def baseStart_1976511 : Nat := 118140960795 + 1976511 * 2 ^ 59
def prefixEnd_1976511 : Nat := 4983230072969 + 3 ^ 40 * 1976511 * 2
def baseEnd_1976511 : Nat := 451066738621698500143421

theorem tailTrace_1976511 : CollatzResearch.WordTrace tailWord_1976511 prefixEnd_1976511 451066738621698500143421 := by
  unfold tailWord_1976511
  simp only [CollatzResearch.WordTrace]
  refine ⟨72089278542445683049289387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48059519028297122032859591 72089278542445683049289387)
  ·
    refine ⟨108133917813668524573934081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72089278542445683049289387 108133917813668524573934081)
    ·
      refine ⟨81100438360251393430450561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108133917813668524573934081 81100438360251393430450561)
      ·
        refine ⟨60825328770188545072837921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81100438360251393430450561 60825328770188545072837921)
        ·
          refine ⟨45618996577641408804628441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60825328770188545072837921 45618996577641408804628441)
          ·
            refine ⟨34214247433231056603471331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45618996577641408804628441 34214247433231056603471331)
            ·
              refine ⟨51321371149846584905206997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34214247433231056603471331 51321371149846584905206997)
              ·
                refine ⟨1202844636324529333715789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51321371149846584905206997 1202844636324529333715789)
                ·
                  refine ⟨451066738621698500143421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202844636324529333715789 451066738621698500143421)
                  ·
                    rfl

theorem cell21_1976511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 3].length) (baseStart_1976511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976511 prefixEnd_1976511 := by exact prefixLift 1976511
  have htrace : WordTrace (prefixWord ++ tailWord_1976511) baseStart_1976511 baseEnd_1976511 := by
    simpa [prefixWord, tailWord_1976511, baseEnd_1976511] using wordTrace_append hprefix tailTrace_1976511
  have hstable : (prefixWord ++ tailWord_1976511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976511).length < 2 ^ (prefixWord ++ tailWord_1976511).sum := by decide
  have hdescent : baseEnd_1976511 < baseStart_1976511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976556 : List Nat := [2, 2, 1, 1, 2, 3, 5, 5]
def baseStart_1976556 : Nat := 118140960795 + 1976556 * 2 ^ 59
def prefixEnd_1976556 : Nat := 4983230072969 + 3 ^ 40 * 1976556 * 2
def baseEnd_1976556 : Nat := 150359002744929473964443

theorem tailTrace_1976556 : CollatzResearch.WordTrace tailWord_1976556 prefixEnd_1976556 150359002744929473964443 := by
  unfold tailWord_1976556
  simp only [CollatzResearch.WordTrace]
  refine ⟨36045459913641327867338761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48060613218188437156451681 36045459913641327867338761)
  ·
    refine ⟨27034094935230995900504071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36045459913641327867338761 27034094935230995900504071)
    ·
      refine ⟨40551142402846493850756107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27034094935230995900504071 40551142402846493850756107)
      ·
        refine ⟨60826713604269740776134161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40551142402846493850756107 60826713604269740776134161)
        ·
          refine ⟨45620035203202305582100621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60826713604269740776134161 45620035203202305582100621)
          ·
            refine ⟨17107513201200864593287733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45620035203202305582100621 17107513201200864593287733)
            ·
              refine ⟨1603829362612581055620725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17107513201200864593287733 1603829362612581055620725)
              ·
                refine ⟨150359002744929473964443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1603829362612581055620725 150359002744929473964443)
                ·
                  rfl

theorem cell21_1976556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_1976556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976556 prefixEnd_1976556 := by exact prefixLift 1976556
  have htrace : WordTrace (prefixWord ++ tailWord_1976556) baseStart_1976556 baseEnd_1976556 := by
    simpa [prefixWord, tailWord_1976556, baseEnd_1976556] using wordTrace_append hprefix tailTrace_1976556
  have hstable : (prefixWord ++ tailWord_1976556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976556).length < 2 ^ (prefixWord ++ tailWord_1976556).sum := by decide
  have hdescent : baseEnd_1976556 < baseStart_1976556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976587 : List Nat := [1, 1, 1, 1, 5, 2, 1, 6, 3]
def baseStart_1976587 : Nat := 118140960795 + 1976587 * 2 ^ 59
def prefixEnd_1976587 : Nat := 4983230072969 + 3 ^ 40 * 1976587 * 2
def baseEnd_1976587 : Nat := 451084082857139256876599

theorem tailTrace_1976587 : CollatzResearch.WordTrace tailWord_1976587 prefixEnd_1976587 451084082857139256876599 := by
  unfold tailWord_1976587
  simp only [CollatzResearch.WordTrace]
  refine ⟨72092050490170348029056015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48061366993446898686037343 72092050490170348029056015)
  ·
    refine ⟨108138075735255522043584023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72092050490170348029056015 108138075735255522043584023)
    ·
      refine ⟨162207113602883283065376035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108138075735255522043584023 162207113602883283065376035)
      ·
        refine ⟨243310670404324924598064053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162207113602883283065376035 243310670404324924598064053)
        ·
          refine ⟨22810375350405461681068505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243310670404324924598064053 22810375350405461681068505)
          ·
            refine ⟨17107781512804096260801379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22810375350405461681068505 17107781512804096260801379)
            ·
              refine ⟨25661672269206144391202069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17107781512804096260801379 25661672269206144391202069)
              ·
                refine ⟨1202890887619038018337597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25661672269206144391202069 1202890887619038018337597)
                ·
                  refine ⟨451084082857139256876599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202890887619038018337597 451084082857139256876599)
                  ·
                    rfl

theorem cell21_1976587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 3].length) (baseStart_1976587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976587 prefixEnd_1976587 := by exact prefixLift 1976587
  have htrace : WordTrace (prefixWord ++ tailWord_1976587) baseStart_1976587 baseEnd_1976587 := by
    simpa [prefixWord, tailWord_1976587, baseEnd_1976587] using wordTrace_append hprefix tailTrace_1976587
  have hstable : (prefixWord ++ tailWord_1976587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976587).length < 2 ^ (prefixWord ++ tailWord_1976587).sum := by decide
  have hdescent : baseEnd_1976587 < baseStart_1976587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976739 : List Nat := [1, 1, 1, 4, 1, 4, 1, 5, 3]
def baseStart_1976739 : Nat := 118140960795 + 1976739 * 2 ^ 59
def prefixEnd_1976739 : Nat := 4983230072969 + 3 ^ 40 * 1976739 * 2
def baseEnd_1976739 : Nat := 451118771328020770342955

theorem tailTrace_1976739 : CollatzResearch.WordTrace tailWord_1976739 prefixEnd_1976739 451118771328020770342955 := by
  unfold tailWord_1976739
  simp only [CollatzResearch.WordTrace]
  refine ⟨72097594385619677988589271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48065062923746451992392847 72097594385619677988589271)
  ·
    refine ⟨108146391578429516982883907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72097594385619677988589271 108146391578429516982883907)
    ·
      refine ⟨162219587367644275474325861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108146391578429516982883907 162219587367644275474325861)
      ·
        refine ⟨30416172631433301651436099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162219587367644275474325861 30416172631433301651436099)
        ·
          refine ⟨45624258947149952477154149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30416172631433301651436099 45624258947149952477154149)
          ·
            refine ⟨8554548552590616089466403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45624258947149952477154149 8554548552590616089466403)
            ·
              refine ⟨12831822828885924134199605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8554548552590616089466403 12831822828885924134199605)
              ·
                refine ⟨1202983390208055387581213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12831822828885924134199605 1202983390208055387581213)
                ·
                  refine ⟨451118771328020770342955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202983390208055387581213 451118771328020770342955)
                  ·
                    rfl

theorem cell21_1976739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 3].length) (baseStart_1976739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976739 prefixEnd_1976739 := by exact prefixLift 1976739
  have htrace : WordTrace (prefixWord ++ tailWord_1976739) baseStart_1976739 baseEnd_1976739 := by
    simpa [prefixWord, tailWord_1976739, baseEnd_1976739] using wordTrace_append hprefix tailTrace_1976739
  have hstable : (prefixWord ++ tailWord_1976739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976739).length < 2 ^ (prefixWord ++ tailWord_1976739).sum := by decide
  have hdescent : baseEnd_1976739 < baseStart_1976739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976753 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 6]
def baseStart_1976753 : Nat := 118140960795 + 1976753 * 2 ^ 59
def prefixEnd_1976753 : Nat := 4983230072969 + 3 ^ 40 * 1976753 * 2
def baseEnd_1976753 : Nat := 451121966318759857109593

theorem tailTrace_1976753 : CollatzResearch.WordTrace tailWord_1976753 prefixEnd_1976753 451121966318759857109593 := by
  unfold tailWord_1976753
  simp only [CollatzResearch.WordTrace]
  refine ⟨72098105007568958379598913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48065403338379305586399275 72098105007568958379598913)
  ·
    refine ⟨54073578755676718784699185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72098105007568958379598913 54073578755676718784699185)
    ·
      refine ⟨40555184066757539088524389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54073578755676718784699185 40555184066757539088524389)
      ·
        refine ⟨7604097012517038579098323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40555184066757539088524389 7604097012517038579098323)
        ·
          refine ⟨11406145518775557868647485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7604097012517038579098323 11406145518775557868647485)
          ·
            refine ⟨4277304569540834200742807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11406145518775557868647485 4277304569540834200742807)
            ·
              refine ⟨6415956854311251301114211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277304569540834200742807 6415956854311251301114211)
              ·
                refine ⟨9623935281466876951671317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415956854311251301114211 9623935281466876951671317)
                ·
                  refine ⟨451121966318759857109593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9623935281466876951671317 451121966318759857109593)
                  ·
                    rfl

theorem cell21_1976753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_1976753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976753 prefixEnd_1976753 := by exact prefixLift 1976753
  have htrace : WordTrace (prefixWord ++ tailWord_1976753) baseStart_1976753 baseEnd_1976753 := by
    simpa [prefixWord, tailWord_1976753, baseEnd_1976753] using wordTrace_append hprefix tailTrace_1976753
  have hstable : (prefixWord ++ tailWord_1976753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976753).length < 2 ^ (prefixWord ++ tailWord_1976753).sum := by decide
  have hdescent : baseEnd_1976753 < baseStart_1976753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976812 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_1976812 : Nat := 118140960795 + 1976812 * 2 ^ 59
def prefixEnd_1976812 : Nat := 4983230072969 + 3 ^ 40 * 1976812 * 2
def baseEnd_1976812 : Nat := 451135430922588865626139

theorem tailTrace_1976812 : CollatzResearch.WordTrace tailWord_1976812 prefixEnd_1976812 451135430922588865626139 := by
  unfold tailWord_1976812
  simp only [CollatzResearch.WordTrace]
  refine ⟨36050128457177605727998345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48066837942903474303997793 36050128457177605727998345)
  ·
    refine ⟨27037596342883204295998759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36050128457177605727998345 27037596342883204295998759)
    ·
      refine ⟨40556394514324806443998139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27037596342883204295998759 40556394514324806443998139)
      ·
        refine ⟨60834591771487209665997209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40556394514324806443998139 60834591771487209665997209)
        ·
          refine ⟨45625943828615407249497907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60834591771487209665997209 45625943828615407249497907)
          ·
            refine ⟨68438915742923110874246861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45625943828615407249497907 68438915742923110874246861)
            ·
              refine ⟨25664593403596166577842573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68438915742923110874246861 25664593403596166577842573)
              ·
                refine ⟨9624222526348562466690965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25664593403596166577842573 9624222526348562466690965)
                ·
                  refine ⟨451135430922588865626139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9624222526348562466690965 451135430922588865626139)
                  ·
                    rfl

theorem cell21_1976812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_1976812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976812 prefixEnd_1976812 := by exact prefixLift 1976812
  have htrace : WordTrace (prefixWord ++ tailWord_1976812) baseStart_1976812 baseEnd_1976812 := by
    simpa [prefixWord, tailWord_1976812, baseEnd_1976812] using wordTrace_append hprefix tailTrace_1976812
  have hstable : (prefixWord ++ tailWord_1976812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976812).length < 2 ^ (prefixWord ++ tailWord_1976812).sum := by decide
  have hdescent : baseEnd_1976812 < baseStart_1976812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976821 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 4]
def baseStart_1976821 : Nat := 118140960795 + 1976821 * 2 ^ 59
def prefixEnd_1976821 : Nat := 4983230072969 + 3 ^ 40 * 1976821 * 2
def baseEnd_1976821 : Nat := 451137484845206849976121

theorem tailTrace_1976821 : CollatzResearch.WordTrace tailWord_1976821 prefixEnd_1976821 451137484845206849976121 := by
  unfold tailWord_1976821
  simp only [CollatzResearch.WordTrace]
  refine ⟨72100585171322605993074317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48067056780881737328716211 72100585171322605993074317)
  ·
    refine ⟨27037719439245977247402869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72100585171322605993074317 27037719439245977247402869)
    ·
      refine ⟨2534786197429310366944019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27037719439245977247402869 2534786197429310366944019)
      ·
        refine ⟨3802179296143965550416029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2534786197429310366944019 3802179296143965550416029)
        ·
          refine ⟨1425817236053987081406011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3802179296143965550416029 1425817236053987081406011)
          ·
            refine ⟨2138725854080980622109017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425817236053987081406011 2138725854080980622109017)
            ·
              refine ⟨1604044390560735466581763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2138725854080980622109017 1604044390560735466581763)
              ·
                refine ⟨2406066585841103199872645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604044390560735466581763 2406066585841103199872645)
                ·
                  refine ⟨451137484845206849976121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2406066585841103199872645 451137484845206849976121)
                  ·
                    rfl

theorem cell21_1976821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_1976821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976821 prefixEnd_1976821 := by exact prefixLift 1976821
  have htrace : WordTrace (prefixWord ++ tailWord_1976821) baseStart_1976821 baseEnd_1976821 := by
    simpa [prefixWord, tailWord_1976821, baseEnd_1976821] using wordTrace_append hprefix tailTrace_1976821
  have hstable : (prefixWord ++ tailWord_1976821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976821).length < 2 ^ (prefixWord ++ tailWord_1976821).sum := by decide
  have hdescent : baseEnd_1976821 < baseStart_1976821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976829 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 4]
def baseStart_1976829 : Nat := 118140960795 + 1976829 * 2 ^ 59
def prefixEnd_1976829 : Nat := 4983230072969 + 3 ^ 40 * 1976829 * 2
def baseEnd_1976829 : Nat := 451139310554200613842771

theorem tailTrace_1976829 : CollatzResearch.WordTrace tailWord_1976829 prefixEnd_1976829 451139310554200613842771 := by
  unfold tailWord_1976829
  simp only [CollatzResearch.WordTrace]
  refine ⟨72100876955293623359365541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48067251303529082239577027 72100876955293623359365541)
  ·
    refine ⟨13518914429117554379881039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72100876955293623359365541 13518914429117554379881039)
    ·
      refine ⟨20278371643676331569821559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13518914429117554379881039 20278371643676331569821559)
      ·
        refine ⟨30417557465514497354732339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20278371643676331569821559 30417557465514497354732339)
        ·
          refine ⟨45626336198271746032098509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30417557465514497354732339 45626336198271746032098509)
          ·
            refine ⟨17109876074351904762036941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45626336198271746032098509 17109876074351904762036941)
            ·
              refine ⟨6416203527881964285763853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17109876074351904762036941 6416203527881964285763853)
              ·
                refine ⟨2406076322955736607161445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6416203527881964285763853 2406076322955736607161445)
                ·
                  refine ⟨451139310554200613842771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2406076322955736607161445 451139310554200613842771)
                  ·
                    rfl

theorem cell21_1976829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_1976829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976829 prefixEnd_1976829 := by exact prefixLift 1976829
  have htrace : WordTrace (prefixWord ++ tailWord_1976829) baseStart_1976829 baseEnd_1976829 := by
    simpa [prefixWord, tailWord_1976829, baseEnd_1976829] using wordTrace_append hprefix tailTrace_1976829
  have hstable : (prefixWord ++ tailWord_1976829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976829).length < 2 ^ (prefixWord ++ tailWord_1976829).sum := by decide
  have hdescent : baseEnd_1976829 < baseStart_1976829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976843 : List Nat := [1, 1, 1, 1, 7, 1, 2, 7]
def baseStart_1976843 : Nat := 118140960795 + 1976843 * 2 ^ 59
def prefixEnd_1976843 : Nat := 4983230072969 + 3 ^ 40 * 1976843 * 2
def baseEnd_1976843 : Nat := 150380835181646566869803

theorem tailTrace_1976843 : CollatzResearch.WordTrace tailWord_1976843 prefixEnd_1976843 150380835181646566869803 := by
  unfold tailWord_1976843
  simp only [CollatzResearch.WordTrace]
  refine ⟨72101387577242903750375183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48067591718161935833583455 72101387577242903750375183)
  ·
    refine ⟨108152081365864355625562775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72101387577242903750375183 108152081365864355625562775)
    ·
      refine ⟨162228122048796533438344163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108152081365864355625562775 162228122048796533438344163)
      ·
        refine ⟨243342183073194800157516245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162228122048796533438344163 243342183073194800157516245)
        ·
          refine ⟨5703332415778003128691787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 243342183073194800157516245 5703332415778003128691787)
          ·
            refine ⟨8554998623667004693037681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703332415778003128691787 8554998623667004693037681)
            ·
              refine ⟨6416248967750253519778261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8554998623667004693037681 6416248967750253519778261)
              ·
                refine ⟨150380835181646566869803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6416248967750253519778261 150380835181646566869803)
                ·
                  rfl

theorem cell21_1976843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 7].length) (baseStart_1976843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976843 prefixEnd_1976843 := by exact prefixLift 1976843
  have htrace : WordTrace (prefixWord ++ tailWord_1976843) baseStart_1976843 baseEnd_1976843 := by
    simpa [prefixWord, tailWord_1976843, baseEnd_1976843] using wordTrace_append hprefix tailTrace_1976843
  have hstable : (prefixWord ++ tailWord_1976843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976843).length < 2 ^ (prefixWord ++ tailWord_1976843).sum := by decide
  have hdescent : baseEnd_1976843 < baseStart_1976843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976857 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 7]
def baseStart_1976857 : Nat := 118140960795 + 1976857 * 2 ^ 59
def prefixEnd_1976857 : Nat := 4983230072969 + 3 ^ 40 * 1976857 * 2
def baseEnd_1976857 : Nat := 451145700535678787376047

theorem tailTrace_1976857 : CollatzResearch.WordTrace tailWord_1976857 prefixEnd_1976857 451145700535678787376047 := by
  unfold tailWord_1976857
  simp only [CollatzResearch.WordTrace]
  refine ⟨72101898199192184141384825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48067932132794789427589883 72101898199192184141384825)
  ·
    refine ⟨54076423649394138106038619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72101898199192184141384825 54076423649394138106038619)
    ·
      refine ⟨81114635474091207159057929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54076423649394138106038619 81114635474091207159057929)
      ·
        refine ⟨60835976605568405369293447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81114635474091207159057929 60835976605568405369293447)
        ·
          refine ⟨91253964908352608053940171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60835976605568405369293447 91253964908352608053940171)
          ·
            refine ⟨136880947362528912080910257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91253964908352608053940171 136880947362528912080910257)
            ·
              refine ⟨102660710521896684060682693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136880947362528912080910257 102660710521896684060682693)
              ·
                refine ⟨19248883222855628261378005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102660710521896684060682693 19248883222855628261378005)
                ·
                  refine ⟨451145700535678787376047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19248883222855628261378005 451145700535678787376047)
                  ·
                    rfl

theorem cell21_1976857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_1976857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976857 prefixEnd_1976857 := by exact prefixLift 1976857
  have htrace : WordTrace (prefixWord ++ tailWord_1976857) baseStart_1976857 baseEnd_1976857 := by
    simpa [prefixWord, tailWord_1976857, baseEnd_1976857] using wordTrace_append hprefix tailTrace_1976857
  have hstable : (prefixWord ++ tailWord_1976857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976857).length < 2 ^ (prefixWord ++ tailWord_1976857).sum := by decide
  have hdescent : baseEnd_1976857 < baseStart_1976857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976894 : List Nat := [4, 2, 1, 4, 1, 1, 3, 5]
def baseStart_1976894 : Nat := 118140960795 + 1976894 * 2 ^ 59
def prefixEnd_1976894 : Nat := 4983230072969 + 3 ^ 40 * 1976894 * 2
def baseEnd_1976894 : Nat := 150384714813258315086435

theorem tailTrace_1976894 : CollatzResearch.WordTrace tailWord_1976894 prefixEnd_1976894 150384714813258315086435 := by
  unfold tailWord_1976894
  simp only [CollatzResearch.WordTrace]
  refine ⟨9012905962507267432560217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48068831800038759640321157 9012905962507267432560217)
  ·
    refine ⟨6759679471880450574420163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9012905962507267432560217 6759679471880450574420163)
    ·
      refine ⟨10139519207820675861630245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6759679471880450574420163 10139519207820675861630245)
      ·
        refine ⟨1901159851466376724055671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10139519207820675861630245 1901159851466376724055671)
        ·
          refine ⟨2851739777199565086083507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901159851466376724055671 2851739777199565086083507)
          ·
            refine ⟨4277609665799347629125261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851739777199565086083507 4277609665799347629125261)
            ·
              refine ⟨1604103624674755360921973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4277609665799347629125261 1604103624674755360921973)
              ·
                refine ⟨150384714813258315086435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1604103624674755360921973 150384714813258315086435)
                ·
                  rfl

theorem cell21_1976894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_1976894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976894 prefixEnd_1976894 := by exact prefixLift 1976894
  have htrace : WordTrace (prefixWord ++ tailWord_1976894) baseStart_1976894 baseEnd_1976894 := by
    simpa [prefixWord, tailWord_1976894, baseEnd_1976894] using wordTrace_append hprefix tailTrace_1976894
  have hstable : (prefixWord ++ tailWord_1976894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976894).length < 2 ^ (prefixWord ++ tailWord_1976894).sum := by decide
  have hdescent : baseEnd_1976894 < baseStart_1976894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976984 : List Nat := [2, 1, 2, 4, 1, 1, 5, 2, 3]
def baseStart_1976984 : Nat := 118140960795 + 1976984 * 2 ^ 59
def prefixEnd_1976984 : Nat := 4983230072969 + 3 ^ 40 * 1976984 * 2
def baseEnd_1976984 : Nat := 451174683665954788759121

theorem tailTrace_1976984 : CollatzResearch.WordTrace tailWord_1976984 prefixEnd_1976984 451174683665954788759121 := by
  unfold tailWord_1976984
  simp only [CollatzResearch.WordTrace]
  refine ⟨36053265134866042415629003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48071020179821389887505337 36053265134866042415629003)
  ·
    refine ⟨54079897702299063623443505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36053265134866042415629003 54079897702299063623443505)
    ·
      refine ⟨40559923276724297717582629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54079897702299063623443505 40559923276724297717582629)
      ·
        refine ⟨7604985614385805822046743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40559923276724297717582629 7604985614385805822046743)
        ·
          refine ⟨11407478421578708733070115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7604985614385805822046743 11407478421578708733070115)
          ·
            refine ⟨17111217632368063099605173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11407478421578708733070115 17111217632368063099605173)
            ·
              refine ⟨1604176653034505915587985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17111217632368063099605173 1604176653034505915587985)
              ·
                refine ⟨1203132489775879436690989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1604176653034505915587985 1203132489775879436690989)
                ·
                  refine ⟨451174683665954788759121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203132489775879436690989 451174683665954788759121)
                  ·
                    rfl

theorem cell21_1976984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 3].length) (baseStart_1976984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1976984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1976984 prefixEnd_1976984 := by exact prefixLift 1976984
  have htrace : WordTrace (prefixWord ++ tailWord_1976984) baseStart_1976984 baseEnd_1976984 := by
    simpa [prefixWord, tailWord_1976984, baseEnd_1976984] using wordTrace_append hprefix tailTrace_1976984
  have hstable : (prefixWord ++ tailWord_1976984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976984).length < 2 ^ (prefixWord ++ tailWord_1976984).sum := by decide
  have hdescent : baseEnd_1976984 < baseStart_1976984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977057 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 4]
def baseStart_1977057 : Nat := 118140960795 + 1977057 * 2 ^ 59
def prefixEnd_1977057 : Nat := 4983230072969 + 3 ^ 40 * 1977057 * 2
def baseEnd_1977057 : Nat := 451191343260522884042305

theorem tailTrace_1977057 : CollatzResearch.WordTrace tailWord_1977057 prefixEnd_1977057 451191343260522884042305 := by
  unfold tailWord_1977057
  simp only [CollatzResearch.WordTrace]
  refine ⟨72109192798467618298665425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48072795198978412199110283 72109192798467618298665425)
  ·
    refine ⟨54081894598850713723999069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72109192798467618298665425 54081894598850713723999069)
    ·
      refine ⟨20280710474569017646499651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54081894598850713723999069 20280710474569017646499651)
      ·
        refine ⟨30421065711853526469749477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20280710474569017646499651 30421065711853526469749477)
        ·
          refine ⟨5703949820972536213078027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30421065711853526469749477 5703949820972536213078027)
          ·
            refine ⟨8555924731458804319617041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703949820972536213078027 8555924731458804319617041)
            ·
              refine ⟨6416943548594103239712781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8555924731458804319617041 6416943548594103239712781)
              ·
                refine ⟨2406353830722788714892293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6416943548594103239712781 2406353830722788714892293)
                ·
                  refine ⟨451191343260522884042305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2406353830722788714892293 451191343260522884042305)
                  ·
                    rfl

theorem cell21_1977057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_1977057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977057 prefixEnd_1977057 := by exact prefixLift 1977057
  have htrace : WordTrace (prefixWord ++ tailWord_1977057) baseStart_1977057 baseEnd_1977057 := by
    simpa [prefixWord, tailWord_1977057, baseEnd_1977057] using wordTrace_append hprefix tailTrace_1977057
  have hstable : (prefixWord ++ tailWord_1977057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977057).length < 2 ^ (prefixWord ++ tailWord_1977057).sum := by decide
  have hdescent : baseEnd_1977057 < baseStart_1977057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977085 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 7]
def baseStart_1977085 : Nat := 118140960795 + 1977085 * 2 ^ 59
def prefixEnd_1977085 : Nat := 4983230072969 + 3 ^ 40 * 1977085 * 2
def baseEnd_1977085 : Nat := 451197733242001057575581

theorem tailTrace_1977085 : CollatzResearch.WordTrace tailWord_1977085 prefixEnd_1977085 451197733242001057575581 := by
  unfold tailWord_1977085
  simp only [CollatzResearch.WordTrace]
  refine ⟨72110214042366179080684709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48073476028244119387123139 72110214042366179080684709)
  ·
    refine ⟨13520665132943658577628383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72110214042366179080684709 13520665132943658577628383)
    ·
      refine ⟨20280997699415487866442575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13520665132943658577628383 20280997699415487866442575)
      ·
        refine ⟨30421496549123231799663863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20280997699415487866442575 30421496549123231799663863)
        ·
          refine ⟨45632244823684847699495795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30421496549123231799663863 45632244823684847699495795)
          ·
            refine ⟨68448367235527271549243693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45632244823684847699495795 68448367235527271549243693)
            ·
              refine ⟨25668137713322726830966385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68448367235527271549243693 25668137713322726830966385)
              ·
                refine ⟨19251103284992045123224789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25668137713322726830966385 19251103284992045123224789)
                ·
                  refine ⟨451197733242001057575581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19251103284992045123224789 451197733242001057575581)
                  ·
                    rfl

theorem cell21_1977085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_1977085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977085 prefixEnd_1977085 := by exact prefixLift 1977085
  have htrace : WordTrace (prefixWord ++ tailWord_1977085) baseStart_1977085 baseEnd_1977085 := by
    simpa [prefixWord, tailWord_1977085, baseEnd_1977085] using wordTrace_append hprefix tailTrace_1977085
  have hstable : (prefixWord ++ tailWord_1977085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977085).length < 2 ^ (prefixWord ++ tailWord_1977085).sum := by decide
  have hdescent : baseEnd_1977085 < baseStart_1977085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977153 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 5]
def baseStart_1977153 : Nat := 118140960795 + 1977153 * 2 ^ 59
def prefixEnd_1977153 : Nat := 4983230072969 + 3 ^ 40 * 1977153 * 2
def baseEnd_1977153 : Nat := 451213251768448050442109

theorem tailTrace_1977153 : CollatzResearch.WordTrace tailWord_1977153 prefixEnd_1977153 451213251768448050442109 := by
  unfold tailWord_1977153
  simp only [CollatzResearch.WordTrace]
  refine ⟨72112694206119826694160113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48075129470746551129440075 72112694206119826694160113)
  ·
    refine ⟨54084520654589870020620085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72112694206119826694160113 54084520654589870020620085)
    ·
      refine ⟨5070423811367800314433133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54084520654589870020620085 5070423811367800314433133)
      ·
        refine ⟨1901408929262925117912425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5070423811367800314433133 1901408929262925117912425)
        ·
          refine ⟨1426056696947193838434319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1901408929262925117912425 1426056696947193838434319)
          ·
            refine ⟨2139085045420790757651479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426056696947193838434319 2139085045420790757651479)
            ·
              refine ⟨3208627568131186136477219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139085045420790757651479 3208627568131186136477219)
              ·
                refine ⟨4812941352196779204715829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208627568131186136477219 4812941352196779204715829)
                ·
                  refine ⟨451213251768448050442109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4812941352196779204715829 451213251768448050442109)
                  ·
                    rfl

theorem cell21_1977153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 5].length) (baseStart_1977153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977153 prefixEnd_1977153 := by exact prefixLift 1977153
  have htrace : WordTrace (prefixWord ++ tailWord_1977153) baseStart_1977153 baseEnd_1977153 := by
    simpa [prefixWord, tailWord_1977153, baseEnd_1977153] using wordTrace_append hprefix tailTrace_1977153
  have hstable : (prefixWord ++ tailWord_1977153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977153).length < 2 ^ (prefixWord ++ tailWord_1977153).sum := by decide
  have hdescent : baseEnd_1977153 < baseStart_1977153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977209 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 4]
def baseStart_1977209 : Nat := 118140960795 + 1977209 * 2 ^ 59
def prefixEnd_1977209 : Nat := 4983230072969 + 3 ^ 40 * 1977209 * 2
def baseEnd_1977209 : Nat := 451226031731404397508661

theorem tailTrace_1977209 : CollatzResearch.WordTrace tailWord_1977209 prefixEnd_1977209 451226031731404397508661 := by
  unfold tailWord_1977209
  simp only [CollatzResearch.WordTrace]
  refine ⟨72114736693916948258198681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48076491129277965505465787 72114736693916948258198681)
  ·
    refine ⟨54086052520437711193649011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72114736693916948258198681 54086052520437711193649011)
    ·
      refine ⟨81129078780656566790473517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54086052520437711193649011 81129078780656566790473517)
      ·
        refine ⟨30423404542746212546427569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81129078780656566790473517 30423404542746212546427569)
        ·
          refine ⟨22817553407059659409820677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30423404542746212546427569 22817553407059659409820677)
          ·
            refine ⟨4278291263823686139341377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22817553407059659409820677 4278291263823686139341377)
            ·
              refine ⟨3208718447867764604506033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4278291263823686139341377 3208718447867764604506033)
              ·
                refine ⟨2406538835900823453379525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208718447867764604506033 2406538835900823453379525)
                ·
                  refine ⟨451226031731404397508661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2406538835900823453379525 451226031731404397508661)
                  ·
                    rfl

theorem cell21_1977209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_1977209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977209 prefixEnd_1977209 := by exact prefixLift 1977209
  have htrace : WordTrace (prefixWord ++ tailWord_1977209) baseStart_1977209 baseEnd_1977209 := by
    simpa [prefixWord, tailWord_1977209, baseEnd_1977209] using wordTrace_append hprefix tailTrace_1977209
  have hstable : (prefixWord ++ tailWord_1977209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977209).length < 2 ^ (prefixWord ++ tailWord_1977209).sum := by decide
  have hdescent : baseEnd_1977209 < baseStart_1977209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977223 : List Nat := [1, 1, 4, 2, 3, 1, 3, 6]
def baseStart_1977223 : Nat := 118140960795 + 1977223 * 2 ^ 59
def prefixEnd_1977223 : Nat := 4983230072969 + 3 ^ 40 * 1977223 * 2
def baseEnd_1977223 : Nat := 150409742240714494758433

theorem tailTrace_1977223 : CollatzResearch.WordTrace tailWord_1977223 prefixEnd_1977223 150409742240714494758433 := by
  unfold tailWord_1977223
  simp only [CollatzResearch.WordTrace]
  refine ⟨72115247315866228649208323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48076831543910819099472215 72115247315866228649208323)
  ·
    refine ⟨108172870973799342973812485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72115247315866228649208323 108172870973799342973812485)
    ·
      refine ⟨20282413307587376807589841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108172870973799342973812485 20282413307587376807589841)
      ·
        refine ⟨15211809980690532605692381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20282413307587376807589841 15211809980690532605692381)
        ·
          refine ⟨5704428742758949727134643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15211809980690532605692381 5704428742758949727134643)
          ·
            refine ⟨8556643114138424590701965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704428742758949727134643 8556643114138424590701965)
            ·
              refine ⟨3208741167801909221513237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8556643114138424590701965 3208741167801909221513237)
              ·
                refine ⟨150409742240714494758433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3208741167801909221513237 150409742240714494758433)
                ·
                  rfl

theorem cell21_1977223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 6].length) (baseStart_1977223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977223 prefixEnd_1977223 := by exact prefixLift 1977223
  have htrace : WordTrace (prefixWord ++ tailWord_1977223) baseStart_1977223 baseEnd_1977223 := by
    simpa [prefixWord, tailWord_1977223, baseEnd_1977223] using wordTrace_append hprefix tailTrace_1977223
  have hstable : (prefixWord ++ tailWord_1977223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977223).length < 2 ^ (prefixWord ++ tailWord_1977223).sum := by decide
  have hdescent : baseEnd_1977223 < baseStart_1977223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977237 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 7]
def baseStart_1977237 : Nat := 118140960795 + 1977237 * 2 ^ 59
def prefixEnd_1977237 : Nat := 4983230072969 + 3 ^ 40 * 1977237 * 2
def baseEnd_1977237 : Nat := 451232421712882571041937

theorem tailTrace_1977237 : CollatzResearch.WordTrace tailWord_1977237 prefixEnd_1977237 451232421712882571041937 := by
  unfold tailWord_1977237
  simp only [CollatzResearch.WordTrace]
  refine ⟨72115757937815509040217965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48077171958543672693478643 72115757937815509040217965)
  ·
    refine ⟨27043409226680815890081737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72115757937815509040217965 27043409226680815890081737)
    ·
      refine ⟨20282556920010611917561303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27043409226680815890081737 20282556920010611917561303)
      ·
        refine ⟨30423835380015917876341955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20282556920010611917561303 30423835380015917876341955)
        ·
          refine ⟨45635753070023876814512933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30423835380015917876341955 45635753070023876814512933)
          ·
            refine ⟨8556703700629476902721175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45635753070023876814512933 8556703700629476902721175)
            ·
              refine ⟨12835055550944215354081763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556703700629476902721175 12835055550944215354081763)
              ·
                refine ⟨19252583326416323031122645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12835055550944215354081763 19252583326416323031122645)
                ·
                  refine ⟨451232421712882571041937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19252583326416323031122645 451232421712882571041937)
                  ·
                    rfl

theorem cell21_1977237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_1977237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977237 prefixEnd_1977237 := by exact prefixLift 1977237
  have htrace : WordTrace (prefixWord ++ tailWord_1977237) baseStart_1977237 baseEnd_1977237 := by
    simpa [prefixWord, tailWord_1977237, baseEnd_1977237] using wordTrace_append hprefix tailTrace_1977237
  have hstable : (prefixWord ++ tailWord_1977237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977237).length < 2 ^ (prefixWord ++ tailWord_1977237).sum := by decide
  have hdescent : baseEnd_1977237 < baseStart_1977237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977333 : List Nat := [1, 3, 5, 2, 1, 1, 2, 6]
def baseStart_1977333 : Nat := 118140960795 + 1977333 * 2 ^ 59
def prefixEnd_1977333 : Nat := 4983230072969 + 3 ^ 40 * 1977333 * 2
def baseEnd_1977333 : Nat := 150418110073602579147247

theorem tailTrace_1977333 : CollatzResearch.WordTrace tailWord_1977333 prefixEnd_1977333 150418110073602579147247 := by
  unfold tailWord_1977333
  simp only [CollatzResearch.WordTrace]
  refine ⟨72119259345467717435712653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48079506230311811623808435 72119259345467717435712653)
  ·
    refine ⟨27044722254550394038392245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72119259345467717435712653 27044722254550394038392245)
    ·
      refine ⟨2535442711364099441099273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27044722254550394038392245 2535442711364099441099273)
      ·
        refine ⟨1901582033523074580824455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2535442711364099441099273 1901582033523074580824455)
        ·
          refine ⟨2852373050284611871236683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901582033523074580824455 2852373050284611871236683)
          ·
            refine ⟨4278559575426917806855025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2852373050284611871236683 4278559575426917806855025)
            ·
              refine ⟨3208919681570188355141269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4278559575426917806855025 3208919681570188355141269)
              ·
                refine ⟨150418110073602579147247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3208919681570188355141269 150418110073602579147247)
                ·
                  rfl

theorem cell21_1977333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 6].length) (baseStart_1977333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977333 prefixEnd_1977333 := by exact prefixLift 1977333
  have htrace : WordTrace (prefixWord ++ tailWord_1977333) baseStart_1977333 baseEnd_1977333 := by
    simpa [prefixWord, tailWord_1977333, baseEnd_1977333] using wordTrace_append hprefix tailTrace_1977333
  have hstable : (prefixWord ++ tailWord_1977333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977333).length < 2 ^ (prefixWord ++ tailWord_1977333).sum := by decide
  have hdescent : baseEnd_1977333 < baseStart_1977333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977406 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1977406 : Nat := 118140960795 + 1977406 * 2 ^ 59
def prefixEnd_1977406 : Nat := 4983230072969 + 3 ^ 40 * 1977406 * 2
def baseEnd_1977406 : Nat := 451270989815375832724925

theorem tailTrace_1977406 : CollatzResearch.WordTrace tailWord_1977406 prefixEnd_1977406 451270989815375832724925 := by
  unfold tailWord_1977406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9015240234275406362890009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48081281249468833935413381 9015240234275406362890009)
  ·
    refine ⟨6761430175706554772167507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9015240234275406362890009 6761430175706554772167507)
    ·
      refine ⟨10142145263559832158251261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6761430175706554772167507 10142145263559832158251261)
      ·
        refine ⟨3803304473834937059344223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10142145263559832158251261 3803304473834937059344223)
        ·
          refine ⟨5704956710752405589016335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3803304473834937059344223 5704956710752405589016335)
          ·
            refine ⟨8557435066128608383524503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704956710752405589016335 8557435066128608383524503)
            ·
              refine ⟨12836152599192912575286755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8557435066128608383524503 12836152599192912575286755)
              ·
                refine ⟨19254228898789368862930133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12836152599192912575286755 19254228898789368862930133)
                ·
                  refine ⟨451270989815375832724925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19254228898789368862930133 451270989815375832724925)
                  ·
                    rfl

theorem cell21_1977406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1977406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977406 prefixEnd_1977406 := by exact prefixLift 1977406
  have htrace : WordTrace (prefixWord ++ tailWord_1977406) baseStart_1977406 baseEnd_1977406 := by
    simpa [prefixWord, tailWord_1977406, baseEnd_1977406] using wordTrace_append hprefix tailTrace_1977406
  have hstable : (prefixWord ++ tailWord_1977406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977406).length < 2 ^ (prefixWord ++ tailWord_1977406).sum := by decide
  have hdescent : baseEnd_1977406 < baseStart_1977406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977454 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_1977454 : Nat := 118140960795 + 1977454 * 2 ^ 59
def prefixEnd_1977454 : Nat := 4983230072969 + 3 ^ 40 * 1977454 * 2
def baseEnd_1977454 : Nat := 451281944069338415924827

theorem tailTrace_1977454 : CollatzResearch.WordTrace tailWord_1977454 prefixEnd_1977454 451281944069338415924827 := by
  unfold tailWord_1977454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9015459072253669387608427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48082448385352903400578277 9015459072253669387608427)
  ·
    refine ⟨13523188608380504081412641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9015459072253669387608427 13523188608380504081412641)
    ·
      refine ⟨10142391456285378061059481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13523188608380504081412641 10142391456285378061059481)
      ·
        refine ⟨7606793592214033545794611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10142391456285378061059481 7606793592214033545794611)
        ·
          refine ⟨11410190388321050318691917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7606793592214033545794611 11410190388321050318691917)
          ·
            refine ⟨4278821395620393869509469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11410190388321050318691917 4278821395620393869509469)
            ·
              refine ⟨1604558023357647701066051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4278821395620393869509469 1604558023357647701066051)
              ·
                refine ⟨2406837035036471551599077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604558023357647701066051 2406837035036471551599077)
                ·
                  refine ⟨451281944069338415924827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2406837035036471551599077 451281944069338415924827)
                  ·
                    rfl

theorem cell21_1977454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_1977454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977454 prefixEnd_1977454 := by exact prefixLift 1977454
  have htrace : WordTrace (prefixWord ++ tailWord_1977454) baseStart_1977454 baseEnd_1977454 := by
    simpa [prefixWord, tailWord_1977454, baseEnd_1977454] using wordTrace_append hprefix tailTrace_1977454
  have hstable : (prefixWord ++ tailWord_1977454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977454).length < 2 ^ (prefixWord ++ tailWord_1977454).sum := by decide
  have hdescent : baseEnd_1977454 < baseStart_1977454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977496 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_1977496 : Nat := 118140960795 + 1977496 * 2 ^ 59
def prefixEnd_1977496 : Nat := 4983230072969 + 3 ^ 40 * 1977496 * 2
def baseEnd_1977496 : Nat := 451291529041555676224741

theorem tailTrace_1977496 : CollatzResearch.WordTrace tailWord_1977496 prefixEnd_1977496 451291529041555676224741 := by
  unfold tailWord_1977496
  simp only [CollatzResearch.WordTrace]
  refine ⟨36062602221938598136948171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48083469629251464182597561 36062602221938598136948171)
  ·
    refine ⟨54093903332907897205422257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36062602221938598136948171 54093903332907897205422257)
    ·
      refine ⟨40570427499680922904066693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54093903332907897205422257 40570427499680922904066693)
      ·
        refine ⟨7606955156190173044512505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40570427499680922904066693 7606955156190173044512505)
        ·
          refine ⟨5705216367142629783384379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7606955156190173044512505 5705216367142629783384379)
          ·
            refine ⟨8557824550713944675076569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5705216367142629783384379 8557824550713944675076569)
            ·
              refine ⟨6418368413035458506307427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8557824550713944675076569 6418368413035458506307427)
              ·
                refine ⟨9627552619553187759461141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418368413035458506307427 9627552619553187759461141)
                ·
                  refine ⟨451291529041555676224741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9627552619553187759461141 451291529041555676224741)
                  ·
                    rfl

theorem cell21_1977496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_1977496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977496 prefixEnd_1977496 := by exact prefixLift 1977496
  have htrace : WordTrace (prefixWord ++ tailWord_1977496) baseStart_1977496 baseEnd_1977496 := by
    simpa [prefixWord, tailWord_1977496, baseEnd_1977496] using wordTrace_append hprefix tailTrace_1977496
  have hstable : (prefixWord ++ tailWord_1977496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977496).length < 2 ^ (prefixWord ++ tailWord_1977496).sum := by decide
  have hdescent : baseEnd_1977496 < baseStart_1977496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977572 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 4]
def baseStart_1977572 : Nat := 118140960795 + 1977572 * 2 ^ 59
def prefixEnd_1977572 : Nat := 4983230072969 + 3 ^ 40 * 1977572 * 2
def baseEnd_1977572 : Nat := 451308873276996432957919

theorem tailTrace_1977572 : CollatzResearch.WordTrace tailWord_1977572 prefixEnd_1977572 451308873276996432957919 := by
  unfold tailWord_1977572
  simp only [CollatzResearch.WordTrace]
  refine ⟨36063988195800930626831485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48085317594401240835775313 36063988195800930626831485)
  ·
    refine ⟨13523995573425348985061807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36063988195800930626831485 13523995573425348985061807)
    ·
      refine ⟨20285993360138023477592711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13523995573425348985061807 20285993360138023477592711)
      ·
        refine ⟨30428990040207035216389067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20285993360138023477592711 30428990040207035216389067)
        ·
          refine ⟨45643485060310552824583601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30428990040207035216389067 45643485060310552824583601)
          ·
            refine ⟨34232613795232914618437701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45643485060310552824583601 34232613795232914618437701)
            ·
              refine ⟨6418615086606171490957069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34232613795232914618437701 6418615086606171490957069)
              ·
                refine ⟨2406980657477314309108901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6418615086606171490957069 2406980657477314309108901)
                ·
                  refine ⟨451308873276996432957919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2406980657477314309108901 451308873276996432957919)
                  ·
                    rfl

theorem cell21_1977572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_1977572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977572 prefixEnd_1977572 := by exact prefixLift 1977572
  have htrace : WordTrace (prefixWord ++ tailWord_1977572) baseStart_1977572 baseEnd_1977572 := by
    simpa [prefixWord, tailWord_1977572, baseEnd_1977572] using wordTrace_append hprefix tailTrace_1977572
  have hstable : (prefixWord ++ tailWord_1977572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977572).length < 2 ^ (prefixWord ++ tailWord_1977572).sum := by decide
  have hdescent : baseEnd_1977572 < baseStart_1977572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977600 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_1977600 : Nat := 118140960795 + 1977600 * 2 ^ 59
def prefixEnd_1977600 : Nat := 4983230072969 + 3 ^ 40 * 1977600 * 2
def baseEnd_1977600 : Nat := 451315263258474606491195

theorem tailTrace_1977600 : CollatzResearch.WordTrace tailWord_1977600 prefixEnd_1977600 451315263258474606491195 := by
  unfold tailWord_1977600
  simp only [CollatzResearch.WordTrace]
  refine ⟨36064498817750211017841127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48085998423666948023788169 36064498817750211017841127)
  ·
    refine ⟨54096748226625316526761691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36064498817750211017841127 54096748226625316526761691)
    ·
      refine ⟨81145122339937974790142537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54096748226625316526761691 81145122339937974790142537)
      ·
        refine ⟨60858841754953481092606903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81145122339937974790142537 60858841754953481092606903)
        ·
          refine ⟨91288262632430221638910355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60858841754953481092606903 91288262632430221638910355)
          ·
            refine ⟨136932393948645332458365533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91288262632430221638910355 136932393948645332458365533)
            ·
              refine ⟨51349647730741999671887075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136932393948645332458365533 51349647730741999671887075)
              ·
                refine ⟨77024471596112999507830613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51349647730741999671887075 77024471596112999507830613)
                ·
                  refine ⟨451315263258474606491195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77024471596112999507830613 451315263258474606491195)
                  ·
                    rfl

theorem cell21_1977600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_1977600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977600 prefixEnd_1977600 := by exact prefixLift 1977600
  have htrace : WordTrace (prefixWord ++ tailWord_1977600) baseStart_1977600 baseEnd_1977600 := by
    simpa [prefixWord, tailWord_1977600, baseEnd_1977600] using wordTrace_append hprefix tailTrace_1977600
  have hstable : (prefixWord ++ tailWord_1977600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977600).length < 2 ^ (prefixWord ++ tailWord_1977600).sum := by decide
  have hdescent : baseEnd_1977600 < baseStart_1977600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977617 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 5]
def baseStart_1977617 : Nat := 118140960795 + 1977617 * 2 ^ 59
def prefixEnd_1977617 : Nat := 4983230072969 + 3 ^ 40 * 1977617 * 2
def baseEnd_1977617 : Nat := 451319142890086354707827

theorem tailTrace_1977617 : CollatzResearch.WordTrace tailWord_1977617 prefixEnd_1977617 451319142890086354707827 := by
  unfold tailWord_1977617
  simp only [CollatzResearch.WordTrace]
  refine ⟨72129617676438833939051105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48086411784292555959367403 72129617676438833939051105)
  ·
    refine ⟨54097213257329125454288329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72129617676438833939051105 54097213257329125454288329)
    ·
      refine ⟨40572909942996844090716247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54097213257329125454288329 40572909942996844090716247)
      ·
        refine ⟨60859364914495266136074371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40572909942996844090716247 60859364914495266136074371)
        ·
          refine ⟨91289047371742899204111557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60859364914495266136074371 91289047371742899204111557)
          ·
            refine ⟨17116696382201793600770917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91289047371742899204111557 17116696382201793600770917)
            ·
              refine ⟨3209380571662836300144547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17116696382201793600770917 3209380571662836300144547)
              ·
                refine ⟨4814070857494254450216821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3209380571662836300144547 4814070857494254450216821)
                ·
                  refine ⟨451319142890086354707827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4814070857494254450216821 451319142890086354707827)
                  ·
                    rfl

theorem cell21_1977617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_1977617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977617 prefixEnd_1977617 := by exact prefixLift 1977617
  have htrace : WordTrace (prefixWord ++ tailWord_1977617) baseStart_1977617 baseEnd_1977617 := by
    simpa [prefixWord, tailWord_1977617, baseEnd_1977617] using wordTrace_append hprefix tailTrace_1977617
  have hstable : (prefixWord ++ tailWord_1977617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977617).length < 2 ^ (prefixWord ++ tailWord_1977617).sum := by decide
  have hdescent : baseEnd_1977617 < baseStart_1977617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977651 : List Nat := [1, 1, 1, 2, 5, 4, 1, 3, 3]
def baseStart_1977651 : Nat := 118140960795 + 1977651 * 2 ^ 59
def prefixEnd_1977651 : Nat := 4983230072969 + 3 ^ 40 * 1977651 * 2
def baseEnd_1977651 : Nat := 451326902153309851141091

theorem tailTrace_1977651 : CollatzResearch.WordTrace tailWord_1977651 prefixEnd_1977651 451326902153309851141091 := by
  unfold tailWord_1977651
  simp only [CollatzResearch.WordTrace]
  refine ⟨72130857758315657745788807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48087238505543771830525871 72130857758315657745788807)
  ·
    refine ⟨108196286637473486618683211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72130857758315657745788807 108196286637473486618683211)
    ·
      refine ⟨162294429956210229928024817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108196286637473486618683211 162294429956210229928024817)
      ·
        refine ⟨121720822467157672446018613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162294429956210229928024817 121720822467157672446018613)
        ·
          refine ⟨11411327106296031791814245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121720822467157672446018613 11411327106296031791814245)
          ·
            refine ⟨2139623832430505960965171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11411327106296031791814245 2139623832430505960965171)
            ·
              refine ⟨3209435748645758941447757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139623832430505960965171 3209435748645758941447757)
              ·
                refine ⟨1203538405742159603042909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3209435748645758941447757 1203538405742159603042909)
                ·
                  refine ⟨451326902153309851141091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203538405742159603042909 451326902153309851141091)
                  ·
                    rfl

theorem cell21_1977651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 3].length) (baseStart_1977651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977651 prefixEnd_1977651 := by exact prefixLift 1977651
  have htrace : WordTrace (prefixWord ++ tailWord_1977651) baseStart_1977651 baseEnd_1977651 := by
    simpa [prefixWord, tailWord_1977651, baseEnd_1977651] using wordTrace_append hprefix tailTrace_1977651
  have hstable : (prefixWord ++ tailWord_1977651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977651).length < 2 ^ (prefixWord ++ tailWord_1977651).sum := by decide
  have hdescent : baseEnd_1977651 < baseStart_1977651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977724 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 4]
def baseStart_1977724 : Nat := 118140960795 + 1977724 * 2 ^ 59
def prefixEnd_1977724 : Nat := 4983230072969 + 3 ^ 40 * 1977724 * 2
def baseEnd_1977724 : Nat := 451343561747877946424275

theorem tailTrace_1977724 : CollatzResearch.WordTrace tailWord_1977724 prefixEnd_1977724 451343561747877946424275 := by
  unfold tailWord_1977724
  simp only [CollatzResearch.WordTrace]
  refine ⟨36066760143525595606598113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48089013524700794142130817 36066760143525595606598113)
  ·
    refine ⟨27050070107644196704948585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36066760143525595606598113 27050070107644196704948585)
    ·
      refine ⟨20287552580733147528711439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27050070107644196704948585 20287552580733147528711439)
      ·
        refine ⟨30431328871099721293067159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20287552580733147528711439 30431328871099721293067159)
        ·
          refine ⟨45646993306649581939600739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30431328871099721293067159 45646993306649581939600739)
          ·
            refine ⟨68470489959974372909401109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45646993306649581939600739 68470489959974372909401109)
            ·
              refine ⟨3209554216873798730128177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68470489959974372909401109 3209554216873798730128177)
              ·
                refine ⟨2407165662655349047596133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3209554216873798730128177 2407165662655349047596133)
                ·
                  refine ⟨451343561747877946424275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2407165662655349047596133 451343561747877946424275)
                  ·
                    rfl

theorem cell21_1977724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_1977724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977724 prefixEnd_1977724 := by exact prefixLift 1977724
  have htrace : WordTrace (prefixWord ++ tailWord_1977724) baseStart_1977724 baseEnd_1977724 := by
    simpa [prefixWord, tailWord_1977724, baseEnd_1977724] using wordTrace_append hprefix tailTrace_1977724
  have hstable : (prefixWord ++ tailWord_1977724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977724).length < 2 ^ (prefixWord ++ tailWord_1977724).sum := by decide
  have hdescent : baseEnd_1977724 < baseStart_1977724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977783 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 6]
def baseStart_1977783 : Nat := 118140960795 + 1977783 * 2 ^ 59
def prefixEnd_1977783 : Nat := 4983230072969 + 3 ^ 40 * 1977783 * 2
def baseEnd_1977783 : Nat := 451357026351706954940821

theorem tailTrace_1977783 : CollatzResearch.WordTrace tailWord_1977783 prefixEnd_1977783 451357026351706954940821 := by
  unfold tailWord_1977783
  simp only [CollatzResearch.WordTrace]
  refine ⟨72135672193837444289594003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48090448129224962859729335 72135672193837444289594003)
  ·
    refine ⟨108203508290756166434391005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72135672193837444289594003 108203508290756166434391005)
    ·
      refine ⟨40576315609033562412896627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108203508290756166434391005 40576315609033562412896627)
      ·
        refine ⟨60864473413550343619344941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40576315609033562412896627 60864473413550343619344941)
        ·
          refine ⟨22824177530081378857254353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60864473413550343619344941 22824177530081378857254353)
          ·
            refine ⟨17118133147561034142940765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22824177530081378857254353 17118133147561034142940765)
            ·
              refine ⟨6419299930335387803602787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17118133147561034142940765 6419299930335387803602787)
              ·
                refine ⟨9628949895503081705404181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419299930335387803602787 9628949895503081705404181)
                ·
                  refine ⟨451357026351706954940821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9628949895503081705404181 451357026351706954940821)
                  ·
                    rfl

theorem cell21_1977783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_1977783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977783 prefixEnd_1977783 := by exact prefixLift 1977783
  have htrace : WordTrace (prefixWord ++ tailWord_1977783) baseStart_1977783 baseEnd_1977783 := by
    simpa [prefixWord, tailWord_1977783, baseEnd_1977783] using wordTrace_append hprefix tailTrace_1977783
  have hstable : (prefixWord ++ tailWord_1977783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977783).length < 2 ^ (prefixWord ++ tailWord_1977783).sum := by decide
  have hdescent : baseEnd_1977783 < baseStart_1977783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977828 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_1977828 : Nat := 118140960795 + 1977828 * 2 ^ 59
def prefixEnd_1977828 : Nat := 4983230072969 + 3 ^ 40 * 1977828 * 2
def baseEnd_1977828 : Nat := 451367295964796876690729

theorem tailTrace_1977828 : CollatzResearch.WordTrace tailWord_1977828 prefixEnd_1977828 451367295964796876690729 := by
  unfold tailWord_1977828
  simp only [CollatzResearch.WordTrace]
  refine ⟨36068656739337208487491069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48091542319116277983321425 36068656739337208487491069)
  ·
    refine ⟨13525746277251453182809151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36068656739337208487491069 13525746277251453182809151)
    ·
      refine ⟨20288619415877179774213727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13525746277251453182809151 20288619415877179774213727)
      ·
        refine ⟨30432929123815769661320591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20288619415877179774213727 30432929123815769661320591)
        ·
          refine ⟨45649393685723654491980887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30432929123815769661320591 45649393685723654491980887)
          ·
            refine ⟨68474090528585481737971331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45649393685723654491980887 68474090528585481737971331)
            ·
              refine ⟨102711135792878222606956997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68474090528585481737971331 102711135792878222606956997)
              ·
                refine ⟨19258337961164666738804437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102711135792878222606956997 19258337961164666738804437)
                ·
                  refine ⟨451367295964796876690729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19258337961164666738804437 451367295964796876690729)
                  ·
                    rfl

theorem cell21_1977828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_1977828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977828 prefixEnd_1977828 := by exact prefixLift 1977828
  have htrace : WordTrace (prefixWord ++ tailWord_1977828) baseStart_1977828 baseEnd_1977828 := by
    simpa [prefixWord, tailWord_1977828, baseEnd_1977828] using wordTrace_append hprefix tailTrace_1977828
  have hstable : (prefixWord ++ tailWord_1977828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977828).length < 2 ^ (prefixWord ++ tailWord_1977828).sum := by decide
  have hdescent : baseEnd_1977828 < baseStart_1977828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977873 : List Nat := [1, 2, 2, 1, 1, 2, 3, 9]
def baseStart_1977873 : Nat := 118140960795 + 1977873 * 2 ^ 59
def prefixEnd_1977873 : Nat := 4983230072969 + 3 ^ 40 * 1977873 * 2
def baseEnd_1977873 : Nat := 150459188525962266146879

theorem tailTrace_1977873 : CollatzResearch.WordTrace tailWord_1977873 prefixEnd_1977873 150459188525962266146879 := by
  unfold tailWord_1977873
  simp only [CollatzResearch.WordTrace]
  refine ⟨72138954763511389660370273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48092636509007593106913515 72138954763511389660370273)
  ·
    refine ⟨54104216072633542245277705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72138954763511389660370273 54104216072633542245277705)
    ·
      refine ⟨40578162054475156683958279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54104216072633542245277705 40578162054475156683958279)
      ·
        refine ⟨60867243081712735025937419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40578162054475156683958279 60867243081712735025937419)
        ·
          refine ⟨91300864622569102538906129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60867243081712735025937419 91300864622569102538906129)
          ·
            refine ⟨68475648466926826904179597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91300864622569102538906129 68475648466926826904179597)
            ·
              refine ⟨25678368175097560089067349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68475648466926826904179597 25678368175097560089067349)
              ·
                refine ⟨150459188525962266146879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25678368175097560089067349 150459188525962266146879)
                ·
                  rfl

theorem cell21_1977873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 9].length) (baseStart_1977873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977873 prefixEnd_1977873 := by exact prefixLift 1977873
  have htrace : WordTrace (prefixWord ++ tailWord_1977873) baseStart_1977873 baseEnd_1977873 := by
    simpa [prefixWord, tailWord_1977873, baseEnd_1977873] using wordTrace_append hprefix tailTrace_1977873
  have hstable : (prefixWord ++ tailWord_1977873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977873).length < 2 ^ (prefixWord ++ tailWord_1977873).sum := by decide
  have hdescent : baseEnd_1977873 < baseStart_1977873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977904 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_1977904 : Nat := 118140960795 + 1977904 * 2 ^ 59
def prefixEnd_1977904 : Nat := 4983230072969 + 3 ^ 40 * 1977904 * 2
def baseEnd_1977904 : Nat := 451384640200237633423907

theorem tailTrace_1977904 : CollatzResearch.WordTrace tailWord_1977904 prefixEnd_1977904 451384640200237633423907 := by
  unfold tailWord_1977904
  simp only [CollatzResearch.WordTrace]
  refine ⟨36070042713199540977374383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48093390284266054636499177 36070042713199540977374383)
  ·
    refine ⟨54105064069799311466061575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36070042713199540977374383 54105064069799311466061575)
    ·
      refine ⟨81157596104698967199092363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54105064069799311466061575 81157596104698967199092363)
      ·
        refine ⟨121736394157048450798638545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81157596104698967199092363 121736394157048450798638545)
        ·
          refine ⟨91302295617786338098978909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121736394157048450798638545 91302295617786338098978909)
          ·
            refine ⟨34238360856669876787117091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91302295617786338098978909 34238360856669876787117091)
            ·
              refine ⟨51357541285004815180675637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34238360856669876787117091 51357541285004815180675637)
              ·
                refine ⟨4814769495469201423188341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51357541285004815180675637 4814769495469201423188341)
                ·
                  refine ⟨451384640200237633423907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4814769495469201423188341 451384640200237633423907)
                  ·
                    rfl

theorem cell21_1977904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_1977904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977904 prefixEnd_1977904 := by exact prefixLift 1977904
  have htrace : WordTrace (prefixWord ++ tailWord_1977904) baseStart_1977904 baseEnd_1977904 := by
    simpa [prefixWord, tailWord_1977904, baseEnd_1977904] using wordTrace_append hprefix tailTrace_1977904
  have hstable : (prefixWord ++ tailWord_1977904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977904).length < 2 ^ (prefixWord ++ tailWord_1977904).sum := by decide
  have hdescent : baseEnd_1977904 < baseStart_1977904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977921 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 5]
def baseStart_1977921 : Nat := 118140960795 + 1977921 * 2 ^ 59
def prefixEnd_1977921 : Nat := 4983230072969 + 3 ^ 40 * 1977921 * 2
def baseEnd_1977921 : Nat := 451388519831849381640539

theorem tailTrace_1977921 : CollatzResearch.WordTrace tailWord_1977921 prefixEnd_1977921 451388519831849381640539 := by
  unfold tailWord_1977921
  simp only [CollatzResearch.WordTrace]
  refine ⟨72140705467337493858117617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48093803644891662572078411 72140705467337493858117617)
  ·
    refine ⟨54105529100503120393588213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72140705467337493858117617 54105529100503120393588213)
    ·
      refine ⟨5072393353172167536898895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54105529100503120393588213 5072393353172167536898895)
      ·
        refine ⟨7608590029758251305348343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072393353172167536898895 7608590029758251305348343)
        ·
          refine ⟨11412885044637376958022515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7608590029758251305348343 11412885044637376958022515)
          ·
            refine ⟨17119327566956065437033773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11412885044637376958022515 17119327566956065437033773)
            ·
              refine ⟨6419747837608524538887665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17119327566956065437033773 6419747837608524538887665)
              ·
                refine ⟨4814810878206393404165749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6419747837608524538887665 4814810878206393404165749)
                ·
                  refine ⟨451388519831849381640539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4814810878206393404165749 451388519831849381640539)
                  ·
                    rfl

theorem cell21_1977921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_1977921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977921 prefixEnd_1977921 := by exact prefixLift 1977921
  have htrace : WordTrace (prefixWord ++ tailWord_1977921) baseStart_1977921 baseEnd_1977921 := by
    simpa [prefixWord, tailWord_1977921, baseEnd_1977921] using wordTrace_append hprefix tailTrace_1977921
  have hstable : (prefixWord ++ tailWord_1977921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977921).length < 2 ^ (prefixWord ++ tailWord_1977921).sum := by decide
  have hdescent : baseEnd_1977921 < baseStart_1977921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977938 : List Nat := [3, 2, 2, 1, 2, 2, 1, 5, 3]
def baseStart_1977938 : Nat := 118140960795 + 1977938 * 2 ^ 59
def prefixEnd_1977938 : Nat := 4983230072969 + 3 ^ 40 * 1977938 * 2
def baseEnd_1977938 : Nat := 451392399463461129857171

theorem tailTrace_1977938 : CollatzResearch.WordTrace tailWord_1977938 prefixEnd_1977938 451392399463461129857171 := by
  unfold tailWord_1977938
  simp only [CollatzResearch.WordTrace]
  refine ⟨18035331377068976440371617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48094217005517270507657645 18035331377068976440371617)
  ·
    refine ⟨13526498532801732330278713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18035331377068976440371617 13526498532801732330278713)
    ·
      refine ⟨10144873899601299247709035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13526498532801732330278713 10144873899601299247709035)
      ·
        refine ⟨15217310849401948871563553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10144873899601299247709035 15217310849401948871563553)
        ·
          refine ⟨11412983137051461653672665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15217310849401948871563553 11412983137051461653672665)
          ·
            refine ⟨8559737352788596240254499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11412983137051461653672665 8559737352788596240254499)
            ·
              refine ⟨12839606029182894360381749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8559737352788596240254499 12839606029182894360381749)
              ·
                refine ⟨1203713065235896346285789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12839606029182894360381749 1203713065235896346285789)
                ·
                  refine ⟨451392399463461129857171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203713065235896346285789 451392399463461129857171)
                  ·
                    rfl

theorem cell21_1977938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_1977938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977938 prefixEnd_1977938 := by exact prefixLift 1977938
  have htrace : WordTrace (prefixWord ++ tailWord_1977938) baseStart_1977938 baseEnd_1977938 := by
    simpa [prefixWord, tailWord_1977938, baseEnd_1977938] using wordTrace_append hprefix tailTrace_1977938
  have hstable : (prefixWord ++ tailWord_1977938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977938).length < 2 ^ (prefixWord ++ tailWord_1977938).sum := by decide
  have hdescent : baseEnd_1977938 < baseStart_1977938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978014 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1978014 : Nat := 118140960795 + 1978014 * 2 ^ 59
def prefixEnd_1978014 : Nat := 4983230072969 + 3 ^ 40 * 1978014 * 2
def baseEnd_1978014 : Nat := 451409743698901886590349

theorem tailTrace_1978014 : CollatzResearch.WordTrace tailWord_1978014 prefixEnd_1978014 451409743698901886590349 := by
  unfold tailWord_1978014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9018012182000071342656637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48096064970667047160835397 9018012182000071342656637)
  ·
    refine ⟨3381754568250026753496239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9018012182000071342656637 3381754568250026753496239)
    ·
      refine ⟨5072631852375040130244359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3381754568250026753496239 5072631852375040130244359)
      ·
        refine ⟨7608947778562560195366539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072631852375040130244359 7608947778562560195366539)
        ·
          refine ⟨11413421667843840293049809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7608947778562560195366539 11413421667843840293049809)
          ·
            refine ⟨8560066250882880219787357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11413421667843840293049809 8560066250882880219787357)
            ·
              refine ⟨3210024844081080082420259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8560066250882880219787357 3210024844081080082420259)
              ·
                refine ⟨4815037266121620123630389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210024844081080082420259 4815037266121620123630389)
                ·
                  refine ⟨451409743698901886590349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4815037266121620123630389 451409743698901886590349)
                  ·
                    rfl

theorem cell21_1978014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1978014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978014 prefixEnd_1978014 := by exact prefixLift 1978014
  have htrace : WordTrace (prefixWord ++ tailWord_1978014) baseStart_1978014 baseEnd_1978014 := by
    simpa [prefixWord, tailWord_1978014, baseEnd_1978014] using wordTrace_append hprefix tailTrace_1978014
  have hstable : (prefixWord ++ tailWord_1978014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978014).length < 2 ^ (prefixWord ++ tailWord_1978014).sum := by decide
  have hdescent : baseEnd_1978014 < baseStart_1978014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978076 : List Nat := [2, 2, 5, 1, 2, 2, 1, 6]
def baseStart_1978076 : Nat := 118140960795 + 1978076 * 2 ^ 59
def prefixEnd_1978076 : Nat := 4983230072969 + 3 ^ 40 * 1978076 * 2
def baseEnd_1978076 : Nat := 150474630981201185518963

theorem tailTrace_1978076 : CollatzResearch.WordTrace tailWord_1978076 prefixEnd_1978076 150474630981201185518963 := by
  unfold tailWord_1978076
  simp only [CollatzResearch.WordTrace]
  refine ⟨36073179390887977665005041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48097572521183970220006721 36073179390887977665005041)
  ·
    refine ⟨27054884543165983248753781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36073179390887977665005041 27054884543165983248753781)
    ·
      refine ⟨2536395425921810929570667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27054884543165983248753781 2536395425921810929570667)
      ·
        refine ⟨3804593138882716394356001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2536395425921810929570667 3804593138882716394356001)
        ·
          refine ⟨2853444854162037295767001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3804593138882716394356001 2853444854162037295767001)
          ·
            refine ⟨2140083640621527971825251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2853444854162037295767001 2140083640621527971825251)
            ·
              refine ⟨3210125460932291957737877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140083640621527971825251 3210125460932291957737877)
              ·
                refine ⟨150474630981201185518963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3210125460932291957737877 150474630981201185518963)
                ·
                  rfl

theorem cell21_1978076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_1978076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978076 prefixEnd_1978076 := by exact prefixLift 1978076
  have htrace : WordTrace (prefixWord ++ tailWord_1978076) baseStart_1978076 baseEnd_1978076 := by
    simpa [prefixWord, tailWord_1978076, baseEnd_1978076] using wordTrace_append hprefix tailTrace_1978076
  have hstable : (prefixWord ++ tailWord_1978076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978076).length < 2 ^ (prefixWord ++ tailWord_1978076).sum := by decide
  have hdescent : baseEnd_1978076 < baseStart_1978076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978194 : List Nat := [3, 2, 2, 1, 1, 4, 2, 6]
def baseStart_1978194 : Nat := 118140960795 + 1978194 * 2 ^ 59
def prefixEnd_1978194 : Nat := 4983230072969 + 3 ^ 40 * 1978194 * 2
def baseEnd_1978194 : Nat := 150483607383753857863327

theorem tailTrace_1978194 : CollatzResearch.WordTrace tailWord_1978194 prefixEnd_1978194 150483607383753857863327 := by
  unfold tailWord_1978194
  simp only [CollatzResearch.WordTrace]
  refine ⟨18037665648837115370701409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48100441730232307655203757 18037665648837115370701409)
  ·
    refine ⟨13528249236627836528026057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18037665648837115370701409 13528249236627836528026057)
    ·
      refine ⟨10146186927470877396019543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13528249236627836528026057 10146186927470877396019543)
      ·
        refine ⟨15219280391206316094029315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10146186927470877396019543 15219280391206316094029315)
        ·
          refine ⟨22828920586809474141043973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15219280391206316094029315 22828920586809474141043973)
          ·
            refine ⟨4280422610026776401445745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22828920586809474141043973 4280422610026776401445745)
            ·
              refine ⟨3210316957520082301084309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4280422610026776401445745 3210316957520082301084309)
              ·
                refine ⟨150483607383753857863327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3210316957520082301084309 150483607383753857863327)
                ·
                  rfl

theorem cell21_1978194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_1978194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978194 prefixEnd_1978194 := by exact prefixLift 1978194
  have htrace : WordTrace (prefixWord ++ tailWord_1978194) baseStart_1978194 baseEnd_1978194 := by
    simpa [prefixWord, tailWord_1978194, baseEnd_1978194] using wordTrace_append hprefix tailTrace_1978194
  have hstable : (prefixWord ++ tailWord_1978194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978194).length < 2 ^ (prefixWord ++ tailWord_1978194).sum := by decide
  have hdescent : baseEnd_1978194 < baseStart_1978194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978197 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 4]
def baseStart_1978197 : Nat := 118140960795 + 1978197 * 2 ^ 59
def prefixEnd_1978197 : Nat := 4983230072969 + 3 ^ 40 * 1978197 * 2
def baseEnd_1978197 : Nat := 451451506792134235039975

theorem tailTrace_1978197 : CollatzResearch.WordTrace tailWord_1978197 prefixEnd_1978197 451451506792134235039975 := by
  unfold tailWord_1978197
  simp only [CollatzResearch.WordTrace]
  refine ⟨72150772014337592995164845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48100514676225061996776563 72150772014337592995164845)
  ·
    refine ⟨27056539505376597373186817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72150772014337592995164845 27056539505376597373186817)
    ·
      refine ⟨20292404629032448029890113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27056539505376597373186817 20292404629032448029890113)
      ·
        refine ⟨15219303471774336022417585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20292404629032448029890113 15219303471774336022417585)
        ·
          refine ⟨11414477603830752016813189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15219303471774336022417585 11414477603830752016813189)
          ·
            refine ⟨2140214550718266003152473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11414477603830752016813189 2140214550718266003152473)
            ·
              refine ⟨1605160913038699502364355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2140214550718266003152473 1605160913038699502364355)
              ·
                refine ⟨2407741369558049253546533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605160913038699502364355 2407741369558049253546533)
                ·
                  refine ⟨451451506792134235039975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2407741369558049253546533 451451506792134235039975)
                  ·
                    rfl

theorem cell21_1978197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_1978197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978197 prefixEnd_1978197 := by exact prefixLift 1978197
  have htrace : WordTrace (prefixWord ++ tailWord_1978197) baseStart_1978197 baseEnd_1978197 := by
    simpa [prefixWord, tailWord_1978197, baseEnd_1978197] using wordTrace_append hprefix tailTrace_1978197
  have hstable : (prefixWord ++ tailWord_1978197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978197).length < 2 ^ (prefixWord ++ tailWord_1978197).sum := by decide
  have hdescent : baseEnd_1978197 < baseStart_1978197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978225 : List Nat := [1, 2, 2, 2, 1, 3, 2, 5, 3]
def baseStart_1978225 : Nat := 118140960795 + 1978225 * 2 ^ 59
def prefixEnd_1978225 : Nat := 4983230072969 + 3 ^ 40 * 1978225 * 2
def baseEnd_1978225 : Nat := 451457896773612408573251

theorem tailTrace_1978225 : CollatzResearch.WordTrace tailWord_1978225 prefixEnd_1978225 451457896773612408573251 := by
  unfold tailWord_1978225
  simp only [CollatzResearch.WordTrace]
  refine ⟨72151793258236153777184129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48101195505490769184789419 72151793258236153777184129)
  ·
    refine ⟨54113844943677115332888097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72151793258236153777184129 54113844943677115332888097)
    ·
      refine ⟨40585383707757836499666073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54113844943677115332888097 40585383707757836499666073)
      ·
        refine ⟨30439037780818377374749555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40585383707757836499666073 30439037780818377374749555)
        ·
          refine ⟨45658556671227566062124333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30439037780818377374749555 45658556671227566062124333)
          ·
            refine ⟨17121958751710337273296625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45658556671227566062124333 17121958751710337273296625)
            ·
              refine ⟨12841469063782752954972469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17121958751710337273296625 12841469063782752954972469)
              ·
                refine ⟨1203887724729633089528669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12841469063782752954972469 1203887724729633089528669)
                ·
                  refine ⟨451457896773612408573251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203887724729633089528669 451457896773612408573251)
                  ·
                    rfl

theorem cell21_1978225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 3].length) (baseStart_1978225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978225 prefixEnd_1978225 := by exact prefixLift 1978225
  have htrace : WordTrace (prefixWord ++ tailWord_1978225) baseStart_1978225 baseEnd_1978225 := by
    simpa [prefixWord, tailWord_1978225, baseEnd_1978225] using wordTrace_append hprefix tailTrace_1978225
  have hstable : (prefixWord ++ tailWord_1978225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978225).length < 2 ^ (prefixWord ++ tailWord_1978225).sum := by decide
  have hdescent : baseEnd_1978225 < baseStart_1978225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978301 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1978301 : Nat := 118140960795 + 1978301 * 2 ^ 59
def prefixEnd_1978301 : Nat := 4983230072969 + 3 ^ 40 * 1978301 * 2
def baseEnd_1978301 : Nat := 451475241009053165306429

theorem tailTrace_1978301 : CollatzResearch.WordTrace tailWord_1978301 prefixEnd_1978301 451475241009053165306429 := by
  unfold tailWord_1978301
  simp only [CollatzResearch.WordTrace]
  refine ⟨72154565205960818756950757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48103043470640545837967171 72154565205960818756950757)
  ·
    refine ⟨13528980976117653516928267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72154565205960818756950757 13528980976117653516928267)
    ·
      refine ⟨20293471464176480275392401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13528980976117653516928267 20293471464176480275392401)
      ·
        refine ⟨15220103598132360206544301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20293471464176480275392401 15220103598132360206544301)
        ·
          refine ⟨5707538849299635077454113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15220103598132360206544301 5707538849299635077454113)
          ·
            refine ⟨4280654136974726308090585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5707538849299635077454113 4280654136974726308090585)
            ·
              refine ⟨3210490602731044731067939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4280654136974726308090585 3210490602731044731067939)
              ·
                refine ⟨4815735904096567096601909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210490602731044731067939 4815735904096567096601909)
                ·
                  refine ⟨451475241009053165306429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4815735904096567096601909 451475241009053165306429)
                  ·
                    rfl

theorem cell21_1978301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1978301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978301 prefixEnd_1978301 := by exact prefixLift 1978301
  have htrace : WordTrace (prefixWord ++ tailWord_1978301) baseStart_1978301 baseEnd_1978301 := by
    simpa [prefixWord, tailWord_1978301, baseEnd_1978301] using wordTrace_append hprefix tailTrace_1978301
  have hstable : (prefixWord ++ tailWord_1978301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978301).length < 2 ^ (prefixWord ++ tailWord_1978301).sum := by decide
  have hdescent : baseEnd_1978301 < baseStart_1978301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978360 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 5]
def baseStart_1978360 : Nat := 118140960795 + 1978360 * 2 ^ 59
def prefixEnd_1978360 : Nat := 4983230072969 + 3 ^ 40 * 1978360 * 2
def baseEnd_1978360 : Nat := 451488705612882173822975

theorem tailTrace_1978360 : CollatzResearch.WordTrace tailWord_1978360 prefixEnd_1978360 451488705612882173822975 := by
  unfold tailWord_1978360
  simp only [CollatzResearch.WordTrace]
  refine ⟨36078358556373535916674267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48104478075164714555565689 36078358556373535916674267)
  ·
    refine ⟨54117537834560303875011401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36078358556373535916674267 54117537834560303875011401)
    ·
      refine ⟨40588153375920227906258551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54117537834560303875011401 40588153375920227906258551)
      ·
        refine ⟨60882230063880341859387827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40588153375920227906258551 60882230063880341859387827)
        ·
          refine ⟨91323345095820512789081741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60882230063880341859387827 91323345095820512789081741)
          ·
            refine ⟨34246254410932692295905653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91323345095820512789081741 34246254410932692295905653)
            ·
              refine ⟨3210586351024939902741155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34246254410932692295905653 3210586351024939902741155)
              ·
                refine ⟨4815879526537409854111733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210586351024939902741155 4815879526537409854111733)
                ·
                  refine ⟨451488705612882173822975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4815879526537409854111733 451488705612882173822975)
                  ·
                    rfl

theorem cell21_1978360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_1978360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978360 prefixEnd_1978360 := by exact prefixLift 1978360
  have htrace : WordTrace (prefixWord ++ tailWord_1978360) baseStart_1978360 baseEnd_1978360 := by
    simpa [prefixWord, tailWord_1978360, baseEnd_1978360] using wordTrace_append hprefix tailTrace_1978360
  have hstable : (prefixWord ++ tailWord_1978360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978360).length < 2 ^ (prefixWord ++ tailWord_1978360).sum := by decide
  have hdescent : baseEnd_1978360 < baseStart_1978360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978366 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_1978366 : Nat := 118140960795 + 1978366 * 2 ^ 59
def prefixEnd_1978366 : Nat := 4983230072969 + 3 ^ 40 * 1978366 * 2
def baseEnd_1978366 : Nat := 451490074894627496722963

theorem tailTrace_1978366 : CollatzResearch.WordTrace tailWord_1978366 prefixEnd_1978366 451490074894627496722963 := by
  unfold tailWord_1978366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9019616993840666857258369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48104623967150223238711301 9019616993840666857258369)
  ·
    refine ⟨6764712745380500142943777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9019616993840666857258369 6764712745380500142943777)
    ·
      refine ⟨5073534559035375107207833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6764712745380500142943777 5073534559035375107207833)
      ·
        refine ⟨3805150919276531330405875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5073534559035375107207833 3805150919276531330405875)
        ·
          refine ⟨5707726378914796995608813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3805150919276531330405875 5707726378914796995608813)
          ·
            refine ⟨2140397392093048873353305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5707726378914796995608813 2140397392093048873353305)
            ·
              refine ⟨1605298044069786655014979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2140397392093048873353305 1605298044069786655014979)
              ·
                refine ⟨2407947066104679982522469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605298044069786655014979 2407947066104679982522469)
                ·
                  refine ⟨451490074894627496722963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2407947066104679982522469 451490074894627496722963)
                  ·
                    rfl

theorem cell21_1978366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_1978366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978366 prefixEnd_1978366 := by exact prefixLift 1978366
  have htrace : WordTrace (prefixWord ++ tailWord_1978366) baseStart_1978366 baseEnd_1978366 := by
    simpa [prefixWord, tailWord_1978366, baseEnd_1978366] using wordTrace_append hprefix tailTrace_1978366
  have hstable : (prefixWord ++ tailWord_1978366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978366).length < 2 ^ (prefixWord ++ tailWord_1978366).sum := by decide
  have hdescent : baseEnd_1978366 < baseStart_1978366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978453 : List Nat := [1, 3, 2, 2, 1, 3, 1, 5, 3]
def baseStart_1978453 : Nat := 118140960795 + 1978453 * 2 ^ 59
def prefixEnd_1978453 : Nat := 4983230072969 + 3 ^ 40 * 1978453 * 2
def baseEnd_1978453 : Nat := 451509929479934678772785

theorem tailTrace_1978453 : CollatzResearch.WordTrace tailWord_1978453 prefixEnd_1978453 451509929479934678772785 := by
  unfold tailWord_1978453
  simp only [CollatzResearch.WordTrace]
  refine ⟨72160109101410148716484013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48106739400940099144322675 72160109101410148716484013)
  ·
    refine ⟨27060040913028805768681505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72160109101410148716484013 27060040913028805768681505)
    ·
      refine ⟨20295030684771604326511129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27060040913028805768681505 20295030684771604326511129)
      ·
        refine ⟨15221273013578703244883347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20295030684771604326511129 15221273013578703244883347)
        ·
          refine ⟨22831909520368054867325021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15221273013578703244883347 22831909520368054867325021)
          ·
            refine ⟨8561966070138020575246883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22831909520368054867325021 8561966070138020575246883)
            ·
              refine ⟨12842949105207030862870325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561966070138020575246883 12842949105207030862870325)
              ·
                refine ⟨1204026478613159143394093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12842949105207030862870325 1204026478613159143394093)
                ·
                  refine ⟨451509929479934678772785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204026478613159143394093 451509929479934678772785)
                  ·
                    rfl

theorem cell21_1978453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_1978453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978453 prefixEnd_1978453 := by exact prefixLift 1978453
  have htrace : WordTrace (prefixWord ++ tailWord_1978453) baseStart_1978453 baseEnd_1978453 := by
    simpa [prefixWord, tailWord_1978453, baseEnd_1978453] using wordTrace_append hprefix tailTrace_1978453
  have hstable : (prefixWord ++ tailWord_1978453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978453).length < 2 ^ (prefixWord ++ tailWord_1978453).sum := by decide
  have hdescent : baseEnd_1978453 < baseStart_1978453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978467 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 4]
def baseStart_1978467 : Nat := 118140960795 + 1978467 * 2 ^ 59
def prefixEnd_1978467 : Nat := 4983230072969 + 3 ^ 40 * 1978467 * 2
def baseEnd_1978467 : Nat := 451513124470673765539423

theorem tailTrace_1978467 : CollatzResearch.WordTrace tailWord_1978467 prefixEnd_1978467 451513124470673765539423 := by
  unfold tailWord_1978467
  simp only [CollatzResearch.WordTrace]
  refine ⟨72160619723359429107493655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48107079815572952738329103 72160619723359429107493655)
  ·
    refine ⟨108240929585039143661240483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72160619723359429107493655 108240929585039143661240483)
    ·
      refine ⟨162361394377558715491860725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108240929585039143661240483 162361394377558715491860725)
      ·
        refine ⟨15221380722896129577361943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162361394377558715491860725 15221380722896129577361943)
        ·
          refine ⟨22832071084344194366042915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15221380722896129577361943 22832071084344194366042915)
          ·
            refine ⟨34248106626516291549064373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22832071084344194366042915 34248106626516291549064373)
            ·
              refine ⟨3210759996235902332724785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34248106626516291549064373 3210759996235902332724785)
              ·
                refine ⟨2408069997176926749543589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3210759996235902332724785 2408069997176926749543589)
                ·
                  refine ⟨451513124470673765539423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408069997176926749543589 451513124470673765539423)
                  ·
                    rfl

theorem cell21_1978467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 4].length) (baseStart_1978467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978467 prefixEnd_1978467 := by exact prefixLift 1978467
  have htrace : WordTrace (prefixWord ++ tailWord_1978467) baseStart_1978467 baseEnd_1978467 := by
    simpa [prefixWord, tailWord_1978467, baseEnd_1978467] using wordTrace_append hprefix tailTrace_1978467
  have hstable : (prefixWord ++ tailWord_1978467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978467).length < 2 ^ (prefixWord ++ tailWord_1978467).sum := by decide
  have hdescent : baseEnd_1978467 < baseStart_1978467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978529 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 5]
def baseStart_1978529 : Nat := 118140960795 + 1978529 * 2 ^ 59
def prefixEnd_1978529 : Nat := 4983230072969 + 3 ^ 40 * 1978529 * 2
def baseEnd_1978529 : Nat := 451527273715375435505963

theorem tailTrace_1978529 : CollatzResearch.WordTrace tailWord_1978529 prefixEnd_1978529 451527273715375435505963 := by
  unfold tailWord_1978529
  simp only [CollatzResearch.WordTrace]
  refine ⟨72162881049134813696250641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48108587366089875797500427 72162881049134813696250641)
  ·
    refine ⟨54122160786851110272187981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72162881049134813696250641 54122160786851110272187981)
    ·
      refine ⟨20295810295069166352070493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54122160786851110272187981 20295810295069166352070493)
      ·
        refine ⟨7610928860650937382026435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20295810295069166352070493 7610928860650937382026435)
        ·
          refine ⟨11416393290976406073039653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7610928860650937382026435 11416393290976406073039653)
          ·
            refine ⟨2140573742058076138694935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11416393290976406073039653 2140573742058076138694935)
            ·
              refine ⟨3210860613087114208042403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140573742058076138694935 3210860613087114208042403)
              ·
                refine ⟨4816290919630671312063605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210860613087114208042403 4816290919630671312063605)
                ·
                  refine ⟨451527273715375435505963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4816290919630671312063605 451527273715375435505963)
                  ·
                    rfl

theorem cell21_1978529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_1978529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978529 prefixEnd_1978529 := by exact prefixLift 1978529
  have htrace : WordTrace (prefixWord ++ tailWord_1978529) baseStart_1978529 baseEnd_1978529 := by
    simpa [prefixWord, tailWord_1978529, baseEnd_1978529] using wordTrace_append hprefix tailTrace_1978529
  have hstable : (prefixWord ++ tailWord_1978529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978529).length < 2 ^ (prefixWord ++ tailWord_1978529).sum := by decide
  have hdescent : baseEnd_1978529 < baseStart_1978529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978605 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1978605 : Nat := 118140960795 + 1978605 * 2 ^ 59
def prefixEnd_1978605 : Nat := 4983230072969 + 3 ^ 40 * 1978605 * 2
def baseEnd_1978605 : Nat := 451544617950816192239141

theorem tailTrace_1978605 : CollatzResearch.WordTrace tailWord_1978605 prefixEnd_1978605 451544617950816192239141 := by
  unfold tailWord_1978605
  simp only [CollatzResearch.WordTrace]
  refine ⟨72165652996859478676017269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48110435331239652450678179 72165652996859478676017269)
  ·
    refine ⟨6765529968455576125876619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72165652996859478676017269 6765529968455576125876619)
    ·
      refine ⟨10148294952683364188814929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6765529968455576125876619 10148294952683364188814929)
      ·
        refine ⟨7611221214512523141611197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10148294952683364188814929 7611221214512523141611197)
        ·
          refine ⟨2854207955442196178104199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7611221214512523141611197 2854207955442196178104199)
          ·
            refine ⟨4281311933163294267156299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854207955442196178104199 4281311933163294267156299)
            ·
              refine ⟨6421967899744941400734449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4281311933163294267156299 6421967899744941400734449)
              ·
                refine ⟨4816475924808706050550837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6421967899744941400734449 4816475924808706050550837)
                ·
                  refine ⟨451544617950816192239141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4816475924808706050550837 451544617950816192239141)
                  ·
                    rfl

theorem cell21_1978605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1978605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978605 prefixEnd_1978605 := by exact prefixLift 1978605
  have htrace : WordTrace (prefixWord ++ tailWord_1978605) baseStart_1978605 baseEnd_1978605 := by
    simpa [prefixWord, tailWord_1978605, baseEnd_1978605] using wordTrace_append hprefix tailTrace_1978605
  have hstable : (prefixWord ++ tailWord_1978605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978605).length < 2 ^ (prefixWord ++ tailWord_1978605).sum := by decide
  have hdescent : baseEnd_1978605 < baseStart_1978605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978616 : List Nat := [2, 1, 2, 1, 1, 2, 1, 11]
def baseStart_1978616 : Nat := 118140960795 + 1978616 * 2 ^ 59
def prefixEnd_1978616 : Nat := 4983230072969 + 3 ^ 40 * 1978616 * 2
def baseEnd_1978616 : Nat := 150515709433560872518595

theorem tailTrace_1978616 : CollatzResearch.WordTrace tailWord_1978616 prefixEnd_1978616 150515709433560872518595 := by
  unfold tailWord_1978616
  simp only [CollatzResearch.WordTrace]
  refine ⟨36083027099909813777333851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48110702799879751703111801 36083027099909813777333851)
  ·
    refine ⟨54124540649864720666000777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36083027099909813777333851 54124540649864720666000777)
    ·
      refine ⟨40593405487398540499500583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54124540649864720666000777 40593405487398540499500583)
      ·
        refine ⟨60890108231097810749250875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40593405487398540499500583 60890108231097810749250875)
        ·
          refine ⟨91335162346646716123876313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60890108231097810749250875 91335162346646716123876313)
          ·
            refine ⟨68501371759985037092907235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91335162346646716123876313 68501371759985037092907235)
            ·
              refine ⟨102752057639977555639360853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68501371759985037092907235 102752057639977555639360853)
              ·
                refine ⟨150515709433560872518595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 102752057639977555639360853 150515709433560872518595)
                ·
                  rfl

theorem cell21_1978616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_1978616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978616 prefixEnd_1978616 := by exact prefixLift 1978616
  have htrace : WordTrace (prefixWord ++ tailWord_1978616) baseStart_1978616 baseEnd_1978616 := by
    simpa [prefixWord, tailWord_1978616, baseEnd_1978616] using wordTrace_append hprefix tailTrace_1978616
  have hstable : (prefixWord ++ tailWord_1978616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978616).length < 2 ^ (prefixWord ++ tailWord_1978616).sum := by decide
  have hdescent : baseEnd_1978616 < baseStart_1978616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978622 : List Nat := [4, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1978622 : Nat := 118140960795 + 1978622 * 2 ^ 59
def prefixEnd_1978622 : Nat := 4983230072969 + 3 ^ 40 * 1978622 * 2
def baseEnd_1978622 : Nat := 451548497582427940455773

theorem tailTrace_1978622 : CollatzResearch.WordTrace tailWord_1978622 prefixEnd_1978622 451548497582427940455773 := by
  unfold tailWord_1978622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020784129724736322423265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48110848691865260386257413 9020784129724736322423265)
  ·
    refine ⟨6765588097293552241817449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9020784129724736322423265 6765588097293552241817449)
    ·
      refine ⟨5074191072970164181363087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6765588097293552241817449 5074191072970164181363087)
      ·
        refine ⟨7611286609455246272044631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5074191072970164181363087 7611286609455246272044631)
        ·
          refine ⟨11416929914182869408066947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7611286609455246272044631 11416929914182869408066947)
          ·
            refine ⟨17125394871274304112100421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11416929914182869408066947 17125394871274304112100421)
            ·
              refine ⟨3211011538363932021018829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17125394871274304112100421 3211011538363932021018829)
              ·
                refine ⟨1204129326886474507882061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3211011538363932021018829 1204129326886474507882061)
                ·
                  refine ⟨451548497582427940455773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204129326886474507882061 451548497582427940455773)
                  ·
                    rfl

theorem cell21_1978622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1978622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978622 prefixEnd_1978622 := by exact prefixLift 1978622
  have htrace : WordTrace (prefixWord ++ tailWord_1978622) baseStart_1978622 baseEnd_1978622 := by
    simpa [prefixWord, tailWord_1978622, baseEnd_1978622] using wordTrace_append hprefix tailTrace_1978622
  have hstable : (prefixWord ++ tailWord_1978622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978622).length < 2 ^ (prefixWord ++ tailWord_1978622).sum := by decide
  have hdescent : baseEnd_1978622 < baseStart_1978622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978653 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 4]
def baseStart_1978653 : Nat := 118140960795 + 1978653 * 2 ^ 59
def prefixEnd_1978653 : Nat := 4983230072969 + 3 ^ 40 * 1978653 * 2
def baseEnd_1978653 : Nat := 451555572204778775439043

theorem tailTrace_1978653 : CollatzResearch.WordTrace tailWord_1978653 prefixEnd_1978653 451555572204778775439043 := by
  unfold tailWord_1978653
  simp only [CollatzResearch.WordTrace]
  refine ⟨72167403700685582873764613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48111602467123721915843075 72167403700685582873764613)
  ·
    refine ⟨13531388193878546788830865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72167403700685582873764613 13531388193878546788830865)
    ·
      refine ⟨10148541145408910091623149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13531388193878546788830865 10148541145408910091623149)
      ·
        refine ⟨3805702929528341284358681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10148541145408910091623149 3805702929528341284358681)
        ·
          refine ⟨2854277197146255963269011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3805702929528341284358681 2854277197146255963269011)
          ·
            refine ⟨4281415795719383944903517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854277197146255963269011 4281415795719383944903517)
            ·
              refine ⟨1605530923394768979338819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4281415795719383944903517 1605530923394768979338819)
              ·
                refine ⟨2408296385092153469008229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605530923394768979338819 2408296385092153469008229)
                ·
                  refine ⟨451555572204778775439043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408296385092153469008229 451555572204778775439043)
                  ·
                    rfl

theorem cell21_1978653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_1978653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978653 prefixEnd_1978653 := by exact prefixLift 1978653
  have htrace : WordTrace (prefixWord ++ tailWord_1978653) baseStart_1978653 baseEnd_1978653 := by
    simpa [prefixWord, tailWord_1978653, baseEnd_1978653] using wordTrace_append hprefix tailTrace_1978653
  have hstable : (prefixWord ++ tailWord_1978653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978653).length < 2 ^ (prefixWord ++ tailWord_1978653).sum := by decide
  have hdescent : baseEnd_1978653 < baseStart_1978653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978723 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 7]
def baseStart_1978723 : Nat := 118140960795 + 1978723 * 2 ^ 59
def prefixEnd_1978723 : Nat := 4983230072969 + 3 ^ 40 * 1978723 * 2
def baseEnd_1978723 : Nat := 451571547158474209272233

theorem tailTrace_1978723 : CollatzResearch.WordTrace tailWord_1978723 prefixEnd_1978723 451571547158474209272233 := by
  unfold tailWord_1978723
  simp only [CollatzResearch.WordTrace]
  refine ⟨72169956810431984828812823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48113304540287989885875215 72169956810431984828812823)
  ·
    refine ⟨108254935215647977243219235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72169956810431984828812823 108254935215647977243219235)
    ·
      refine ⟨162382402823471965864828853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108254935215647977243219235 162382402823471965864828853)
      ·
        refine ⟨15223350264700496799827705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162382402823471965864828853 15223350264700496799827705)
        ·
          refine ⟨11417512698525372599870779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15223350264700496799827705 11417512698525372599870779)
          ·
            refine ⟨17126269047788058899806169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11417512698525372599870779 17126269047788058899806169)
            ·
              refine ⟨12844701785841044174854627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17126269047788058899806169 12844701785841044174854627)
              ·
                refine ⟨19267052678761566262281941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12844701785841044174854627 19267052678761566262281941)
                ·
                  refine ⟨451571547158474209272233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19267052678761566262281941 451571547158474209272233)
                  ·
                    rfl

theorem cell21_1978723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_1978723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978723 prefixEnd_1978723 := by exact prefixLift 1978723
  have htrace : WordTrace (prefixWord ++ tailWord_1978723) baseStart_1978723 baseEnd_1978723 := by
    simpa [prefixWord, tailWord_1978723, baseEnd_1978723] using wordTrace_append hprefix tailTrace_1978723
  have hstable : (prefixWord ++ tailWord_1978723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978723).length < 2 ^ (prefixWord ++ tailWord_1978723).sum := by decide
  have hdescent : baseEnd_1978723 < baseStart_1978723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978805 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 4]
def baseStart_1978805 : Nat := 118140960795 + 1978805 * 2 ^ 59
def prefixEnd_1978805 : Nat := 4983230072969 + 3 ^ 40 * 1978805 * 2
def baseEnd_1978805 : Nat := 451590260675660288905399

theorem tailTrace_1978805 : CollatzResearch.WordTrace tailWord_1978805 prefixEnd_1978805 451590260675660288905399 := by
  unfold tailWord_1978805
  simp only [CollatzResearch.WordTrace]
  refine ⟨72172947596134912833297869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48115298397423275222198579 72172947596134912833297869)
  ·
    refine ⟨27064855348550592312486701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72172947596134912833297869 27064855348550592312486701)
    ·
      refine ⟨10149320755706472117182513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27064855348550592312486701 10149320755706472117182513)
      ·
        refine ⟨7611990566779854087886885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10149320755706472117182513 7611990566779854087886885)
        ·
          refine ⟨1427248231271222641478791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7611990566779854087886885 1427248231271222641478791)
          ·
            refine ⟨2140872346906833962218187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427248231271222641478791 2140872346906833962218187)
            ·
              refine ⟨3211308520360250943327281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140872346906833962218187 3211308520360250943327281)
              ·
                refine ⟨2408481390270188207495461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3211308520360250943327281 2408481390270188207495461)
                ·
                  refine ⟨451590260675660288905399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408481390270188207495461 451590260675660288905399)
                  ·
                    rfl

theorem cell21_1978805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_1978805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978805 prefixEnd_1978805 := by exact prefixLift 1978805
  have htrace : WordTrace (prefixWord ++ tailWord_1978805) baseStart_1978805 baseEnd_1978805 := by
    simpa [prefixWord, tailWord_1978805, baseEnd_1978805] using wordTrace_append hprefix tailTrace_1978805
  have hstable : (prefixWord ++ tailWord_1978805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978805).length < 2 ^ (prefixWord ++ tailWord_1978805).sum := by decide
  have hdescent : baseEnd_1978805 < baseStart_1978805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978861 : List Nat := [1, 5, 1, 3, 1, 1, 9]
def baseStart_1978861 : Nat := 118140960795 + 1978861 * 2 ^ 59
def prefixEnd_1978861 : Nat := 4983230072969 + 3 ^ 40 * 1978861 * 2
def baseEnd_1978861 : Nat := 50178115626512959552439

theorem tailTrace_1978861 : CollatzResearch.WordTrace tailWord_1978861 prefixEnd_1978861 50178115626512959552439 := by
  unfold tailWord_1978861
  simp only [CollatzResearch.WordTrace]
  refine ⟨72174990083932034397336437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48116660055954689598224291 72174990083932034397336437)
  ·
    refine ⟨6766405320368628224750291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72174990083932034397336437 6766405320368628224750291)
    ·
      refine ⟨10149607980552942337125437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6766405320368628224750291 10149607980552942337125437)
      ·
        refine ⟨3806102992707353376422039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10149607980552942337125437 3806102992707353376422039)
        ·
          refine ⟨5709154489061030064633059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3806102992707353376422039 5709154489061030064633059)
          ·
            refine ⟨8563731733591545096949589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709154489061030064633059 8563731733591545096949589)
            ·
              refine ⟨50178115626512959552439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8563731733591545096949589 50178115626512959552439)
              ·
                rfl

theorem cell21_1978861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 9].length) (baseStart_1978861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978861 prefixEnd_1978861 := by exact prefixLift 1978861
  have htrace : WordTrace (prefixWord ++ tailWord_1978861) baseStart_1978861 baseEnd_1978861 := by
    simpa [prefixWord, tailWord_1978861, baseEnd_1978861] using wordTrace_append hprefix tailTrace_1978861
  have hstable : (prefixWord ++ tailWord_1978861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978861).length < 2 ^ (prefixWord ++ tailWord_1978861).sum := by decide
  have hdescent : baseEnd_1978861 < baseStart_1978861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978889 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 8]
def baseStart_1978889 : Nat := 118140960795 + 1978889 * 2 ^ 59
def prefixEnd_1978889 : Nat := 4983230072969 + 3 ^ 40 * 1978889 * 2
def baseEnd_1978889 : Nat := 451609430620094809505227

theorem tailTrace_1978889 : CollatzResearch.WordTrace tailWord_1978889 prefixEnd_1978889 451609430620094809505227 := by
  unfold tailWord_1978889
  simp only [CollatzResearch.WordTrace]
  refine ⟨72176011327830595179355721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48117340885220396786237147 72176011327830595179355721)
  ·
    refine ⟨54132008495872946384516791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72176011327830595179355721 54132008495872946384516791)
    ·
      refine ⟨81198012743809419576775187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54132008495872946384516791 81198012743809419576775187)
      ·
        refine ⟨121797019115714129365162781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81198012743809419576775187 121797019115714129365162781)
        ·
          refine ⟨45673882168392798511936043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121797019115714129365162781 45673882168392798511936043)
          ·
            refine ⟨68510823252589197767904065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45673882168392798511936043 68510823252589197767904065)
            ·
              refine ⟨51383117439441898325928049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68510823252589197767904065 51383117439441898325928049)
              ·
                refine ⟨38537338079581423744446037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51383117439441898325928049 38537338079581423744446037)
                ·
                  refine ⟨451609430620094809505227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38537338079581423744446037 451609430620094809505227)
                  ·
                    rfl

theorem cell21_1978889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_1978889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978889 prefixEnd_1978889 := by exact prefixLift 1978889
  have htrace : WordTrace (prefixWord ++ tailWord_1978889) baseStart_1978889 baseEnd_1978889 := by
    simpa [prefixWord, tailWord_1978889, baseEnd_1978889] using wordTrace_append hprefix tailTrace_1978889
  have hstable : (prefixWord ++ tailWord_1978889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978889).length < 2 ^ (prefixWord ++ tailWord_1978889).sum := by decide
  have hdescent : baseEnd_1978889 < baseStart_1978889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978926 : List Nat := [4, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_1978926 : Nat := 118140960795 + 1978926 * 2 ^ 59
def prefixEnd_1978926 : Nat := 4983230072969 + 3 ^ 40 * 1978926 * 2
def baseEnd_1978926 : Nat := 451617874524190967388485

theorem tailTrace_1978926 : CollatzResearch.WordTrace tailWord_1978926 prefixEnd_1978926 451617874524190967388485 := by
  unfold tailWord_1978926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9022170103587068812306579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48118240552464366998968421 9022170103587068812306579)
  ·
    refine ⟨13533255155380603218459869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9022170103587068812306579 13533255155380603218459869)
    ·
      refine ⟨5074970683267726206922451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13533255155380603218459869 5074970683267726206922451)
      ·
        refine ⟨7612456024901589310383677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5074970683267726206922451 7612456024901589310383677)
        ·
          refine ⟨2854671009338095991393879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7612456024901589310383677 2854671009338095991393879)
          ·
            refine ⟨4282006514007143987090819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854671009338095991393879 4282006514007143987090819)
            ·
              refine ⟨6423009771010715980636229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282006514007143987090819 6423009771010715980636229)
              ·
                refine ⟨1204314332064509246369293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6423009771010715980636229 1204314332064509246369293)
                ·
                  refine ⟨451617874524190967388485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204314332064509246369293 451617874524190967388485)
                  ·
                    rfl

theorem cell21_1978926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_1978926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978926 prefixEnd_1978926 := by exact prefixLift 1978926
  have htrace : WordTrace (prefixWord ++ tailWord_1978926) baseStart_1978926 baseEnd_1978926 := by
    simpa [prefixWord, tailWord_1978926, baseEnd_1978926] using wordTrace_append hprefix tailTrace_1978926
  have hstable : (prefixWord ++ tailWord_1978926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978926).length < 2 ^ (prefixWord ++ tailWord_1978926).sum := by decide
  have hdescent : baseEnd_1978926 < baseStart_1978926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978951 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 7]
def baseStart_1978951 : Nat := 118140960795 + 1978951 * 2 ^ 59
def prefixEnd_1978951 : Nat := 4983230072969 + 3 ^ 40 * 1978951 * 2
def baseEnd_1978951 : Nat := 451623579864796479471767

theorem tailTrace_1978951 : CollatzResearch.WordTrace tailWord_1978951 prefixEnd_1978951 451623579864796479471767 := by
  unfold tailWord_1978951
  simp only [CollatzResearch.WordTrace]
  refine ⟨72178272653605979768112707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48118848435737319845408471 72178272653605979768112707)
  ·
    refine ⟨108267408980408969652169061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72178272653605979768112707 108267408980408969652169061)
    ·
      refine ⟨20300139183826681809781699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108267408980408969652169061 20300139183826681809781699)
      ·
        refine ⟨30450208775740022714672549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20300139183826681809781699 30450208775740022714672549)
        ·
          refine ⟨5709414145451254259001103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30450208775740022714672549 5709414145451254259001103)
          ·
            refine ⟨8564121218176881388501655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709414145451254259001103 8564121218176881388501655)
            ·
              refine ⟨12846181827265322082752483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8564121218176881388501655 12846181827265322082752483)
              ·
                refine ⟨19269272740897983124128725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12846181827265322082752483 19269272740897983124128725)
                ·
                  refine ⟨451623579864796479471767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19269272740897983124128725 451623579864796479471767)
                  ·
                    rfl

theorem cell21_1978951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_1978951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978951 prefixEnd_1978951 := by exact prefixLift 1978951
  have htrace : WordTrace (prefixWord ++ tailWord_1978951) baseStart_1978951 baseEnd_1978951 := by
    simpa [prefixWord, tailWord_1978951, baseEnd_1978951] using wordTrace_append hprefix tailTrace_1978951
  have hstable : (prefixWord ++ tailWord_1978951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978951).length < 2 ^ (prefixWord ++ tailWord_1978951).sum := by decide
  have hdescent : baseEnd_1978951 < baseStart_1978951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978968 : List Nat := [2, 1, 2, 2, 1, 2, 3, 5, 3]
def baseStart_1978968 : Nat := 118140960795 + 1978968 * 2 ^ 59
def prefixEnd_1978968 : Nat := 4983230072969 + 3 ^ 40 * 1978968 * 2
def baseEnd_1978968 : Nat := 451627459496408227688399

theorem tailTrace_1978968 : CollatzResearch.WordTrace tailWord_1978968 prefixEnd_1978968 451627459496408227688399 := by
  unfold tailWord_1978968
  simp only [CollatzResearch.WordTrace]
  refine ⟨36089446347272195835740779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48119261796362927780987705 36089446347272195835740779)
  ·
    refine ⟨54134169520908293753611169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36089446347272195835740779 54134169520908293753611169)
    ·
      refine ⟨40600627140681220315208377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54134169520908293753611169 40600627140681220315208377)
      ·
        refine ⟨30450470355510915236406283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40600627140681220315208377 30450470355510915236406283)
        ·
          refine ⟨45675705533266372854609425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30450470355510915236406283 45675705533266372854609425)
          ·
            refine ⟨34256779149949779640957069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45675705533266372854609425 34256779149949779640957069)
            ·
              refine ⟨12846292181231167365358901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34256779149949779640957069 12846292181231167365358901)
              ·
                refine ⟨1204339891990421940502397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12846292181231167365358901 1204339891990421940502397)
                ·
                  refine ⟨451627459496408227688399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204339891990421940502397 451627459496408227688399)
                  ·
                    rfl

theorem cell21_1978968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 3].length) (baseStart_1978968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1978968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1978968 prefixEnd_1978968 := by exact prefixLift 1978968
  have htrace : WordTrace (prefixWord ++ tailWord_1978968) baseStart_1978968 baseEnd_1978968 := by
    simpa [prefixWord, tailWord_1978968, baseEnd_1978968] using wordTrace_append hprefix tailTrace_1978968
  have hstable : (prefixWord ++ tailWord_1978968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978968).length < 2 ^ (prefixWord ++ tailWord_1978968).sum := by decide
  have hdescent : baseEnd_1978968 < baseStart_1978968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979013 : List Nat := [1, 3, 1, 1, 4, 2, 4, 5]
def baseStart_1979013 : Nat := 118140960795 + 1979013 * 2 ^ 59
def prefixEnd_1979013 : Nat := 4983230072969 + 3 ^ 40 * 1979013 * 2
def baseEnd_1979013 : Nat := 150545909703166049812769

theorem tailTrace_1979013 : CollatzResearch.WordTrace tailWord_1979013 prefixEnd_1979013 150545909703166049812769 := by
  unfold tailWord_1979013
  simp only [CollatzResearch.WordTrace]
  refine ⟨72180533979381364356869693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48120355986254242904579795 72180533979381364356869693)
  ·
    refine ⟨27067700242268011633826135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72180533979381364356869693 27067700242268011633826135)
    ·
      refine ⟨40601550363402017450739203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27067700242268011633826135 40601550363402017450739203)
      ·
        refine ⟨60902325545103026176108805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40601550363402017450739203 60902325545103026176108805)
        ·
          refine ⟨11419186039706817408020401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60902325545103026176108805 11419186039706817408020401)
          ·
            refine ⟨8564389529780113056015301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11419186039706817408020401 8564389529780113056015301)
            ·
              refine ⟨1605823036833771198002869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8564389529780113056015301 1605823036833771198002869)
              ·
                refine ⟨150545909703166049812769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1605823036833771198002869 150545909703166049812769)
                ·
                  rfl

theorem cell21_1979013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 5].length) (baseStart_1979013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979013 prefixEnd_1979013 := by exact prefixLift 1979013
  have htrace : WordTrace (prefixWord ++ tailWord_1979013) baseStart_1979013 baseEnd_1979013 := by
    simpa [prefixWord, tailWord_1979013, baseEnd_1979013] using wordTrace_append hprefix tailTrace_1979013
  have hstable : (prefixWord ++ tailWord_1979013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979013).length < 2 ^ (prefixWord ++ tailWord_1979013).sum := by decide
  have hdescent : baseEnd_1979013 < baseStart_1979013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979050 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_1979050 : Nat := 118140960795 + 1979050 * 2 ^ 59
def prefixEnd_1979050 : Nat := 4983230072969 + 3 ^ 40 * 1979050 * 2
def baseEnd_1979050 : Nat := 451646173013594307321565

theorem tailTrace_1979050 : CollatzResearch.WordTrace tailWord_1979050 prefixEnd_1979050 451646173013594307321565 := by
  unfold tailWord_1979050
  simp only [CollatzResearch.WordTrace]
  refine ⟨18045470870061829918991651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48121255653498213117311069 18045470870061829918991651)
  ·
    refine ⟨27068206305092744878487477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18045470870061829918991651 27068206305092744878487477)
    ·
      refine ⟨2537644341102444832358201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27068206305092744878487477 2537644341102444832358201)
      ·
        refine ⟨1903233255826833624268651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2537644341102444832358201 1903233255826833624268651)
        ·
          refine ⟨2854849883740250436402977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903233255826833624268651 2854849883740250436402977)
          ·
            refine ⟨2141137412805187827302233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2854849883740250436402977 2141137412805187827302233)
            ·
              refine ⟨1605853059603890870476675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2141137412805187827302233 1605853059603890870476675)
              ·
                refine ⟨2408779589405836305715013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605853059603890870476675 2408779589405836305715013)
                ·
                  refine ⟨451646173013594307321565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408779589405836305715013 451646173013594307321565)
                  ·
                    rfl

theorem cell21_1979050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_1979050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979050 prefixEnd_1979050 := by exact prefixLift 1979050
  have htrace : WordTrace (prefixWord ++ tailWord_1979050) baseStart_1979050 baseEnd_1979050 := by
    simpa [prefixWord, tailWord_1979050, baseEnd_1979050] using wordTrace_append hprefix tailTrace_1979050
  have hstable : (prefixWord ++ tailWord_1979050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979050).length < 2 ^ (prefixWord ++ tailWord_1979050).sum := by decide
  have hdescent : baseEnd_1979050 < baseStart_1979050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979072 : List Nat := [2, 1, 1, 2, 4, 2, 2, 7]
def baseStart_1979072 : Nat := 118140960795 + 1979072 * 2 ^ 59
def prefixEnd_1979072 : Nat := 4983230072969 + 3 ^ 40 * 1979072 * 2
def baseEnd_1979072 : Nat := 150550397904442385984951

theorem tailTrace_1979072 : CollatzResearch.WordTrace tailWord_1979072 prefixEnd_1979072 150550397904442385984951 := by
  unfold tailWord_1979072
  simp only [CollatzResearch.WordTrace]
  refine ⟨36091342943083808716633735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48121790590778411622178313 36091342943083808716633735)
  ·
    refine ⟨54137014414625713074950603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36091342943083808716633735 54137014414625713074950603)
    ·
      refine ⟨81205521621938569612425905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54137014414625713074950603 81205521621938569612425905)
      ·
        refine ⟨60904141216453927209319429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81205521621938569612425905 60904141216453927209319429)
        ·
          refine ⟨11419526478085111351747393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60904141216453927209319429 11419526478085111351747393)
          ·
            refine ⟨8564644858563833513810545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11419526478085111351747393 8564644858563833513810545)
            ·
              refine ⟨6423483643922875135357909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8564644858563833513810545 6423483643922875135357909)
              ·
                refine ⟨150550397904442385984951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6423483643922875135357909 150550397904442385984951)
                ·
                  rfl

theorem cell21_1979072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_1979072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979072 prefixEnd_1979072 := by exact prefixLift 1979072
  have htrace : WordTrace (prefixWord ++ tailWord_1979072) baseStart_1979072 baseEnd_1979072 := by
    simpa [prefixWord, tailWord_1979072, baseEnd_1979072] using wordTrace_append hprefix tailTrace_1979072
  have hstable : (prefixWord ++ tailWord_1979072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979072).length < 2 ^ (prefixWord ++ tailWord_1979072).sum := by decide
  have hdescent : baseEnd_1979072 < baseStart_1979072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979092 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 4]
def baseStart_1979092 : Nat := 118140960795 + 1979092 * 2 ^ 59
def prefixEnd_1979092 : Nat := 4983230072969 + 3 ^ 40 * 1979092 * 2
def baseEnd_1979092 : Nat := 451655757985811567621479

theorem tailTrace_1979092 : CollatzResearch.WordTrace tailWord_1979092 prefixEnd_1979092 451655757985811567621479 := by
  unfold tailWord_1979092
  simp only [CollatzResearch.WordTrace]
  refine ⟨36091707673047580424497765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48122276897396773899330353 36091707673047580424497765)
  ·
    refine ⟨6767195188696421329593331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36091707673047580424497765 6767195188696421329593331)
    ·
      refine ⟨10150792783044631994389997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6767195188696421329593331 10150792783044631994389997)
      ·
        refine ⟨3806547293641736997896249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10150792783044631994389997 3806547293641736997896249)
        ·
          refine ⟨2854910470231302748422187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3806547293641736997896249 2854910470231302748422187)
          ·
            refine ⟨4282365705346954122633281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854910470231302748422187 4282365705346954122633281)
            ·
              refine ⟨3211774279010215591974961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4282365705346954122633281 3211774279010215591974961)
              ·
                refine ⟨2408830709257661693981221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3211774279010215591974961 2408830709257661693981221)
                ·
                  refine ⟨451655757985811567621479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408830709257661693981221 451655757985811567621479)
                  ·
                    rfl

theorem cell21_1979092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_1979092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979092 prefixEnd_1979092 := by exact prefixLift 1979092
  have htrace : WordTrace (prefixWord ++ tailWord_1979092) baseStart_1979092 baseEnd_1979092 := by
    simpa [prefixWord, tailWord_1979092, baseEnd_1979092] using wordTrace_append hprefix tailTrace_1979092
  have hstable : (prefixWord ++ tailWord_1979092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979092).length < 2 ^ (prefixWord ++ tailWord_1979092).sum := by decide
  have hdescent : baseEnd_1979092 < baseStart_1979092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979182 : List Nat := [4, 1, 3, 2, 1, 1, 4, 5]
def baseStart_1979182 : Nat := 118140960795 + 1979182 * 2 ^ 59
def prefixEnd_1979182 : Nat := 4983230072969 + 3 ^ 40 * 1979182 * 2
def baseEnd_1979182 : Nat := 150558765737330470373765

theorem tailTrace_1979182 : CollatzResearch.WordTrace tailWord_1979182 prefixEnd_1979182 150558765737330470373765 := by
  unfold tailWord_1979182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9023337239471138277471475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48124465277179404146514533 9023337239471138277471475)
  ·
    refine ⟨13535005859206707416207213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9023337239471138277471475 13535005859206707416207213)
    ·
      refine ⟨5075627197202515281077705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13535005859206707416207213 5075627197202515281077705)
      ·
        refine ⟨3806720397901886460808279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5075627197202515281077705 3806720397901886460808279)
        ·
          refine ⟨5710080596852829691212419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3806720397901886460808279 5710080596852829691212419)
          ·
            refine ⟨8565120895279244536818629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5710080596852829691212419 8565120895279244536818629)
            ·
              refine ⟨1605960167864858350653493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8565120895279244536818629 1605960167864858350653493)
              ·
                refine ⟨150558765737330470373765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1605960167864858350653493 150558765737330470373765)
                ·
                  rfl

theorem cell21_1979182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_1979182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979182 prefixEnd_1979182 := by exact prefixLift 1979182
  have htrace : WordTrace (prefixWord ++ tailWord_1979182) baseStart_1979182 baseEnd_1979182 := by
    simpa [prefixWord, tailWord_1979182, baseEnd_1979182] using wordTrace_append hprefix tailTrace_1979182
  have hstable : (prefixWord ++ tailWord_1979182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979182).length < 2 ^ (prefixWord ++ tailWord_1979182).sum := by decide
  have hdescent : baseEnd_1979182 < baseStart_1979182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979283 : List Nat := [1, 1, 1, 2, 1, 2, 1, 12]
def baseStart_1979283 : Nat := 118140960795 + 1979283 * 2 ^ 59
def prefixEnd_1979283 : Nat := 4983230072969 + 3 ^ 40 * 1979283 * 2
def baseEnd_1979283 : Nat := 150566448929345893312585

theorem tailTrace_1979283 : CollatzResearch.WordTrace tailWord_1979283 prefixEnd_1979283 150566448929345893312585 := by
  unfold tailWord_1979283
  simp only [CollatzResearch.WordTrace]
  refine ⟨72190381688403200469198503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48126921125602133646132335 72190381688403200469198503)
  ·
    refine ⟨108285572532604800703797755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72190381688403200469198503 108285572532604800703797755)
    ·
      refine ⟨162428358798907201055696633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108285572532604800703797755 162428358798907201055696633)
      ·
        refine ⟨121821269099180400791772475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162428358798907201055696633 121821269099180400791772475)
        ·
          refine ⟨182731903648770601187658713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121821269099180400791772475 182731903648770601187658713)
          ·
            refine ⟨137048927736577950890744035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182731903648770601187658713 137048927736577950890744035)
            ·
              refine ⟨205573391604866926336116053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137048927736577950890744035 205573391604866926336116053)
              ·
                refine ⟨150566448929345893312585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 205573391604866926336116053 150566448929345893312585)
                ·
                  rfl

theorem cell21_1979283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 12].length) (baseStart_1979283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979283 prefixEnd_1979283 := by exact prefixLift 1979283
  have htrace : WordTrace (prefixWord ++ tailWord_1979283) baseStart_1979283 baseEnd_1979283 := by
    simpa [prefixWord, tailWord_1979283, baseEnd_1979283] using wordTrace_append hprefix tailTrace_1979283
  have hstable : (prefixWord ++ tailWord_1979283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979283).length < 2 ^ (prefixWord ++ tailWord_1979283).sum := by decide
  have hdescent : baseEnd_1979283 < baseStart_1979283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979382 : List Nat := [5, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_1979382 : Nat := 118140960795 + 1979382 * 2 ^ 59
def prefixEnd_1979382 : Nat := 4983230072969 + 3 ^ 40 * 1979382 * 2
def baseEnd_1979382 : Nat := 451721939936835507787553

theorem tailTrace_1979382 : CollatzResearch.WordTrace tailWord_1979382 prefixEnd_1979382 451721939936835507787553 := by
  unfold tailWord_1979382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512124532190283773565775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48129328343363026918034933 4512124532190283773565775)
  ·
    refine ⟨6768186798285425660348663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4512124532190283773565775 6768186798285425660348663)
    ·
      refine ⟨10152280197428138490522995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6768186798285425660348663 10152280197428138490522995)
      ·
        refine ⟨15228420296142207735784493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10152280197428138490522995 15228420296142207735784493)
        ·
          refine ⟨5710657611053327900919185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15228420296142207735784493 5710657611053327900919185)
          ·
            refine ⟨4282993208289995925689389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5710657611053327900919185 4282993208289995925689389)
            ·
              refine ⟨1606122453108748472133521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4282993208289995925689389 1606122453108748472133521)
              ·
                refine ⟨1204591839831561354100141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1606122453108748472133521 1204591839831561354100141)
                ·
                  refine ⟨451721939936835507787553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204591839831561354100141 451721939936835507787553)
                  ·
                    rfl

theorem cell21_1979382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_1979382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979382 prefixEnd_1979382 := by exact prefixLift 1979382
  have htrace : WordTrace (prefixWord ++ tailWord_1979382) baseStart_1979382 baseEnd_1979382 := by
    simpa [prefixWord, tailWord_1979382, baseEnd_1979382] using wordTrace_append hprefix tailTrace_1979382
  have hstable : (prefixWord ++ tailWord_1979382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979382).length < 2 ^ (prefixWord ++ tailWord_1979382).sum := by decide
  have hdescent : baseEnd_1979382 < baseStart_1979382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979452 : List Nat := [2, 2, 2, 2, 2, 2, 3, 6]
def baseStart_1979452 : Nat := 118140960795 + 1979452 * 2 ^ 59
def prefixEnd_1979452 : Nat := 4983230072969 + 3 ^ 40 * 1979452 * 2
def baseEnd_1979452 : Nat := 150579304963510313873581

theorem tailTrace_1979452 : CollatzResearch.WordTrace tailWord_1979452 prefixEnd_1979452 150579304963510313873581 := by
  unfold tailWord_1979452
  simp only [CollatzResearch.WordTrace]
  refine ⟨36098272812395471166050305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48131030416527294888067073 36098272812395471166050305)
  ·
    refine ⟨27073704609296603374537729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36098272812395471166050305 27073704609296603374537729)
    ·
      refine ⟨20305278456972452530903297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27073704609296603374537729 20305278456972452530903297)
      ·
        refine ⟨15228958842729339398177473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20305278456972452530903297 15228958842729339398177473)
        ·
          refine ⟨11421719132047004548633105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15228958842729339398177473 11421719132047004548633105)
          ·
            refine ⟨8566289349035253411474829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11421719132047004548633105 8566289349035253411474829)
            ·
              refine ⟨3212358505888220029303061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8566289349035253411474829 3212358505888220029303061)
              ·
                refine ⟨150579304963510313873581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3212358505888220029303061 150579304963510313873581)
                ·
                  rfl

theorem cell21_1979452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_1979452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979452 prefixEnd_1979452 := by exact prefixLift 1979452
  have htrace : WordTrace (prefixWord ++ tailWord_1979452) baseStart_1979452 baseEnd_1979452 := by
    simpa [prefixWord, tailWord_1979452, baseEnd_1979452] using wordTrace_append hprefix tailTrace_1979452
  have hstable : (prefixWord ++ tailWord_1979452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979452).length < 2 ^ (prefixWord ++ tailWord_1979452).sum := by decide
  have hdescent : baseEnd_1979452 < baseStart_1979452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979466 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_1979466 : Nat := 118140960795 + 1979466 * 2 ^ 59
def prefixEnd_1979466 : Nat := 4983230072969 + 3 ^ 40 * 1979466 * 2
def baseEnd_1979466 : Nat := 451741109881270028387381

theorem tailTrace_1979466 : CollatzResearch.WordTrace tailWord_1979466 prefixEnd_1979466 451741109881270028387381 := by
  unfold tailWord_1979466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18049264061685055680777563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48131370831160148482073501 18049264061685055680777563)
  ·
    refine ⟨27073896092527583521166345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18049264061685055680777563 27073896092527583521166345)
    ·
      refine ⟨20305422069395687640874759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27073896092527583521166345 20305422069395687640874759)
      ·
        refine ⟨30458133104093531461312139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20305422069395687640874759 30458133104093531461312139)
        ·
          refine ⟨45687199656140297191968209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30458133104093531461312139 45687199656140297191968209)
          ·
            refine ⟨34265399742105222893976157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45687199656140297191968209 34265399742105222893976157)
            ·
              refine ⟨12849524903289458585241059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34265399742105222893976157 12849524903289458585241059)
              ·
                refine ⟨19274287354934187877861589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12849524903289458585241059 19274287354934187877861589)
                ·
                  refine ⟨451741109881270028387381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19274287354934187877861589 451741109881270028387381)
                  ·
                    rfl

theorem cell21_1979466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_1979466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979466 prefixEnd_1979466 := by exact prefixLift 1979466
  have htrace : WordTrace (prefixWord ++ tailWord_1979466) baseStart_1979466 baseEnd_1979466 := by
    simpa [prefixWord, tailWord_1979466, baseEnd_1979466] using wordTrace_append hprefix tailTrace_1979466
  have hstable : (prefixWord ++ tailWord_1979466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979466).length < 2 ^ (prefixWord ++ tailWord_1979466).sum := by decide
  have hdescent : baseEnd_1979466 < baseStart_1979466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979486 : List Nat := [4, 4, 1, 1, 1, 2, 8]
def baseStart_1979486 : Nat := 118140960795 + 1979486 * 2 ^ 59
def prefixEnd_1979486 : Nat := 4983230072969 + 3 ^ 40 * 1979486 * 2
def baseEnd_1979486 : Nat := 50193963794861604228223

theorem tailTrace_1979486 : CollatzResearch.WordTrace tailWord_1979486 prefixEnd_1979486 50193963794861604228223 := by
  unfold tailWord_1979486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9024723213333470767354789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48131857137778510759225541 9024723213333470767354789)
  ·
    refine ⟨1692135602500025768879023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9024723213333470767354789 1692135602500025768879023)
    ·
      refine ⟨2538203403750038653318535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1692135602500025768879023 2538203403750038653318535)
      ·
        refine ⟨3807305105625057979977803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538203403750038653318535 3807305105625057979977803)
        ·
          refine ⟨5710957658437586969966705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807305105625057979977803 5710957658437586969966705)
          ·
            refine ⟨4283218243828190227475029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5710957658437586969966705 4283218243828190227475029)
            ·
              refine ⟨50193963794861604228223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4283218243828190227475029 50193963794861604228223)
              ·
                rfl

theorem cell21_1979486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 8].length) (baseStart_1979486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979486 prefixEnd_1979486 := by exact prefixLift 1979486
  have htrace : WordTrace (prefixWord ++ tailWord_1979486) baseStart_1979486 baseEnd_1979486 := by
    simpa [prefixWord, tailWord_1979486, baseEnd_1979486] using wordTrace_append hprefix tailTrace_1979486
  have hstable : (prefixWord ++ tailWord_1979486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979486).length < 2 ^ (prefixWord ++ tailWord_1979486).sum := by decide
  have hdescent : baseEnd_1979486 < baseStart_1979486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979497 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 6]
def baseStart_1979497 : Nat := 118140960795 + 1979497 * 2 ^ 59
def prefixEnd_1979497 : Nat := 4983230072969 + 3 ^ 40 * 1979497 * 2
def baseEnd_1979497 : Nat := 451748184503620863370651

theorem tailTrace_1979497 : CollatzResearch.WordTrace tailWord_1979497 prefixEnd_1979497 451748184503620863370651 := by
  unfold tailWord_1979497
  simp only [CollatzResearch.WordTrace]
  refine ⟨72198186909627915017488745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48132124606418610011659163 72198186909627915017488745)
  ·
    refine ⟨54148640182220936263116559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72198186909627915017488745 54148640182220936263116559)
    ·
      refine ⟨81222960273331404394674839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54148640182220936263116559 81222960273331404394674839)
      ·
        refine ⟨121834440409997106592012259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81222960273331404394674839 121834440409997106592012259)
        ·
          refine ⟨182751660614995659888018389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121834440409997106592012259 182751660614995659888018389)
          ·
            refine ⟨4283242045663960778625431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 182751660614995659888018389 4283242045663960778625431)
            ·
              refine ⟨6424863068495941167938147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4283242045663960778625431 6424863068495941167938147)
              ·
                refine ⟨9637294602743911751907221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6424863068495941167938147 9637294602743911751907221)
                ·
                  refine ⟨451748184503620863370651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9637294602743911751907221 451748184503620863370651)
                  ·
                    rfl

theorem cell21_1979497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_1979497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979497 prefixEnd_1979497 := by exact prefixLift 1979497
  have htrace : WordTrace (prefixWord ++ tailWord_1979497) baseStart_1979497 baseEnd_1979497 := by
    simpa [prefixWord, tailWord_1979497, baseEnd_1979497] using wordTrace_append hprefix tailTrace_1979497
  have hstable : (prefixWord ++ tailWord_1979497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979497).length < 2 ^ (prefixWord ++ tailWord_1979497).sum := by decide
  have hdescent : baseEnd_1979497 < baseStart_1979497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979511 : List Nat := [1, 1, 3, 1, 1, 4, 2, 8]
def baseStart_1979511 : Nat := 118140960795 + 1979511 * 2 ^ 59
def prefixEnd_1979511 : Nat := 4983230072969 + 3 ^ 40 * 1979511 * 2
def baseEnd_1979511 : Nat := 150583793164786650045763

theorem tailTrace_1979511 : CollatzResearch.WordTrace tailWord_1979511 prefixEnd_1979511 150583793164786650045763 := by
  unfold tailWord_1979511
  simp only [CollatzResearch.WordTrace]
  refine ⟨72198697531577195408498387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48132465021051463605665591 72198697531577195408498387)
  ·
    refine ⟨108298046297365793112747581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72198697531577195408498387 108298046297365793112747581)
    ·
      refine ⟨40611767361512172417280343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108298046297365793112747581 40611767361512172417280343)
      ·
        refine ⟨60917651042268258625920515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40611767361512172417280343 60917651042268258625920515)
        ·
          refine ⟨91376476563402387938880773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60917651042268258625920515 91376476563402387938880773)
          ·
            refine ⟨17133089355637947738540145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91376476563402387938880773 17133089355637947738540145)
            ·
              refine ⟨12849817016728460803905109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17133089355637947738540145 12849817016728460803905109)
              ·
                refine ⟨150583793164786650045763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12849817016728460803905109 150583793164786650045763)
                ·
                  rfl

theorem cell21_1979511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 8].length) (baseStart_1979511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979511 prefixEnd_1979511 := by exact prefixLift 1979511
  have htrace : WordTrace (prefixWord ++ tailWord_1979511) baseStart_1979511 baseEnd_1979511 := by
    simpa [prefixWord, tailWord_1979511, baseEnd_1979511] using wordTrace_append hprefix tailTrace_1979511
  have hstable : (prefixWord ++ tailWord_1979511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979511).length < 2 ^ (prefixWord ++ tailWord_1979511).sum := by decide
  have hdescent : baseEnd_1979511 < baseStart_1979511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979565 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 4]
def baseStart_1979565 : Nat := 118140960795 + 1979565 * 2 ^ 59
def prefixEnd_1979565 : Nat := 4983230072969 + 3 ^ 40 * 1979565 * 2
def baseEnd_1979565 : Nat := 451763703030067856237179

theorem tailTrace_1979565 : CollatzResearch.WordTrace tailWord_1979565 prefixEnd_1979565 451763703030067856237179 := by
  unfold tailWord_1979565
  simp only [CollatzResearch.WordTrace]
  refine ⟨72200667073381562630964149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48133778048921041753976099 72200667073381562630964149)
  ·
    refine ⟨6768812538129521496652889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72200667073381562630964149 6768812538129521496652889)
    ·
      refine ⟨5076609403597141122489667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6768812538129521496652889 5076609403597141122489667)
      ·
        refine ⟨7614914105395711683734501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5076609403597141122489667 7614914105395711683734501)
        ·
          refine ⟨1427796394761695940700219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7614914105395711683734501 1427796394761695940700219)
          ·
            refine ⟨2141694592142543911050329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427796394761695940700219 2141694592142543911050329)
            ·
              refine ⟨1606270944106907933287747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2141694592142543911050329 1606270944106907933287747)
              ·
                refine ⟨2409406416160361899931621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606270944106907933287747 2409406416160361899931621)
                ·
                  refine ⟨451763703030067856237179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2409406416160361899931621 451763703030067856237179)
                  ·
                    rfl

theorem cell21_1979565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_1979565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979565 prefixEnd_1979565 := by exact prefixLift 1979565
  have htrace : WordTrace (prefixWord ++ tailWord_1979565) baseStart_1979565 baseEnd_1979565 := by
    simpa [prefixWord, tailWord_1979565, baseEnd_1979565] using wordTrace_append hprefix tailTrace_1979565
  have hstable : (prefixWord ++ tailWord_1979565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979565).length < 2 ^ (prefixWord ++ tailWord_1979565).sum := by decide
  have hdescent : baseEnd_1979565 < baseStart_1979565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979604 : List Nat := [2, 4, 1, 4, 10]
def baseStart_1979604 : Nat := 118140960795 + 1979604 * 2 ^ 59
def prefixEnd_1979604 : Nat := 4983230072969 + 3 ^ 40 * 1979604 * 2
def baseEnd_1979604 : Nat := 5577439547671758704779

theorem tailTrace_1979604 : CollatzResearch.WordTrace tailWord_1979604 prefixEnd_1979604 5577439547671758704779 := by
  unfold tailWord_1979604
  simp only [CollatzResearch.WordTrace]
  refine ⟨36101044760120136145816933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48134726346826848194422577 36101044760120136145816933)
  ·
    refine ⟨6768945892522525527340675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36101044760120136145816933 6768945892522525527340675)
    ·
      refine ⟨10153418838783788291011013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6768945892522525527340675 10153418838783788291011013)
      ·
        refine ⟨1903766032271960304564565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10153418838783788291011013 1903766032271960304564565)
        ·
          refine ⟨5577439547671758704779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1903766032271960304564565 5577439547671758704779)
          ·
            rfl

theorem cell21_1979604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 10].length) (baseStart_1979604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979604 prefixEnd_1979604 := by exact prefixLift 1979604
  have htrace : WordTrace (prefixWord ++ tailWord_1979604) baseStart_1979604 baseEnd_1979604 := by
    simpa [prefixWord, tailWord_1979604, baseEnd_1979604] using wordTrace_append hprefix tailTrace_1979604
  have hstable : (prefixWord ++ tailWord_1979604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979604).length < 2 ^ (prefixWord ++ tailWord_1979604).sum := by decide
  have hdescent : baseEnd_1979604 < baseStart_1979604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979621 : List Nat := [1, 3, 1, 4, 3, 2, 1, 6]
def baseStart_1979621 : Nat := 118140960795 + 1979621 * 2 ^ 59
def prefixEnd_1979621 : Nat := 4983230072969 + 3 ^ 40 * 1979621 * 2
def baseEnd_1979621 : Nat := 150592160997674734434577

theorem tailTrace_1979621 : CollatzResearch.WordTrace tailWord_1979621 prefixEnd_1979621 150592160997674734434577 := by
  unfold tailWord_1979621
  simp only [CollatzResearch.WordTrace]
  refine ⟨72202709561178684195002717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48135139707452456130001811 72202709561178684195002717)
  ·
    refine ⟨27076016085442006573126019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72202709561178684195002717 27076016085442006573126019)
    ·
      refine ⟨40614024128163009859689029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27076016085442006573126019 40614024128163009859689029)
      ·
        refine ⟨7615129524030564348691693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40614024128163009859689029 7615129524030564348691693)
        ·
          refine ⟨2855673571511461630759385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7615129524030564348691693 2855673571511461630759385)
          ·
            refine ⟨2141755178633596223069539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2855673571511461630759385 2141755178633596223069539)
            ·
              refine ⟨3212632767950394334604309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141755178633596223069539 3212632767950394334604309)
              ·
                refine ⟨150592160997674734434577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3212632767950394334604309 150592160997674734434577)
                ·
                  rfl

theorem cell21_1979621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 6].length) (baseStart_1979621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979621 prefixEnd_1979621 := by exact prefixLift 1979621
  have htrace : WordTrace (prefixWord ++ tailWord_1979621) baseStart_1979621 baseEnd_1979621 := by
    simpa [prefixWord, tailWord_1979621, baseEnd_1979621] using wordTrace_append hprefix tailTrace_1979621
  have hstable : (prefixWord ++ tailWord_1979621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979621).length < 2 ^ (prefixWord ++ tailWord_1979621).sum := by decide
  have hdescent : baseEnd_1979621 < baseStart_1979621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979632 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_1979632 : Nat := 118140960795 + 1979632 * 2 ^ 59
def prefixEnd_1979632 : Nat := 4983230072969 + 3 ^ 40 * 1979632 * 2
def baseEnd_1979632 : Nat := 451778993342890628620375

theorem tailTrace_1979632 : CollatzResearch.WordTrace tailWord_1979632 prefixEnd_1979632 451778993342890628620375 := by
  unfold tailWord_1979632
  simp only [CollatzResearch.WordTrace]
  refine ⟨36101555382069416536826575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48135407176092555382435433 36101555382069416536826575)
  ·
    refine ⟨54152333073104124805239863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36101555382069416536826575 54152333073104124805239863)
    ·
      refine ⟨81228499609656187207859795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54152333073104124805239863 81228499609656187207859795)
      ·
        refine ⟨121842749414484280811789693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81228499609656187207859795 121842749414484280811789693)
        ·
          refine ⟨45691031030431605304421135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121842749414484280811789693 45691031030431605304421135)
          ·
            refine ⟨68536546545647407956631703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45691031030431605304421135 68536546545647407956631703)
            ·
              refine ⟨102804819818471111934947555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68536546545647407956631703 102804819818471111934947555)
              ·
                refine ⟨154207229727706667902421333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102804819818471111934947555 154207229727706667902421333)
                ·
                  refine ⟨451778993342890628620375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 154207229727706667902421333 451778993342890628620375)
                  ·
                    rfl

theorem cell21_1979632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_1979632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979632 prefixEnd_1979632 := by exact prefixLift 1979632
  have htrace : WordTrace (prefixWord ++ tailWord_1979632) baseStart_1979632 baseEnd_1979632 := by
    simpa [prefixWord, tailWord_1979632, baseEnd_1979632] using wordTrace_append hprefix tailTrace_1979632
  have hstable : (prefixWord ++ tailWord_1979632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979632).length < 2 ^ (prefixWord ++ tailWord_1979632).sum := by decide
  have hdescent : baseEnd_1979632 < baseStart_1979632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979652 : List Nat := [2, 3, 2, 2, 2, 1, 1, 5, 3]
def baseStart_1979652 : Nat := 118140960795 + 1979652 * 2 ^ 59
def prefixEnd_1979652 : Nat := 4983230072969 + 3 ^ 40 * 1979652 * 2
def baseEnd_1979652 : Nat := 451783557615375038287001

theorem tailTrace_1979652 : CollatzResearch.WordTrace tailWord_1979652 prefixEnd_1979652 451783557615375038287001 := by
  unfold tailWord_1979652
  simp only [CollatzResearch.WordTrace]
  refine ⟨36101920112033188244690605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48135893482710917659587473 36101920112033188244690605)
  ·
    refine ⟨13538220042012445591758977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36101920112033188244690605 13538220042012445591758977)
    ·
      refine ⟨10153665031509334193819233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13538220042012445591758977 10153665031509334193819233)
      ·
        refine ⟨7615248773632000645364425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10153665031509334193819233 7615248773632000645364425)
        ·
          refine ⟨5711436580224000484023319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7615248773632000645364425 5711436580224000484023319)
          ·
            refine ⟨8567154870336000726034979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5711436580224000484023319 8567154870336000726034979)
            ·
              refine ⟨12850732305504001089052469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8567154870336000726034979 12850732305504001089052469)
              ·
                refine ⟨1204756153641000102098669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12850732305504001089052469 1204756153641000102098669)
                ·
                  refine ⟨451783557615375038287001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204756153641000102098669 451783557615375038287001)
                  ·
                    rfl

theorem cell21_1979652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_1979652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979652 prefixEnd_1979652 := by exact prefixLift 1979652
  have htrace : WordTrace (prefixWord ++ tailWord_1979652) baseStart_1979652 baseEnd_1979652 := by
    simpa [prefixWord, tailWord_1979652, baseEnd_1979652] using wordTrace_append hprefix tailTrace_1979652
  have hstable : (prefixWord ++ tailWord_1979652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979652).length < 2 ^ (prefixWord ++ tailWord_1979652).sum := by decide
  have hdescent : baseEnd_1979652 < baseStart_1979652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979697 : List Nat := [1, 2, 2, 3, 3, 3, 2, 5]
def baseStart_1979697 : Nat := 118140960795 + 1979697 * 2 ^ 59
def prefixEnd_1979697 : Nat := 4983230072969 + 3 ^ 40 * 1979697 * 2
def baseEnd_1979697 : Nat := 150597942409488320012303

theorem tailTrace_1979697 : CollatzResearch.WordTrace tailWord_1979697 prefixEnd_1979697 150597942409488320012303 := by
  unfold tailWord_1979697
  simp only [CollatzResearch.WordTrace]
  refine ⟨72205481508903349174769345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48136987672602232783179563 72205481508903349174769345)
  ·
    refine ⟨54154111131677511881077009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72205481508903349174769345 54154111131677511881077009)
    ·
      refine ⟨40615583348758133910807757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54154111131677511881077009 40615583348758133910807757)
      ·
        refine ⟨15230843755784300216552909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40615583348758133910807757 15230843755784300216552909)
        ·
          refine ⟨5711566408419112581207341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15230843755784300216552909 5711566408419112581207341)
          ·
            refine ⟨2141837403157167217952753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5711566408419112581207341 2141837403157167217952753)
            ·
              refine ⟨1606378052367875413464565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2141837403157167217952753 1606378052367875413464565)
              ·
                refine ⟨150597942409488320012303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1606378052367875413464565 150597942409488320012303)
                ·
                  rfl

theorem cell21_1979697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 5].length) (baseStart_1979697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979697 prefixEnd_1979697 := by exact prefixLift 1979697
  have htrace : WordTrace (prefixWord ++ tailWord_1979697) baseStart_1979697 baseEnd_1979697 := by
    simpa [prefixWord, tailWord_1979697, baseEnd_1979697] using wordTrace_append hprefix tailTrace_1979697
  have hstable : (prefixWord ++ tailWord_1979697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979697).length < 2 ^ (prefixWord ++ tailWord_1979697).sum := by decide
  have hdescent : baseEnd_1979697 < baseStart_1979697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979728 : List Nat := [2, 1, 1, 1, 1, 5, 5, 2, 3]
def baseStart_1979728 : Nat := 118140960795 + 1979728 * 2 ^ 59
def prefixEnd_1979728 : Nat := 4983230072969 + 3 ^ 40 * 1979728 * 2
def baseEnd_1979728 : Nat := 451800901850815795020179

theorem tailTrace_1979728 : CollatzResearch.WordTrace tailWord_1979728 prefixEnd_1979728 451800901850815795020179 := by
  unfold tailWord_1979728
  simp only [CollatzResearch.WordTrace]
  refine ⟨36103306085895520734573919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48137741447860694312765225 36103306085895520734573919)
  ·
    refine ⟨54154959128843281101860879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36103306085895520734573919 54154959128843281101860879)
    ·
      refine ⟨81232438693264921652791319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54154959128843281101860879 81232438693264921652791319)
      ·
        refine ⟨121848658039897382479186979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81232438693264921652791319 121848658039897382479186979)
        ·
          refine ⟨182772987059846073718780469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121848658039897382479186979 182772987059846073718780469)
          ·
            refine ⟨17134967536860569411135669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182772987059846073718780469 17134967536860569411135669)
            ·
              refine ⟨1606403206580678382293969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17134967536860569411135669 1606403206580678382293969)
              ·
                refine ⟨1204802404935508786720477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1606403206580678382293969 1204802404935508786720477)
                ·
                  refine ⟨451800901850815795020179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204802404935508786720477 451800901850815795020179)
                  ·
                    rfl

theorem cell21_1979728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 3].length) (baseStart_1979728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979728 prefixEnd_1979728 := by exact prefixLift 1979728
  have htrace : WordTrace (prefixWord ++ tailWord_1979728) baseStart_1979728 baseEnd_1979728 := by
    simpa [prefixWord, tailWord_1979728, baseEnd_1979728] using wordTrace_append hprefix tailTrace_1979728
  have hstable : (prefixWord ++ tailWord_1979728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979728).length < 2 ^ (prefixWord ++ tailWord_1979728).sum := by decide
  have hdescent : baseEnd_1979728 < baseStart_1979728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979787 : List Nat := [1, 1, 1, 1, 4, 3, 3, 4, 3]
def baseStart_1979787 : Nat := 118140960795 + 1979787 * 2 ^ 59
def prefixEnd_1979787 : Nat := 4983230072969 + 3 ^ 40 * 1979787 * 2
def baseEnd_1979787 : Nat := 451814366454644803536725

theorem tailTrace_1979787 : CollatzResearch.WordTrace tailWord_1979787 prefixEnd_1979787 451814366454644803536725 := by
  unfold tailWord_1979787
  simp only [CollatzResearch.WordTrace]
  refine ⟨72208764078577294545545615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48139176052384863030363743 72208764078577294545545615)
  ·
    refine ⟨108313146117865941818318423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72208764078577294545545615 108313146117865941818318423)
    ·
      refine ⟨162469719176798912727477635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108313146117865941818318423 162469719176798912727477635)
      ·
        refine ⟨243704578765198369091216453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162469719176798912727477635 243704578765198369091216453)
        ·
          refine ⟨45694608518474694204603085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243704578765198369091216453 45694608518474694204603085)
          ·
            refine ⟨17135478194428010326726157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45694608518474694204603085 17135478194428010326726157)
            ·
              refine ⟨6425804322910503872522309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17135478194428010326726157 6425804322910503872522309)
              ·
                refine ⟨1204838310545719476097933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6425804322910503872522309 1204838310545719476097933)
                ·
                  refine ⟨451814366454644803536725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204838310545719476097933 451814366454644803536725)
                  ·
                    rfl

theorem cell21_1979787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 3].length) (baseStart_1979787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979787 prefixEnd_1979787 := by exact prefixLift 1979787
  have htrace : WordTrace (prefixWord ++ tailWord_1979787) baseStart_1979787 baseEnd_1979787 := by
    simpa [prefixWord, tailWord_1979787, baseEnd_1979787] using wordTrace_append hprefix tailTrace_1979787
  have hstable : (prefixWord ++ tailWord_1979787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979787).length < 2 ^ (prefixWord ++ tailWord_1979787).sum := by decide
  have hdescent : baseEnd_1979787 < baseStart_1979787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979790 : List Nat := [4, 1, 1, 4, 3, 1, 1, 6]
def baseStart_1979790 : Nat := 118140960795 + 1979790 * 2 ^ 59
def prefixEnd_1979790 : Nat := 4983230072969 + 3 ^ 40 * 1979790 * 2
def baseEnd_1979790 : Nat := 150605017031839154995573

theorem tailTrace_1979790 : CollatzResearch.WordTrace tailWord_1979790 prefixEnd_1979790 150605017031839154995573 := by
  unfold tailWord_1979790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9026109187195803257238103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48139248998377617371936549 9026109187195803257238103)
  ·
    refine ⟨13539163780793704885857155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9026109187195803257238103 13539163780793704885857155)
    ·
      refine ⟨20308745671190557328785733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13539163780793704885857155 20308745671190557328785733)
      ·
        refine ⟨3807889813348229499147325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20308745671190557328785733 3807889813348229499147325)
        ·
          refine ⟨1427958680005586062180247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3807889813348229499147325 1427958680005586062180247)
          ·
            refine ⟨2141938020008379093270371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427958680005586062180247 2141938020008379093270371)
            ·
              refine ⟨3212907030012568639905557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141938020008379093270371 3212907030012568639905557)
              ·
                refine ⟨150605017031839154995573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3212907030012568639905557 150605017031839154995573)
                ·
                  rfl

theorem cell21_1979790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_1979790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979790 prefixEnd_1979790 := by exact prefixLift 1979790
  have htrace : WordTrace (prefixWord ++ tailWord_1979790) baseStart_1979790 baseEnd_1979790 := by
    simpa [prefixWord, tailWord_1979790, baseEnd_1979790] using wordTrace_append hprefix tailTrace_1979790
  have hstable : (prefixWord ++ tailWord_1979790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979790).length < 2 ^ (prefixWord ++ tailWord_1979790).sum := by decide
  have hdescent : baseEnd_1979790 < baseStart_1979790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979801 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 4]
def baseStart_1979801 : Nat := 118140960795 + 1979801 * 2 ^ 59
def prefixEnd_1979801 : Nat := 4983230072969 + 3 ^ 40 * 1979801 * 2
def baseEnd_1979801 : Nat := 451817561445383890303363

theorem tailTrace_1979801 : CollatzResearch.WordTrace tailWord_1979801 prefixEnd_1979801 451817561445383890303363 := by
  unfold tailWord_1979801
  simp only [CollatzResearch.WordTrace]
  refine ⟨72209274700526574936555257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48139516467017716624370171 72209274700526574936555257)
  ·
    refine ⟨54156956025394931202416443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72209274700526574936555257 54156956025394931202416443)
    ·
      refine ⟨81235434038092396803624665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54156956025394931202416443 81235434038092396803624665)
      ·
        refine ⟨60926575528569297602718499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81235434038092396803624665 60926575528569297602718499)
        ·
          refine ⟨91389863292853946404077749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60926575528569297602718499 91389863292853946404077749)
          ·
            refine ⟨8567799683705057475382289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91389863292853946404077749 8567799683705057475382289)
            ·
              refine ⟨6425849762778793106536717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8567799683705057475382289 6425849762778793106536717)
              ·
                refine ⟨2409693661042047414951269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6425849762778793106536717 2409693661042047414951269)
                ·
                  refine ⟨451817561445383890303363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2409693661042047414951269 451817561445383890303363)
                  ·
                    rfl

theorem cell21_1979801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_1979801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979801 prefixEnd_1979801 := by exact prefixLift 1979801
  have htrace : WordTrace (prefixWord ++ tailWord_1979801) baseStart_1979801 baseEnd_1979801 := by
    simpa [prefixWord, tailWord_1979801, baseEnd_1979801] using wordTrace_append hprefix tailTrace_1979801
  have hstable : (prefixWord ++ tailWord_1979801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979801).length < 2 ^ (prefixWord ++ tailWord_1979801).sum := by decide
  have hdescent : baseEnd_1979801 < baseStart_1979801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979804 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 5]
def baseStart_1979804 : Nat := 118140960795 + 1979804 * 2 ^ 59
def prefixEnd_1979804 : Nat := 4983230072969 + 3 ^ 40 * 1979804 * 2
def baseEnd_1979804 : Nat := 451818246086256551753357

theorem tailTrace_1979804 : CollatzResearch.WordTrace tailWord_1979804 prefixEnd_1979804 451818246086256551753357 := by
  unfold tailWord_1979804
  simp only [CollatzResearch.WordTrace]
  refine ⟨36104692059757853224457233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48139589413010470965942977 36104692059757853224457233)
  ·
    refine ⟨27078519044818389918342925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36104692059757853224457233 27078519044818389918342925)
    ·
      refine ⟨10154444641806896219378597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27078519044818389918342925 10154444641806896219378597)
      ·
        refine ⟨1903958370338793041133487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10154444641806896219378597 1903958370338793041133487)
        ·
          refine ⟨2855937555508189561700231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903958370338793041133487 2855937555508189561700231)
          ·
            refine ⟨4283906333262284342550347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2855937555508189561700231 4283906333262284342550347)
            ·
              refine ⟨6425859499893426513825521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4283906333262284342550347 6425859499893426513825521)
              ·
                refine ⟨4819394624920069885369141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6425859499893426513825521 4819394624920069885369141)
                ·
                  refine ⟨451818246086256551753357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4819394624920069885369141 451818246086256551753357)
                  ·
                    rfl

theorem cell21_1979804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_1979804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979804 prefixEnd_1979804 := by exact prefixLift 1979804
  have htrace : WordTrace (prefixWord ++ tailWord_1979804) baseStart_1979804 baseEnd_1979804 := by
    simpa [prefixWord, tailWord_1979804, baseEnd_1979804] using wordTrace_append hprefix tailTrace_1979804
  have hstable : (prefixWord ++ tailWord_1979804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979804).length < 2 ^ (prefixWord ++ tailWord_1979804).sum := by decide
  have hdescent : baseEnd_1979804 < baseStart_1979804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979821 : List Nat := [1, 5, 2, 2, 1, 2, 2, 3, 3]
def baseStart_1979821 : Nat := 118140960795 + 1979821 * 2 ^ 59
def prefixEnd_1979821 : Nat := 4983230072969 + 3 ^ 40 * 1979821 * 2
def baseEnd_1979821 : Nat := 451822125717868299969989

theorem tailTrace_1979821 : CollatzResearch.WordTrace tailWord_1979821 prefixEnd_1979821 451822125717868299969989 := by
  unfold tailWord_1979821
  simp only [CollatzResearch.WordTrace]
  refine ⟨72210004160454118352283317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48140002773636078901522211 72210004160454118352283317)
  ·
    refine ⟨6769687890042573595526561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72210004160454118352283317 6769687890042573595526561)
    ·
      refine ⟨5077265917531930196644921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6769687890042573595526561 5077265917531930196644921)
      ·
        refine ⟨3807949438148947647483691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5077265917531930196644921 3807949438148947647483691)
        ·
          refine ⟨5711924157223421471225537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807949438148947647483691 5711924157223421471225537)
          ·
            refine ⟨4283943117917566103419153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5711924157223421471225537 4283943117917566103419153)
            ·
              refine ⟨3212957338438174577564365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4283943117917566103419153 3212957338438174577564365)
              ·
                refine ⟨1204859001914315466586637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3212957338438174577564365 1204859001914315466586637)
                ·
                  refine ⟨451822125717868299969989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204859001914315466586637 451822125717868299969989)
                  ·
                    rfl

theorem cell21_1979821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_1979821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979821 prefixEnd_1979821 := by exact prefixLift 1979821
  have htrace : WordTrace (prefixWord ++ tailWord_1979821) baseStart_1979821 baseEnd_1979821 := by
    simpa [prefixWord, tailWord_1979821, baseEnd_1979821] using wordTrace_append hprefix tailTrace_1979821
  have hstable : (prefixWord ++ tailWord_1979821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979821).length < 2 ^ (prefixWord ++ tailWord_1979821).sum := by decide
  have hdescent : baseEnd_1979821 < baseStart_1979821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979877 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 6]
def baseStart_1979877 : Nat := 118140960795 + 1979877 * 2 ^ 59
def prefixEnd_1979877 : Nat := 4983230072969 + 3 ^ 40 * 1979877 * 2
def baseEnd_1979877 : Nat := 451834905680824647036541

theorem tailTrace_1979877 : CollatzResearch.WordTrace tailWord_1979877 prefixEnd_1979877 451834905680824647036541 := by
  unfold tailWord_1979877
  simp only [CollatzResearch.WordTrace]
  refine ⟨72212046648251239916321885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48141364432167493277547923 72212046648251239916321885)
  ·
    refine ⟨27079517493094214968620707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72212046648251239916321885 27079517493094214968620707)
    ·
      refine ⟨40619276239641322452931061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27079517493094214968620707 40619276239641322452931061)
      ·
        refine ⟨3808057147466373979962287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40619276239641322452931061 3808057147466373979962287)
        ·
          refine ⟨5712085721199560969943431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808057147466373979962287 5712085721199560969943431)
          ·
            refine ⟨8568128581799341454915147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712085721199560969943431 8568128581799341454915147)
            ·
              refine ⟨12852192872699012182372721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568128581799341454915147 12852192872699012182372721)
              ·
                refine ⟨9639144654524259136779541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12852192872699012182372721 9639144654524259136779541)
                ·
                  refine ⟨451834905680824647036541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9639144654524259136779541 451834905680824647036541)
                  ·
                    rfl

theorem cell21_1979877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_1979877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979877 prefixEnd_1979877 := by exact prefixLift 1979877
  have htrace : WordTrace (prefixWord ++ tailWord_1979877) baseStart_1979877 baseEnd_1979877 := by
    simpa [prefixWord, tailWord_1979877, baseEnd_1979877] using wordTrace_append hprefix tailTrace_1979877
  have hstable : (prefixWord ++ tailWord_1979877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979877).length < 2 ^ (prefixWord ++ tailWord_1979877).sum := by decide
  have hdescent : baseEnd_1979877 < baseStart_1979877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979911 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 4]
def baseStart_1979911 : Nat := 118140960795 + 1979911 * 2 ^ 59
def prefixEnd_1979911 : Nat := 4983230072969 + 3 ^ 40 * 1979911 * 2
def baseEnd_1979911 : Nat := 451842664944048143469805

theorem tailTrace_1979911 : CollatzResearch.WordTrace tailWord_1979911 prefixEnd_1979911 451842664944048143469805 := by
  unfold tailWord_1979911
  simp only [CollatzResearch.WordTrace]
  refine ⟨72213286730128063723059587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48142191153418709148706391 72213286730128063723059587)
  ·
    refine ⟨108319930095192095584589381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72213286730128063723059587 108319930095192095584589381)
    ·
      refine ⟨20309986892848517922110509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108319930095192095584589381 20309986892848517922110509)
      ·
        refine ⟨7616245084818194220791441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20309986892848517922110509 7616245084818194220791441)
        ·
          refine ⟨5712183813613645665593581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7616245084818194220791441 5712183813613645665593581)
          ·
            refine ⟨2142068930105117124597593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5712183813613645665593581 2142068930105117124597593)
            ·
              refine ⟨1606551697578837843448195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2142068930105117124597593 1606551697578837843448195)
              ·
                refine ⟨2409827546368256765172293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606551697578837843448195 2409827546368256765172293)
                ·
                  refine ⟨451842664944048143469805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2409827546368256765172293 451842664944048143469805)
                  ·
                    rfl

theorem cell21_1979911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 4].length) (baseStart_1979911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979911 prefixEnd_1979911 := by exact prefixLift 1979911
  have htrace : WordTrace (prefixWord ++ tailWord_1979911) baseStart_1979911 baseEnd_1979911 := by
    simpa [prefixWord, tailWord_1979911, baseEnd_1979911] using wordTrace_append hprefix tailTrace_1979911
  have hstable : (prefixWord ++ tailWord_1979911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979911).length < 2 ^ (prefixWord ++ tailWord_1979911).sum := by decide
  have hdescent : baseEnd_1979911 < baseStart_1979911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979967 : List Nat := [1, 1, 2, 2, 3, 3, 3, 6]
def baseStart_1979967 : Nat := 118140960795 + 1979967 * 2 ^ 59
def prefixEnd_1979967 : Nat := 4983230072969 + 3 ^ 40 * 1979967 * 2
def baseEnd_1979967 : Nat := 150618481635668163512119

theorem tailTrace_1979967 : CollatzResearch.WordTrace tailWord_1979967 prefixEnd_1979967 150618481635668163512119 := by
  unfold tailWord_1979967
  simp only [CollatzResearch.WordTrace]
  refine ⟨72215329217925185287098155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48143552811950123524732103 72215329217925185287098155)
  ·
    refine ⟨108322993826887777930647233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72215329217925185287098155 108322993826887777930647233)
    ·
      refine ⟨81242245370165833447985425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108322993826887777930647233 81242245370165833447985425)
      ·
        refine ⟨60931684027624375085989069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81242245370165833447985425 60931684027624375085989069)
        ·
          refine ⟨22849381510359140657245901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60931684027624375085989069 22849381510359140657245901)
          ·
            refine ⟨8568518066384677746467213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22849381510359140657245901 8568518066384677746467213)
            ·
              refine ⟨3213194274894254154925205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8568518066384677746467213 3213194274894254154925205)
              ·
                refine ⟨150618481635668163512119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3213194274894254154925205 150618481635668163512119)
                ·
                  rfl

theorem cell21_1979967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 6].length) (baseStart_1979967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1979967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1979967 prefixEnd_1979967 := by exact prefixLift 1979967
  have htrace : WordTrace (prefixWord ++ tailWord_1979967) baseStart_1979967 baseEnd_1979967 := by
    simpa [prefixWord, tailWord_1979967, baseEnd_1979967] using wordTrace_append hprefix tailTrace_1979967
  have hstable : (prefixWord ++ tailWord_1979967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979967).length < 2 ^ (prefixWord ++ tailWord_1979967).sum := by decide
  have hdescent : baseEnd_1979967 < baseStart_1979967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980060 : List Nat := [2, 2, 3, 2, 3, 2, 7]
def baseStart_1980060 : Nat := 118140960795 + 1980060 * 2 ^ 59
def prefixEnd_1980060 : Nat := 4983230072969 + 3 ^ 40 * 1980060 * 2
def baseEnd_1980060 : Nat := 50208518752672999498463

theorem tailTrace_1980060 : CollatzResearch.WordTrace tailWord_1980060 prefixEnd_1980060 50208518752672999498463 := by
  unfold tailWord_1980060
  simp only [CollatzResearch.WordTrace]
  refine ⟨36109360603294131085116817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48145814137725508113489089 36109360603294131085116817)
  ·
    refine ⟨27082020452470598313837613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36109360603294131085116817 27082020452470598313837613)
    ·
      refine ⟨10155757669676474367689105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27082020452470598313837613 10155757669676474367689105)
      ·
        refine ⟨7616818252257355775766829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10155757669676474367689105 7616818252257355775766829)
        ·
          refine ⟨2856306844596508415912561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7616818252257355775766829 2856306844596508415912561)
          ·
            refine ⟨2142230133447381311934421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2856306844596508415912561 2142230133447381311934421)
            ·
              refine ⟨50208518752672999498463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2142230133447381311934421 50208518752672999498463)
              ·
                rfl

theorem cell21_1980060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 7].length) (baseStart_1980060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980060 prefixEnd_1980060 := by exact prefixLift 1980060
  have htrace : WordTrace (prefixWord ++ tailWord_1980060) baseStart_1980060 baseEnd_1980060 := by
    simpa [prefixWord, tailWord_1980060, baseEnd_1980060] using wordTrace_append hprefix tailTrace_1980060
  have hstable : (prefixWord ++ tailWord_1980060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980060).length < 2 ^ (prefixWord ++ tailWord_1980060).sum := by decide
  have hdescent : baseEnd_1980060 < baseStart_1980060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980066 : List Nat := [3, 3, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1980066 : Nat := 118140960795 + 1980066 * 2 ^ 59
def prefixEnd_1980066 : Nat := 4983230072969 + 3 ^ 40 * 1980066 * 2
def baseEnd_1980066 : Nat := 451878038055802318386155

theorem tailTrace_1980066 : CollatzResearch.WordTrace tailWord_1980066 prefixEnd_1980066 451878038055802318386155 := by
  unfold tailWord_1980066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18054735011141631298738013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48145960029711016796634701 18054735011141631298738013)
  ·
    refine ⟨6770525629178111737026755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18054735011141631298738013 6770525629178111737026755)
    ·
      refine ⟨10155788443767167605540133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6770525629178111737026755 10155788443767167605540133)
      ·
        refine ⟨1904210333206343926038775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10155788443767167605540133 1904210333206343926038775)
        ·
          refine ⟨2856315499809515889058163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904210333206343926038775 2856315499809515889058163)
          ·
            refine ⟨4284473249714273833587245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856315499809515889058163 4284473249714273833587245)
            ·
              refine ⟨1606677468642852687595217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4284473249714273833587245 1606677468642852687595217)
              ·
                refine ⟨1205008101482139515696413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1606677468642852687595217 1205008101482139515696413)
                ·
                  refine ⟨451878038055802318386155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205008101482139515696413 451878038055802318386155)
                  ·
                    rfl

theorem cell21_1980066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1980066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980066 prefixEnd_1980066 := by exact prefixLift 1980066
  have htrace : WordTrace (prefixWord ++ tailWord_1980066) baseStart_1980066 baseEnd_1980066 := by
    simpa [prefixWord, tailWord_1980066, baseEnd_1980066] using wordTrace_append hprefix tailTrace_1980066
  have hstable : (prefixWord ++ tailWord_1980066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980066).length < 2 ^ (prefixWord ++ tailWord_1980066).sum := by decide
  have hdescent : baseEnd_1980066 < baseStart_1980066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980125 : List Nat := [1, 4, 3, 3, 1, 1, 1, 4, 3]
def baseStart_1980125 : Nat := 118140960795 + 1980125 * 2 ^ 59
def prefixEnd_1980125 : Nat := 4983230072969 + 3 ^ 40 * 1980125 * 2
def baseEnd_1980125 : Nat := 451891502659631326902701

theorem tailTrace_1980125 : CollatzResearch.WordTrace tailWord_1980125 prefixEnd_1980125 451891502659631326902701 := by
  unfold tailWord_1980125
  simp only [CollatzResearch.WordTrace]
  refine ⟨72221091951352778271349829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48147394634235185514233219 72221091951352778271349829)
  ·
    refine ⟨13541454740878645925878093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72221091951352778271349829 13541454740878645925878093)
    ·
      refine ⟨5078045527829492222204285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13541454740878645925878093 5078045527829492222204285)
      ·
        refine ⟨1904267072936059583326607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5078045527829492222204285 1904267072936059583326607)
        ·
          refine ⟨2856400609404089374989911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904267072936059583326607 2856400609404089374989911)
          ·
            refine ⟨4284600914106134062484867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856400609404089374989911 4284600914106134062484867)
            ·
              refine ⟨6426901371159201093727301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284600914106134062484867 6426901371159201093727301)
              ·
                refine ⟨1205044007092350205073869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6426901371159201093727301 1205044007092350205073869)
                ·
                  refine ⟨451891502659631326902701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205044007092350205073869 451891502659631326902701)
                  ·
                    rfl

theorem cell21_1980125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_1980125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980125 prefixEnd_1980125 := by exact prefixLift 1980125
  have htrace : WordTrace (prefixWord ++ tailWord_1980125) baseStart_1980125 baseEnd_1980125 := by
    simpa [prefixWord, tailWord_1980125, baseEnd_1980125] using wordTrace_append hprefix tailTrace_1980125
  have hstable : (prefixWord ++ tailWord_1980125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980125).length < 2 ^ (prefixWord ++ tailWord_1980125).sum := by decide
  have hdescent : baseEnd_1980125 < baseStart_1980125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980136 : List Nat := [2, 1, 4, 1, 3, 3, 1, 6]
def baseStart_1980136 : Nat := 118140960795 + 1980136 * 2 ^ 59
def prefixEnd_1980136 : Nat := 4983230072969 + 3 ^ 40 * 1980136 * 2
def baseEnd_1980136 : Nat := 150631337669832584073115

theorem tailTrace_1980136 : CollatzResearch.WordTrace tailWord_1980136 prefixEnd_1980136 150631337669832584073115 := by
  unfold tailWord_1980136
  simp only [CollatzResearch.WordTrace]
  refine ⟨36110746577156463575000131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48147662102875284766666841 36110746577156463575000131)
  ·
    refine ⟨54166119865734695362500197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36110746577156463575000131 54166119865734695362500197)
    ·
      refine ⟨10156147474825255380468787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54166119865734695362500197 10156147474825255380468787)
      ·
        refine ⟨15234221212237883070703181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156147474825255380468787 15234221212237883070703181)
        ·
          refine ⟨5712832954589206151513693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15234221212237883070703181 5712832954589206151513693)
          ·
            refine ⟨2142312357970952306817635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5712832954589206151513693 2142312357970952306817635)
            ·
              refine ⟨3213468536956428460226453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142312357970952306817635 3213468536956428460226453)
              ·
                refine ⟨150631337669832584073115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3213468536956428460226453 150631337669832584073115)
                ·
                  rfl

theorem cell21_1980136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_1980136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980136 prefixEnd_1980136 := by exact prefixLift 1980136
  have htrace : WordTrace (prefixWord ++ tailWord_1980136) baseStart_1980136 baseEnd_1980136 := by
    simpa [prefixWord, tailWord_1980136, baseEnd_1980136] using wordTrace_append hprefix tailTrace_1980136
  have hstable : (prefixWord ++ tailWord_1980136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980136).length < 2 ^ (prefixWord ++ tailWord_1980136).sum := by decide
  have hdescent : baseEnd_1980136 < baseStart_1980136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980150 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1980150 : Nat := 118140960795 + 1980150 * 2 ^ 59
def prefixEnd_1980150 : Nat := 4983230072969 + 3 ^ 40 * 1980150 * 2
def baseEnd_1980150 : Nat := 451897208000236838985983

theorem tailTrace_1980150 : CollatzResearch.WordTrace tailWord_1980150 prefixEnd_1980150 451897208000236838985983 := by
  unfold tailWord_1980150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513875236016387971313119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48148002517508138360673269 4513875236016387971313119)
  ·
    refine ⟨6770812854024581956969679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4513875236016387971313119 6770812854024581956969679)
    ·
      refine ⟨10156219281036872935454519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6770812854024581956969679 10156219281036872935454519)
      ·
        refine ⟨15234328921555309403181779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156219281036872935454519 15234328921555309403181779)
        ·
          refine ⟨22851493382332964104772669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15234328921555309403181779 22851493382332964104772669)
          ·
            refine ⟨8569310018374861539289751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22851493382332964104772669 8569310018374861539289751)
            ·
              refine ⟨12853965027562292308934627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569310018374861539289751 12853965027562292308934627)
              ·
                refine ⟨19280947541343438463401941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12853965027562292308934627 19280947541343438463401941)
                ·
                  refine ⟨451897208000236838985983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19280947541343438463401941 451897208000236838985983)
                  ·
                    rfl

theorem cell21_1980150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1980150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980150 prefixEnd_1980150 := by exact prefixLift 1980150
  have htrace : WordTrace (prefixWord ++ tailWord_1980150) baseStart_1980150 baseEnd_1980150 := by
    simpa [prefixWord, tailWord_1980150, baseEnd_1980150] using wordTrace_append hprefix tailTrace_1980150
  have hstable : (prefixWord ++ tailWord_1980150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980150).length < 2 ^ (prefixWord ++ tailWord_1980150).sum := by decide
  have hdescent : baseEnd_1980150 < baseStart_1980150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980181 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 4]
def baseStart_1980181 : Nat := 118140960795 + 1980181 * 2 ^ 59
def prefixEnd_1980181 : Nat := 4983230072969 + 3 ^ 40 * 1980181 * 2
def baseEnd_1980181 : Nat := 451904282622587673969253

theorem tailTrace_1980181 : CollatzResearch.WordTrace tailWord_1980181 prefixEnd_1980181 451904282622587673969253 := by
  unfold tailWord_1980181
  simp only [CollatzResearch.WordTrace]
  refine ⟨72223134439149899835388397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48148756292766599890258931 72223134439149899835388397)
  ·
    refine ⟨27083675414681212438270649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72223134439149899835388397 27083675414681212438270649)
    ·
      refine ⟨20312756561010909328702987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27083675414681212438270649 20312756561010909328702987)
      ·
        refine ⟨30469134841516363993054481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20312756561010909328702987 30469134841516363993054481)
        ·
          refine ⟨22851851131137272994790861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30469134841516363993054481 22851851131137272994790861)
          ·
            refine ⟨8569444174176477373046573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22851851131137272994790861 8569444174176477373046573)
            ·
              refine ⟨3213541565316179014892465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8569444174176477373046573 3213541565316179014892465)
              ·
                refine ⟨2410156173987134261169349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213541565316179014892465 2410156173987134261169349)
                ·
                  refine ⟨451904282622587673969253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410156173987134261169349 451904282622587673969253)
                  ·
                    rfl

theorem cell21_1980181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_1980181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980181 prefixEnd_1980181 := by exact prefixLift 1980181
  have htrace : WordTrace (prefixWord ++ tailWord_1980181) baseStart_1980181 baseEnd_1980181 := by
    simpa [prefixWord, tailWord_1980181, baseEnd_1980181] using wordTrace_append hprefix tailTrace_1980181
  have hstable : (prefixWord ++ tailWord_1980181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980181).length < 2 ^ (prefixWord ++ tailWord_1980181).sum := by decide
  have hdescent : baseEnd_1980181 < baseStart_1980181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980212 : List Nat := [2, 5, 1, 1, 2, 2, 1, 7]
def baseStart_1980212 : Nat := 118140960795 + 1980212 * 2 ^ 59
def prefixEnd_1980212 : Nat := 4983230072969 + 3 ^ 40 * 1980212 * 2
def baseEnd_1980212 : Nat := 150637119081646169650841

theorem tailTrace_1980212 : CollatzResearch.WordTrace tailWord_1980212 prefixEnd_1980212 150637119081646169650841 := by
  unfold tailWord_1980212
  simp only [CollatzResearch.WordTrace]
  refine ⟨36112132551018796064883445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48149510068025061419844593 36112132551018796064883445)
  ·
    refine ⟨3385512426658012131082823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36112132551018796064883445 3385512426658012131082823)
    ·
      refine ⟨5078268639987018196624235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3385512426658012131082823 5078268639987018196624235)
      ·
        refine ⟨7617402959980527294936353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078268639987018196624235 7617402959980527294936353)
        ·
          refine ⟨5713052219985395471202265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7617402959980527294936353 5713052219985395471202265)
          ·
            refine ⟨4284789164989046603401699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5713052219985395471202265 4284789164989046603401699)
            ·
              refine ⟨6427183747483569905102549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284789164989046603401699 6427183747483569905102549)
              ·
                refine ⟨150637119081646169650841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6427183747483569905102549 150637119081646169650841)
                ·
                  rfl

theorem cell21_1980212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_1980212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980212 prefixEnd_1980212 := by exact prefixLift 1980212
  have htrace : WordTrace (prefixWord ++ tailWord_1980212) baseStart_1980212 baseEnd_1980212 := by
    simpa [prefixWord, tailWord_1980212, baseEnd_1980212] using wordTrace_append hprefix tailTrace_1980212
  have hstable : (prefixWord ++ tailWord_1980212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980212).length < 2 ^ (prefixWord ++ tailWord_1980212).sum := by decide
  have hdescent : baseEnd_1980212 < baseStart_1980212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980240 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 4]
def baseStart_1980240 : Nat := 118140960795 + 1980240 * 2 ^ 59
def prefixEnd_1980240 : Nat := 4983230072969 + 3 ^ 40 * 1980240 * 2
def baseEnd_1980240 : Nat := 451917747226416682485799

theorem tailTrace_1980240 : CollatzResearch.WordTrace tailWord_1980240 prefixEnd_1980240 451917747226416682485799 := by
  unfold tailWord_1980240
  simp only [CollatzResearch.WordTrace]
  refine ⟨36112643172968076455893087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48150190897290768607857449 36112643172968076455893087)
  ·
    refine ⟨54168964759452114683839631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36112643172968076455893087 54168964759452114683839631)
    ·
      refine ⟨81253447139178172025759447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54168964759452114683839631 81253447139178172025759447)
      ·
        refine ⟨121880170708767258038639171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81253447139178172025759447 121880170708767258038639171)
        ·
          refine ⟨182820256063150887057958757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121880170708767258038639171 182820256063150887057958757)
          ·
            refine ⟨34278798011840791323367267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182820256063150887057958757 34278798011840791323367267)
            ·
              refine ⟨51418197017761186985050901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34278798011840791323367267 51418197017761186985050901)
              ·
                refine ⟨2410227985207555639924261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51418197017761186985050901 2410227985207555639924261)
                ·
                  refine ⟨451917747226416682485799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410227985207555639924261 451917747226416682485799)
                  ·
                    rfl

theorem cell21_1980240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_1980240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980240 prefixEnd_1980240 := by exact prefixLift 1980240
  have htrace : WordTrace (prefixWord ++ tailWord_1980240) baseStart_1980240 baseEnd_1980240 := by
    simpa [prefixWord, tailWord_1980240, baseEnd_1980240] using wordTrace_append hprefix tailTrace_1980240
  have hstable : (prefixWord ++ tailWord_1980240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980240).length < 2 ^ (prefixWord ++ tailWord_1980240).sum := by decide
  have hdescent : baseEnd_1980240 < baseStart_1980240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980350 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1980350 : Nat := 118140960795 + 1980350 * 2 ^ 59
def prefixEnd_1980350 : Nat := 4983230072969 + 3 ^ 40 * 1980350 * 2
def baseEnd_1980350 : Nat := 451942850725080935652241

theorem tailTrace_1980350 : CollatzResearch.WordTrace tailWord_1980350 prefixEnd_1980350 451942850725080935652241 := by
  unfold tailWord_1980350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9028662296942205212286313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48152865583691761132193669 9028662296942205212286313)
  ·
    refine ⟨6771496722706653909214735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9028662296942205212286313 6771496722706653909214735)
    ·
      refine ⟨10157245084059980863822103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6771496722706653909214735 10157245084059980863822103)
      ·
        refine ⟨15235867626089971295733155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10157245084059980863822103 15235867626089971295733155)
        ·
          refine ⟨22853801439134956943599733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15235867626089971295733155 22853801439134956943599733)
          ·
            refine ⟨2142543884918902213462475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22853801439134956943599733 2142543884918902213462475)
            ·
              refine ⟨3213815827378353320193713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142543884918902213462475 3213815827378353320193713)
              ·
                refine ⟨2410361870533764990145285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213815827378353320193713 2410361870533764990145285)
                ·
                  refine ⟨451942850725080935652241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410361870533764990145285 451942850725080935652241)
                  ·
                    rfl

theorem cell21_1980350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1980350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980350 prefixEnd_1980350 := by exact prefixLift 1980350
  have htrace : WordTrace (prefixWord ++ tailWord_1980350) baseStart_1980350 baseEnd_1980350 := by
    simpa [prefixWord, tailWord_1980350, baseEnd_1980350] using wordTrace_append hprefix tailTrace_1980350
  have hstable : (prefixWord ++ tailWord_1980350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980350).length < 2 ^ (prefixWord ++ tailWord_1980350).sum := by decide
  have hdescent : baseEnd_1980350 < baseStart_1980350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980381 : List Nat := [1, 4, 3, 1, 3, 2, 2, 5]
def baseStart_1980381 : Nat := 118140960795 + 1980381 * 2 ^ 59
def prefixEnd_1980381 : Nat := 4983230072969 + 3 ^ 40 * 1980381 * 2
def baseEnd_1980381 : Nat := 150649975115810590211837

theorem tailTrace_1980381 : CollatzResearch.WordTrace tailWord_1980381 prefixEnd_1980381 150649975115810590211837 := by
  unfold tailWord_1980381
  simp only [CollatzResearch.WordTrace]
  refine ⟨72230429038425333992668997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48153619358950222661779331 72230429038425333992668997)
  ·
    refine ⟨13543205444704750123625437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72230429038425333992668997 13543205444704750123625437)
    ·
      refine ⟨5078702041764281296359539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13543205444704750123625437 5078702041764281296359539)
      ·
        refine ⟨7618053062646421944539309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078702041764281296359539 7618053062646421944539309)
        ·
          refine ⟨2856769898492408229202241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7618053062646421944539309 2856769898492408229202241)
          ·
            refine ⟨2142577423869306171901681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2856769898492408229202241 2142577423869306171901681)
            ·
              refine ⟨1606933067901979628926261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2142577423869306171901681 1606933067901979628926261)
              ·
                refine ⟨150649975115810590211837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1606933067901979628926261 150649975115810590211837)
                ·
                  rfl

theorem cell21_1980381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 5].length) (baseStart_1980381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980381 prefixEnd_1980381 := by exact prefixLift 1980381
  have htrace : WordTrace (prefixWord ++ tailWord_1980381) baseStart_1980381 baseEnd_1980381 := by
    simpa [prefixWord, tailWord_1980381, baseEnd_1980381] using wordTrace_append hprefix tailTrace_1980381
  have hstable : (prefixWord ++ tailWord_1980381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980381).length < 2 ^ (prefixWord ++ tailWord_1980381).sum := by decide
  have hdescent : baseEnd_1980381 < baseStart_1980381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980423 : List Nat := [1, 1, 4, 3, 1, 3, 2, 6]
def baseStart_1980423 : Nat := 118140960795 + 1980423 * 2 ^ 59
def prefixEnd_1980423 : Nat := 4983230072969 + 3 ^ 40 * 1980423 * 2
def baseEnd_1980423 : Nat := 150653170106549676978475

theorem tailTrace_1980423 : CollatzResearch.WordTrace tailWord_1980423 prefixEnd_1980423 150653170106549676978475 := by
  unfold tailWord_1980423
  simp only [CollatzResearch.WordTrace]
  refine ⟨72231960904273175165697923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48154640602848783443798615 72231960904273175165697923)
  ·
    refine ⟨108347941356409762748546885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72231960904273175165697923 108347941356409762748546885)
    ·
      refine ⟨20315239004326830515352541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108347941356409762748546885 20315239004326830515352541)
      ·
        refine ⟨7618214626622561443257203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20315239004326830515352541 7618214626622561443257203)
        ·
          refine ⟨11427321939933842164885805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7618214626622561443257203 11427321939933842164885805)
          ·
            refine ⟨4285245727475190811832177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11427321939933842164885805 4285245727475190811832177)
            ·
              refine ⟨3213934295606393108874133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4285245727475190811832177 3213934295606393108874133)
              ·
                refine ⟨150653170106549676978475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3213934295606393108874133 150653170106549676978475)
                ·
                  rfl

theorem cell21_1980423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 6].length) (baseStart_1980423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980423 prefixEnd_1980423 := by exact prefixLift 1980423
  have htrace : WordTrace (prefixWord ++ tailWord_1980423) baseStart_1980423 baseEnd_1980423 := by
    simpa [prefixWord, tailWord_1980423, baseEnd_1980423] using wordTrace_append hprefix tailTrace_1980423
  have hstable : (prefixWord ++ tailWord_1980423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980423).length < 2 ^ (prefixWord ++ tailWord_1980423).sum := by decide
  have hdescent : baseEnd_1980423 < baseStart_1980423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980471 : List Nat := [1, 1, 3, 1, 2, 2, 6, 2, 3]
def baseStart_1980471 : Nat := 118140960795 + 1980471 * 2 ^ 59
def prefixEnd_1980471 : Nat := 4983230072969 + 3 ^ 40 * 1980471 * 2
def baseEnd_1980471 : Nat := 451970464573611614135327

theorem tailTrace_1980471 : CollatzResearch.WordTrace tailWord_1980471 prefixEnd_1980471 451970464573611614135327 := by
  unfold tailWord_1980471
  simp only [CollatzResearch.WordTrace]
  refine ⟨72233711608099279363445267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48155807738732852908963511 72233711608099279363445267)
  ·
    refine ⟨108350567412148919045167901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72233711608099279363445267 108350567412148919045167901)
    ·
      refine ⟨40631462779555844641937963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108350567412148919045167901 40631462779555844641937963)
      ·
        refine ⟨60947194169333766962906945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40631462779555844641937963 60947194169333766962906945)
        ·
          refine ⟨45710395627000325222180209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60947194169333766962906945 45710395627000325222180209)
          ·
            refine ⟨34282796720250243916635157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45710395627000325222180209 34282796720250243916635157)
            ·
              refine ⟨1607006096261730183592273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34282796720250243916635157 1607006096261730183592273)
              ·
                refine ⟨1205254572196297637694205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607006096261730183592273 1205254572196297637694205)
                ·
                  refine ⟨451970464573611614135327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205254572196297637694205 451970464573611614135327)
                  ·
                    rfl

theorem cell21_1980471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 3].length) (baseStart_1980471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980471 prefixEnd_1980471 := by exact prefixLift 1980471
  have htrace : WordTrace (prefixWord ++ tailWord_1980471) baseStart_1980471 baseEnd_1980471 := by
    simpa [prefixWord, tailWord_1980471, baseEnd_1980471] using wordTrace_append hprefix tailTrace_1980471
  have hstable : (prefixWord ++ tailWord_1980471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980471).length < 2 ^ (prefixWord ++ tailWord_1980471).sum := by decide
  have hdescent : baseEnd_1980471 < baseStart_1980471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980530 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_1980530 : Nat := 118140960795 + 1980530 * 2 ^ 59
def prefixEnd_1980530 : Nat := 4983230072969 + 3 ^ 40 * 1980530 * 2
def baseEnd_1980530 : Nat := 451983929177440622651873

theorem tailTrace_1980530 : CollatzResearch.WordTrace tailWord_1980530 prefixEnd_1980530 451983929177440622651873 := by
  unfold tailWord_1980530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18058965878721383109960761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48157242343257021626562029 18058965878721383109960761)
  ·
    refine ⟨13544224409041037332470571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18058965878721383109960761 13544224409041037332470571)
    ·
      refine ⟨20316336613561555998705857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13544224409041037332470571 20316336613561555998705857)
      ·
        refine ⟨15237252460171166999029393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20316336613561555998705857 15237252460171166999029393)
        ·
          refine ⟨11427939345128375249272045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15237252460171166999029393 11427939345128375249272045)
          ·
            refine ⟨4285477254423140718477017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11427939345128375249272045 4285477254423140718477017)
            ·
              refine ⟨3214107940817355538857763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4285477254423140718477017 3214107940817355538857763)
              ·
                refine ⟨4821161911226033308286645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3214107940817355538857763 4821161911226033308286645)
                ·
                  refine ⟨451983929177440622651873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4821161911226033308286645 451983929177440622651873)
                  ·
                    rfl

theorem cell21_1980530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_1980530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980530 prefixEnd_1980530 := by exact prefixLift 1980530
  have htrace : WordTrace (prefixWord ++ tailWord_1980530) baseStart_1980530 baseEnd_1980530 := by
    simpa [prefixWord, tailWord_1980530, baseEnd_1980530] using wordTrace_append hprefix tailTrace_1980530
  have hstable : (prefixWord ++ tailWord_1980530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980530).length < 2 ^ (prefixWord ++ tailWord_1980530).sum := by decide
  have hdescent : baseEnd_1980530 < baseStart_1980530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980575 : List Nat := [1, 1, 2, 6, 1, 3, 7]
def baseStart_1980575 : Nat := 118140960795 + 1980575 * 2 ^ 59
def prefixEnd_1980575 : Nat := 4983230072969 + 3 ^ 40 * 1980575 * 2
def baseEnd_1980575 : Nat := 50221577643392282711309

theorem tailTrace_1980575 : CollatzResearch.WordTrace tailWord_1980575 prefixEnd_1980575 50221577643392282711309 := by
  unfold tailWord_1980575
  simp only [CollatzResearch.WordTrace]
  refine ⟨72237504799722505125231179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48158336533148336750154119 72237504799722505125231179)
  ·
    refine ⟨108356257199583757687846769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72237504799722505125231179 108356257199583757687846769)
    ·
      refine ⟨81267192899687818265885077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108356257199583757687846769 81267192899687818265885077)
      ·
        refine ⟨3809399667172866481213363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81267192899687818265885077 3809399667172866481213363)
        ·
          refine ⟨5714099500759299721820045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3809399667172866481213363 5714099500759299721820045)
          ·
            refine ⟨2142787312784737395682517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5714099500759299721820045 2142787312784737395682517)
            ·
              refine ⟨50221577643392282711309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2142787312784737395682517 50221577643392282711309)
              ·
                rfl

theorem cell21_1980575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 7].length) (baseStart_1980575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980575 prefixEnd_1980575 := by exact prefixLift 1980575
  have htrace : WordTrace (prefixWord ++ tailWord_1980575) baseStart_1980575 baseEnd_1980575 := by
    simpa [prefixWord, tailWord_1980575, baseEnd_1980575] using wordTrace_append hprefix tailTrace_1980575
  have hstable : (prefixWord ++ tailWord_1980575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980575).length < 2 ^ (prefixWord ++ tailWord_1980575).sum := by decide
  have hdescent : baseEnd_1980575 < baseStart_1980575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980637 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 4]
def baseStart_1980637 : Nat := 118140960795 + 1980637 * 2 ^ 59
def prefixEnd_1980637 : Nat := 4983230072969 + 3 ^ 40 * 1980637 * 2
def baseEnd_1980637 : Nat := 452008348035232214368321

theorem tailTrace_1980637 : CollatzResearch.WordTrace tailWord_1980637 prefixEnd_1980637 452008348035232214368321 := by
  unfold tailWord_1980637
  simp only [CollatzResearch.WordTrace]
  refine ⟨72239766125497889713988165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48159844083665259809325443 72239766125497889713988165)
  ·
    refine ⟨13544956148530854321372781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72239766125497889713988165 13544956148530854321372781)
    ·
      refine ⟨5079358555699070370514793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13544956148530854321372781 5079358555699070370514793)
      ·
        refine ⟨3809518916774302777886095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5079358555699070370514793 3809518916774302777886095)
        ·
          refine ⟨5714278375161454166829143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3809518916774302777886095 5714278375161454166829143)
          ·
            refine ⟨8571417562742181250243715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5714278375161454166829143 8571417562742181250243715)
            ·
              refine ⟨12857126344113271875365573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8571417562742181250243715 12857126344113271875365573)
              ·
                refine ⟨2410711189521238476631045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12857126344113271875365573 2410711189521238476631045)
                ·
                  refine ⟨452008348035232214368321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410711189521238476631045 452008348035232214368321)
                  ·
                    rfl

theorem cell21_1980637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_1980637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980637 prefixEnd_1980637 := by exact prefixLift 1980637
  have htrace : WordTrace (prefixWord ++ tailWord_1980637) baseStart_1980637 baseEnd_1980637 := by
    simpa [prefixWord, tailWord_1980637, baseEnd_1980637] using wordTrace_append hprefix tailTrace_1980637
  have hstable : (prefixWord ++ tailWord_1980637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980637).length < 2 ^ (prefixWord ++ tailWord_1980637).sum := by decide
  have hdescent : baseEnd_1980637 < baseStart_1980637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980682 : List Nat := [3, 1, 2, 2, 1, 1, 3, 5, 3]
def baseStart_1980682 : Nat := 118140960795 + 1980682 * 2 ^ 59
def prefixEnd_1980682 : Nat := 4983230072969 + 3 ^ 40 * 1980682 * 2
def baseEnd_1980682 : Nat := 452018617648322136118229

theorem tailTrace_1980682 : CollatzResearch.WordTrace tailWord_1980682 prefixEnd_1980682 452018617648322136118229 := by
  unfold tailWord_1980682
  simp only [CollatzResearch.WordTrace]
  refine ⟨18060351852583715599844075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48160938273556574932917533 18060351852583715599844075)
  ·
    refine ⟨27090527778875573399766113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18060351852583715599844075 27090527778875573399766113)
    ·
      refine ⟨20317895834156680049824585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27090527778875573399766113 20317895834156680049824585)
      ·
        refine ⟨15238421875617510037368439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20317895834156680049824585 15238421875617510037368439)
        ·
          refine ⟨22857632813426265056052659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15238421875617510037368439 22857632813426265056052659)
          ·
            refine ⟨34286449220139397584078989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22857632813426265056052659 34286449220139397584078989)
            ·
              refine ⟨12857418457552274094029621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34286449220139397584078989 12857418457552274094029621)
              ·
                refine ⟨1205382980395525696315277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12857418457552274094029621 1205382980395525696315277)
                ·
                  refine ⟨452018617648322136118229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205382980395525696315277 452018617648322136118229)
                  ·
                    rfl

theorem cell21_1980682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_1980682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980682 prefixEnd_1980682 := by exact prefixLift 1980682
  have htrace : WordTrace (prefixWord ++ tailWord_1980682) baseStart_1980682 baseEnd_1980682 := by
    simpa [prefixWord, tailWord_1980682, baseEnd_1980682] using wordTrace_append hprefix tailTrace_1980682
  have hstable : (prefixWord ++ tailWord_1980682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980682).length < 2 ^ (prefixWord ++ tailWord_1980682).sum := by decide
  have hdescent : baseEnd_1980682 < baseStart_1980682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980764 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 4]
def baseStart_1980764 : Nat := 118140960795 + 1980764 * 2 ^ 59
def prefixEnd_1980764 : Nat := 4983230072969 + 3 ^ 40 * 1980764 * 2
def baseEnd_1980764 : Nat := 452037331165508215751395

theorem tailTrace_1980764 : CollatzResearch.WordTrace tailWord_1980764 prefixEnd_1980764 452037331165508215751395 := by
  unfold tailWord_1980764
  simp only [CollatzResearch.WordTrace]
  refine ⟨36122199098018895201930673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48162932130691860269240897 36122199098018895201930673)
  ·
    refine ⟨27091649323514171401448005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36122199098018895201930673 27091649323514171401448005)
    ·
      refine ⟨5079684248158907137771501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27091649323514171401448005 5079684248158907137771501)
      ·
        refine ⟨1904881593059590176664313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5079684248158907137771501 1904881593059590176664313)
        ·
          refine ⟨1428661194794692632498235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1904881593059590176664313 1428661194794692632498235)
          ·
            refine ⟨2142991792192038948747353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428661194794692632498235 2142991792192038948747353)
            ·
              refine ⟨1607243844144029211560515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2142991792192038948747353 1607243844144029211560515)
              ·
                refine ⟨2410865766216043817340773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607243844144029211560515 2410865766216043817340773)
                ·
                  refine ⟨452037331165508215751395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410865766216043817340773 452037331165508215751395)
                  ·
                    rfl

theorem cell21_1980764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_1980764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980764 prefixEnd_1980764 := by exact prefixLift 1980764
  have htrace : WordTrace (prefixWord ++ tailWord_1980764) baseStart_1980764 baseEnd_1980764 := by
    simpa [prefixWord, tailWord_1980764, baseEnd_1980764] using wordTrace_append hprefix tailTrace_1980764
  have hstable : (prefixWord ++ tailWord_1980764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980764).length < 2 ^ (prefixWord ++ tailWord_1980764).sum := by decide
  have hdescent : baseEnd_1980764 < baseStart_1980764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980772 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 4]
def baseStart_1980772 : Nat := 118140960795 + 1980772 * 2 ^ 59
def prefixEnd_1980772 : Nat := 4983230072969 + 3 ^ 40 * 1980772 * 2
def baseEnd_1980772 : Nat := 452039156874501979618045

theorem tailTrace_1980772 : CollatzResearch.WordTrace tailWord_1980772 prefixEnd_1980772 452039156874501979618045 := by
  unfold tailWord_1980772
  simp only [CollatzResearch.WordTrace]
  refine ⟨36122344990004403885076285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48163126653339205180101713 36122344990004403885076285)
  ·
    refine ⟨13545879371251651456903607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36122344990004403885076285 13545879371251651456903607)
    ·
      refine ⟨20318819056877477185355411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13545879371251651456903607 20318819056877477185355411)
      ·
        refine ⟨30478228585316215778033117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20318819056877477185355411 30478228585316215778033117)
        ·
          refine ⟨11429335719493580916762419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30478228585316215778033117 11429335719493580916762419)
          ·
            refine ⟨17144003579240371375143629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11429335719493580916762419 17144003579240371375143629)
            ·
              refine ⟨6429001342215139265678861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17144003579240371375143629 6429001342215139265678861)
              ·
                refine ⟨2410875503330677224629573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6429001342215139265678861 2410875503330677224629573)
                ·
                  refine ⟨452039156874501979618045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410875503330677224629573 452039156874501979618045)
                  ·
                    rfl

theorem cell21_1980772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_1980772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980772 prefixEnd_1980772 := by exact prefixLift 1980772
  have htrace : WordTrace (prefixWord ++ tailWord_1980772) baseStart_1980772 baseEnd_1980772 := by
    simpa [prefixWord, tailWord_1980772, baseEnd_1980772] using wordTrace_append hprefix tailTrace_1980772
  have hstable : (prefixWord ++ tailWord_1980772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980772).length < 2 ^ (prefixWord ++ tailWord_1980772).sum := by decide
  have hdescent : baseEnd_1980772 < baseStart_1980772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980786 : List Nat := [3, 2, 1, 2, 1, 3, 2, 7]
def baseStart_1980786 : Nat := 118140960795 + 1980786 * 2 ^ 59
def prefixEnd_1980786 : Nat := 4983230072969 + 3 ^ 40 * 1980786 * 2
def baseEnd_1980786 : Nat := 150680783955080355461561

theorem tailTrace_1980786 : CollatzResearch.WordTrace tailWord_1980786 prefixEnd_1980786 150680783955080355461561 := by
  unfold tailWord_1980786
  simp only [CollatzResearch.WordTrace]
  refine ⟨18061300150489522040290553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48163467067972058774108141 18061300150489522040290553)
  ·
    refine ⟨13545975112867141530217915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18061300150489522040290553 13545975112867141530217915)
    ·
      refine ⟨20318962669300712295326873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13545975112867141530217915 20318962669300712295326873)
      ·
        refine ⟨15239222001975534221495155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20318962669300712295326873 15239222001975534221495155)
        ·
          refine ⟨22858833002963301332242733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15239222001975534221495155 22858833002963301332242733)
          ·
            refine ⟨8572062376111237999591025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22858833002963301332242733 8572062376111237999591025)
            ·
              refine ⟨6429046782083428499693269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8572062376111237999591025 6429046782083428499693269)
              ·
                refine ⟨150680783955080355461561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6429046782083428499693269 150680783955080355461561)
                ·
                  rfl

theorem cell21_1980786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_1980786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980786 prefixEnd_1980786 := by exact prefixLift 1980786
  have htrace : WordTrace (prefixWord ++ tailWord_1980786) baseStart_1980786 baseEnd_1980786 := by
    simpa [prefixWord, tailWord_1980786, baseEnd_1980786] using wordTrace_append hprefix tailTrace_1980786
  have hstable : (prefixWord ++ tailWord_1980786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980786).length < 2 ^ (prefixWord ++ tailWord_1980786).sum := by decide
  have hdescent : baseEnd_1980786 < baseStart_1980786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980820 : List Nat := [2, 4, 2, 1, 3, 2, 1, 6]
def baseStart_1980820 : Nat := 118140960795 + 1980820 * 2 ^ 59
def prefixEnd_1980820 : Nat := 4983230072969 + 3 ^ 40 * 1980820 * 2
def baseEnd_1980820 : Nat := 150683370376154854272649

theorem tailTrace_1980820 : CollatzResearch.WordTrace tailWord_1980820 prefixEnd_1980820 150683370376154854272649 := by
  unfold tailWord_1980820
  simp only [CollatzResearch.WordTrace]
  refine ⟨36123220341917455983949957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48164293789223274645266609 36123220341917455983949957)
  ·
    refine ⟨6773103814109522996990617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36123220341917455983949957 6773103814109522996990617)
    ·
      refine ⟨5079827860582142247742963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6773103814109522996990617 5079827860582142247742963)
      ·
        refine ⟨7619741790873213371614445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5079827860582142247742963 7619741790873213371614445)
        ·
          refine ⟨2857403171577455014355417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7619741790873213371614445 2857403171577455014355417)
          ·
            refine ⟨2143052378683091260766563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2857403171577455014355417 2143052378683091260766563)
            ·
              refine ⟨3214578568024636891149845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143052378683091260766563 3214578568024636891149845)
              ·
                refine ⟨150683370376154854272649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3214578568024636891149845 150683370376154854272649)
                ·
                  rfl

theorem cell21_1980820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_1980820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980820 prefixEnd_1980820 := by exact prefixLift 1980820
  have htrace : WordTrace (prefixWord ++ tailWord_1980820) baseStart_1980820 baseEnd_1980820 := by
    simpa [prefixWord, tailWord_1980820, baseEnd_1980820] using wordTrace_append hprefix tailTrace_1980820
  have hstable : (prefixWord ++ tailWord_1980820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980820).length < 2 ^ (prefixWord ++ tailWord_1980820).sum := by decide
  have hdescent : baseEnd_1980820 < baseStart_1980820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980893 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1980893 : Nat := 118140960795 + 1980893 * 2 ^ 59
def prefixEnd_1980893 : Nat := 4983230072969 + 3 ^ 40 * 1980893 * 2
def baseEnd_1980893 : Nat := 452066770723032658101131

theorem tailTrace_1980893 : CollatzResearch.WordTrace tailWord_1980893 prefixEnd_1980893 452066770723032658101131 := by
  unfold tailWord_1980893
  simp only [CollatzResearch.WordTrace]
  refine ⟨72249103212570445435307333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48166068808380296956871555 72249103212570445435307333)
  ·
    refine ⟨13546706852356958519120125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72249103212570445435307333 13546706852356958519120125)
    ·
      refine ⟨5080015069633859444670047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13546706852356958519120125 5080015069633859444670047)
      ·
        refine ⟨7620022604450789167005071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5080015069633859444670047 7620022604450789167005071)
        ·
          refine ⟨11430033906676183750507607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7620022604450789167005071 11430033906676183750507607)
          ·
            refine ⟨17145050860014275625761411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11430033906676183750507607 17145050860014275625761411)
            ·
              refine ⟨25717576290021413438642117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17145050860014275625761411 25717576290021413438642117)
              ·
                refine ⟨4822045554379015019745397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25717576290021413438642117 4822045554379015019745397)
                ·
                  refine ⟨452066770723032658101131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4822045554379015019745397 452066770723032658101131)
                  ·
                    rfl

theorem cell21_1980893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1980893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980893 prefixEnd_1980893 := by exact prefixLift 1980893
  have htrace : WordTrace (prefixWord ++ tailWord_1980893) baseStart_1980893 baseEnd_1980893 := by
    simpa [prefixWord, tailWord_1980893, baseEnd_1980893] using wordTrace_append hprefix tailTrace_1980893
  have hstable : (prefixWord ++ tailWord_1980893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980893).length < 2 ^ (prefixWord ++ tailWord_1980893).sum := by decide
  have hdescent : baseEnd_1980893 < baseStart_1980893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980921 : List Nat := [1, 2, 1, 3, 1, 2, 11]
def baseStart_1980921 : Nat := 118140960795 + 1980921 * 2 ^ 59
def prefixEnd_1980921 : Nat := 4983230072969 + 3 ^ 40 * 1980921 * 2
def baseEnd_1980921 : Nat := 50230351189390092403823

theorem tailTrace_1980921 : CollatzResearch.WordTrace tailWord_1980921 prefixEnd_1980921 50230351189390092403823 := by
  unfold tailWord_1980921
  simp only [CollatzResearch.WordTrace]
  refine ⟨72250124456469006217326617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48166749637646004144884411 72250124456469006217326617)
  ·
    refine ⟨54187593342351754662994963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72250124456469006217326617 54187593342351754662994963)
    ·
      refine ⟨81281390013527631994492445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54187593342351754662994963 81281390013527631994492445)
      ·
        refine ⟨30480521255072861997934667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81281390013527631994492445 30480521255072861997934667)
        ·
          refine ⟨45720781882609292996902001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30480521255072861997934667 45720781882609292996902001)
          ·
            refine ⟨34290586411956969747676501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45720781882609292996902001 34290586411956969747676501)
            ·
              refine ⟨50230351189390092403823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34290586411956969747676501 50230351189390092403823)
              ·
                rfl

theorem cell21_1980921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 11].length) (baseStart_1980921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980921 prefixEnd_1980921 := by exact prefixLift 1980921
  have htrace : WordTrace (prefixWord ++ tailWord_1980921) baseStart_1980921 baseEnd_1980921 := by
    simpa [prefixWord, tailWord_1980921, baseEnd_1980921] using wordTrace_append hprefix tailTrace_1980921
  have hstable : (prefixWord ++ tailWord_1980921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980921).length < 2 ^ (prefixWord ++ tailWord_1980921).sum := by decide
  have hdescent : baseEnd_1980921 < baseStart_1980921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980938 : List Nat := [3, 1, 2, 2, 2, 1, 4, 6]
def baseStart_1980938 : Nat := 118140960795 + 1980938 * 2 ^ 59
def prefixEnd_1980938 : Nat := 4983230072969 + 3 ^ 40 * 1980938 * 2
def baseEnd_1980938 : Nat := 150692346778707526617013

theorem tailTrace_1980938 : CollatzResearch.WordTrace tailWord_1980938 prefixEnd_1980938 150692346778707526617013 := by
  unfold tailWord_1980938
  simp only [CollatzResearch.WordTrace]
  refine ⟨18062686124351854530173867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48167162998271612080463645 18062686124351854530173867)
  ·
    refine ⟨27094029186527781795260801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18062686124351854530173867 27094029186527781795260801)
    ·
      refine ⟨20320521889895836346445601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27094029186527781795260801 20320521889895836346445601)
      ·
        refine ⟨15240391417421877259834201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20320521889895836346445601 15240391417421877259834201)
        ·
          refine ⟨11430293563066407944875651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15240391417421877259834201 11430293563066407944875651)
          ·
            refine ⟨17145440344599611917313477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11430293563066407944875651 17145440344599611917313477)
            ·
              refine ⟨3214770064612427234496277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17145440344599611917313477 3214770064612427234496277)
              ·
                refine ⟨150692346778707526617013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3214770064612427234496277 150692346778707526617013)
                ·
                  rfl

theorem cell21_1980938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_1980938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980938 prefixEnd_1980938 := by exact prefixLift 1980938
  have htrace : WordTrace (prefixWord ++ tailWord_1980938) baseStart_1980938 baseEnd_1980938 := by
    simpa [prefixWord, tailWord_1980938, baseEnd_1980938] using wordTrace_append hprefix tailTrace_1980938
  have hstable : (prefixWord ++ tailWord_1980938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980938).length < 2 ^ (prefixWord ++ tailWord_1980938).sum := by decide
  have hdescent : baseEnd_1980938 < baseStart_1980938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980986 : List Nat := [3, 1, 1, 1, 3, 4, 1, 4, 3]
def baseStart_1980986 : Nat := 118140960795 + 1980986 * 2 ^ 59
def prefixEnd_1980986 : Nat := 4983230072969 + 3 ^ 40 * 1980986 * 2
def baseEnd_1980986 : Nat := 452087994590085163050941

theorem tailTrace_1980986 : CollatzResearch.WordTrace tailWord_1980986 prefixEnd_1980986 452087994590085163050941 := by
  unfold tailWord_1980986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18063123800308380579610703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48168330134155681545628541 18063123800308380579610703)
  ·
    refine ⟨27094685700462570869416055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18063123800308380579610703 27094685700462570869416055)
    ·
      refine ⟨40642028550693856304124083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27094685700462570869416055 40642028550693856304124083)
      ·
        refine ⟨60963042826040784456186125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40642028550693856304124083 60963042826040784456186125)
        ·
          refine ⟨22861141059765294171069797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60963042826040784456186125 22861141059765294171069797)
          ·
            refine ⟨4286463948705992657075587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22861141059765294171069797 4286463948705992657075587)
            ·
              refine ⟨6429695923058988985613381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286463948705992657075587 6429695923058988985613381)
              ·
                refine ⟨1205567985573560434802509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6429695923058988985613381 1205567985573560434802509)
                ·
                  refine ⟨452087994590085163050941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205567985573560434802509 452087994590085163050941)
                  ·
                    rfl

theorem cell21_1980986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_1980986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980986 prefixEnd_1980986 := by exact prefixLift 1980986
  have htrace : WordTrace (prefixWord ++ tailWord_1980986) baseStart_1980986 baseEnd_1980986 := by
    simpa [prefixWord, tailWord_1980986, baseEnd_1980986] using wordTrace_append hprefix tailTrace_1980986
  have hstable : (prefixWord ++ tailWord_1980986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980986).length < 2 ^ (prefixWord ++ tailWord_1980986).sum := by decide
  have hdescent : baseEnd_1980986 < baseStart_1980986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981028 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_1981028 : Nat := 118140960795 + 1981028 * 2 ^ 59
def prefixEnd_1981028 : Nat := 4983230072969 + 3 ^ 40 * 1981028 * 2
def baseEnd_1981028 : Nat := 452097579562302423350855

theorem tailTrace_1981028 : CollatzResearch.WordTrace tailWord_1981028 prefixEnd_1981028 452097579562302423350855 := by
  unfold tailWord_1981028
  simp only [CollatzResearch.WordTrace]
  refine ⟨36127013533540681745735869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48169351378054242327647825 36127013533540681745735869)
  ·
    refine ⟨13547630075077755654650951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36127013533540681745735869 13547630075077755654650951)
    ·
      refine ⟨20321445112616633481976427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13547630075077755654650951 20321445112616633481976427)
      ·
        refine ⟨30482167668924950222964641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20321445112616633481976427 30482167668924950222964641)
        ·
          refine ⟨22861625751693712667223481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30482167668924950222964641 22861625751693712667223481)
          ·
            refine ⟨17146219313770284500417611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22861625751693712667223481 17146219313770284500417611)
            ·
              refine ⟨25719328970655426750626417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17146219313770284500417611 25719328970655426750626417)
              ·
                refine ⟨19289496727991570062969813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25719328970655426750626417 19289496727991570062969813)
                ·
                  refine ⟨452097579562302423350855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19289496727991570062969813 452097579562302423350855)
                  ·
                    rfl

theorem cell21_1981028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_1981028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981028 prefixEnd_1981028 := by exact prefixLift 1981028
  have htrace : WordTrace (prefixWord ++ tailWord_1981028) baseStart_1981028 baseEnd_1981028 := by
    simpa [prefixWord, tailWord_1981028, baseEnd_1981028] using wordTrace_append hprefix tailTrace_1981028
  have hstable : (prefixWord ++ tailWord_1981028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981028).length < 2 ^ (prefixWord ++ tailWord_1981028).sum := by decide
  have hdescent : baseEnd_1981028 < baseStart_1981028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981059 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 4]
def baseStart_1981059 : Nat := 118140960795 + 1981059 * 2 ^ 59
def prefixEnd_1981059 : Nat := 4983230072969 + 3 ^ 40 * 1981059 * 2
def baseEnd_1981059 : Nat := 452104654184653258334125

theorem tailTrace_1981059 : CollatzResearch.WordTrace tailWord_1981059 prefixEnd_1981059 452104654184653258334125 := by
  unfold tailWord_1981059
  simp only [CollatzResearch.WordTrace]
  refine ⟨72255157729969055785850231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48170105153312703857233487 72255157729969055785850231)
  ·
    refine ⟨108382736594953583678775347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72255157729969055785850231 108382736594953583678775347)
    ·
      refine ⟨162574104892430375518163021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108382736594953583678775347 162574104892430375518163021)
      ·
        refine ⟨60965289334661390819311133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162574104892430375518163021 60965289334661390819311133)
        ·
          refine ⟨22861983500498021557241675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60965289334661390819311133 22861983500498021557241675)
          ·
            refine ⟨34292975250747032335862513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22861983500498021557241675 34292975250747032335862513)
            ·
              refine ⟨25719731438060274251896885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34292975250747032335862513 25719731438060274251896885)
              ·
                refine ⟨2411224822318150711115333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25719731438060274251896885 2411224822318150711115333)
                ·
                  refine ⟨452104654184653258334125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2411224822318150711115333 452104654184653258334125)
                  ·
                    rfl

theorem cell21_1981059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 4].length) (baseStart_1981059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981059 prefixEnd_1981059 := by exact prefixLift 1981059
  have htrace : WordTrace (prefixWord ++ tailWord_1981059) baseStart_1981059 baseEnd_1981059 := by
    simpa [prefixWord, tailWord_1981059, baseEnd_1981059] using wordTrace_append hprefix tailTrace_1981059
  have hstable : (prefixWord ++ tailWord_1981059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981059).length < 2 ^ (prefixWord ++ tailWord_1981059).sum := by decide
  have hdescent : baseEnd_1981059 < baseStart_1981059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981076 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1981076 : Nat := 118140960795 + 1981076 * 2 ^ 59
def prefixEnd_1981076 : Nat := 4983230072969 + 3 ^ 40 * 1981076 * 2
def baseEnd_1981076 : Nat := 452108533816265006550757

theorem tailTrace_1981076 : CollatzResearch.WordTrace tailWord_1981076 prefixEnd_1981076 452108533816265006550757 := by
  unfold tailWord_1981076
  simp only [CollatzResearch.WordTrace]
  refine ⟨36127888885453733844609541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48170518513938311792812721 36127888885453733844609541)
  ·
    refine ⟨6773979166022575095864289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36127888885453733844609541 6773979166022575095864289)
    ·
      refine ⟨5080484374516931321898217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6773979166022575095864289 5080484374516931321898217)
      ·
        refine ⟨3810363280887698491423663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5080484374516931321898217 3810363280887698491423663)
        ·
          refine ⟨5715544921331547737135495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810363280887698491423663 5715544921331547737135495)
          ·
            refine ⟨8573317381997321605703243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5715544921331547737135495 8573317381997321605703243)
            ·
              refine ⟨12859976072995982408554865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8573317381997321605703243 12859976072995982408554865)
              ·
                refine ⟨9644982054746986806416149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12859976072995982408554865 9644982054746986806416149)
                ·
                  refine ⟨452108533816265006550757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9644982054746986806416149 452108533816265006550757)
                  ·
                    rfl

theorem cell21_1981076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1981076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981076 prefixEnd_1981076 := by exact prefixLift 1981076
  have htrace : WordTrace (prefixWord ++ tailWord_1981076) baseStart_1981076 baseEnd_1981076 := by
    simpa [prefixWord, tailWord_1981076, baseEnd_1981076] using wordTrace_append hprefix tailTrace_1981076
  have hstable : (prefixWord ++ tailWord_1981076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981076).length < 2 ^ (prefixWord ++ tailWord_1981076).sum := by decide
  have hdescent : baseEnd_1981076 < baseStart_1981076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981110 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1981110 : Nat := 118140960795 + 1981110 * 2 ^ 59
def prefixEnd_1981110 : Nat := 4983230072969 + 3 ^ 40 * 1981110 * 2
def baseEnd_1981110 : Nat := 452116293079488502984021

theorem tailTrace_1981110 : CollatzResearch.WordTrace tailWord_1981110 prefixEnd_1981110 452116293079488502984021 := by
  unfold tailWord_1981110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4516063615799018218497299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48171345235189527663971189 4516063615799018218497299)
  ·
    refine ⟨6774095423698527327745949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4516063615799018218497299 6774095423698527327745949)
    ·
      refine ⟨2540285783886947747904731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6774095423698527327745949 2540285783886947747904731)
      ·
        refine ⟨3810428675830421621857097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540285783886947747904731 3810428675830421621857097)
        ·
          refine ⟨2857821506872816216392823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3810428675830421621857097 2857821506872816216392823)
          ·
            refine ⟨4286732260309224324589235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857821506872816216392823 4286732260309224324589235)
            ·
              refine ⟨6430098390463836486883853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286732260309224324589235 6430098390463836486883853)
              ·
                refine ⟨2411286896423938682581445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6430098390463836486883853 2411286896423938682581445)
                ·
                  refine ⟨452116293079488502984021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2411286896423938682581445 452116293079488502984021)
                  ·
                    rfl

theorem cell21_1981110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1981110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981110 prefixEnd_1981110 := by exact prefixLift 1981110
  have htrace : WordTrace (prefixWord ++ tailWord_1981110) baseStart_1981110 baseEnd_1981110 := by
    simpa [prefixWord, tailWord_1981110, baseEnd_1981110] using wordTrace_append hprefix tailTrace_1981110
  have hstable : (prefixWord ++ tailWord_1981110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981110).length < 2 ^ (prefixWord ++ tailWord_1981110).sum := by decide
  have hdescent : baseEnd_1981110 < baseStart_1981110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981149 : List Nat := [1, 4, 3, 13]
def baseStart_1981149 : Nat := 118140960795 + 1981149 * 2 ^ 59
def prefixEnd_1981149 : Nat := 4983230072969 + 3 ^ 40 * 1981149 * 2
def baseEnd_1981149 : Nat := 1860597503748284369687

theorem tailTrace_1981149 : CollatzResearch.WordTrace tailWord_1981149 prefixEnd_1981149 1860597503748284369687 := by
  unfold tailWord_1981149
  simp only [CollatzResearch.WordTrace]
  refine ⟨72258440299643001156626501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48172293533095334104417667 72258440299643001156626501)
  ·
    refine ⟨13548457556183062716867469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72258440299643001156626501 13548457556183062716867469)
    ·
      refine ⟨5080671583568648518825301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13548457556183062716867469 5080671583568648518825301)
      ·
        refine ⟨1860597503748284369687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 5080671583568648518825301 1860597503748284369687)
        ·
          rfl

theorem cell21_1981149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 13].length) (baseStart_1981149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981149 prefixEnd_1981149 := by exact prefixLift 1981149
  have htrace : WordTrace (prefixWord ++ tailWord_1981149) baseStart_1981149 baseEnd_1981149 := by
    simpa [prefixWord, tailWord_1981149, baseEnd_1981149] using wordTrace_append hprefix tailTrace_1981149
  have hstable : (prefixWord ++ tailWord_1981149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981149).length < 2 ^ (prefixWord ++ tailWord_1981149).sum := by decide
  have hdescent : baseEnd_1981149 < baseStart_1981149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981155 : List Nat := [1, 1, 1, 7, 1, 1, 4, 2, 3]
def baseStart_1981155 : Nat := 118140960795 + 1981155 * 2 ^ 59
def prefixEnd_1981155 : Nat := 4983230072969 + 3 ^ 40 * 1981155 * 2
def baseEnd_1981155 : Nat := 452126562692578424733929

theorem tailTrace_1981155 : CollatzResearch.WordTrace tailWord_1981155 prefixEnd_1981155 452126562692578424733929 := by
  unfold tailWord_1981155
  simp only [CollatzResearch.WordTrace]
  refine ⟨72258659137621264181344919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48172439425080842787563279 72258659137621264181344919)
  ·
    refine ⟨108387988706431896272017379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72258659137621264181344919 108387988706431896272017379)
    ·
      refine ⟨162581983059647844408026069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108387988706431896272017379 162581983059647844408026069)
      ·
        refine ⟨3810515227960496353313111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 162581983059647844408026069 3810515227960496353313111)
        ·
          refine ⟨5715772841940744529969667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810515227960496353313111 5715772841940744529969667)
          ·
            refine ⟨8573659262911116794954501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5715772841940744529969667 8573659262911116794954501)
            ·
              refine ⟨1607561111795834399053969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8573659262911116794954501 1607561111795834399053969)
              ·
                refine ⟨1205670833846875799290477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607561111795834399053969 1205670833846875799290477)
                ·
                  refine ⟨452126562692578424733929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205670833846875799290477 452126562692578424733929)
                  ·
                    rfl

theorem cell21_1981155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 3].length) (baseStart_1981155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981155 prefixEnd_1981155 := by exact prefixLift 1981155
  have htrace : WordTrace (prefixWord ++ tailWord_1981155) baseStart_1981155 baseEnd_1981155 := by
    simpa [prefixWord, tailWord_1981155, baseEnd_1981155] using wordTrace_append hprefix tailTrace_1981155
  have hstable : (prefixWord ++ tailWord_1981155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981155).length < 2 ^ (prefixWord ++ tailWord_1981155).sum := by decide
  have hdescent : baseEnd_1981155 < baseStart_1981155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981166 : List Nat := [4, 1, 2, 1, 1, 3, 3, 6]
def baseStart_1981166 : Nat := 118140960795 + 1981166 * 2 ^ 59
def prefixEnd_1981166 : Nat := 4983230072969 + 3 ^ 40 * 1981166 * 2
def baseEnd_1981166 : Nat := 150709691014148283350191

theorem tailTrace_1981166 : CollatzResearch.WordTrace tailWord_1981166 prefixEnd_1981166 150709691014148283350191 := by
  unfold tailWord_1981166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9032382542572676632499419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48172706893720942039996901 9032382542572676632499419)
  ·
    refine ⟨13548573813859014948749129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9032382542572676632499419 13548573813859014948749129)
    ·
      refine ⟨10161430360394261211561847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13548573813859014948749129 10161430360394261211561847)
      ·
        refine ⟨15242145540591391817342771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10161430360394261211561847 15242145540591391817342771)
        ·
          refine ⟨22863218310887087726014157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15242145540591391817342771 22863218310887087726014157)
          ·
            refine ⟨8573706866582657897255309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22863218310887087726014157 8573706866582657897255309)
            ·
              refine ⟨3215140074968496711470741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8573706866582657897255309 3215140074968496711470741)
              ·
                refine ⟨150709691014148283350191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3215140074968496711470741 150709691014148283350191)
                ·
                  rfl

theorem cell21_1981166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_1981166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981166 prefixEnd_1981166 := by exact prefixLift 1981166
  have htrace : WordTrace (prefixWord ++ tailWord_1981166) baseStart_1981166 baseEnd_1981166 := by
    simpa [prefixWord, tailWord_1981166, baseEnd_1981166] using wordTrace_append hprefix tailTrace_1981166
  have hstable : (prefixWord ++ tailWord_1981166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981166).length < 2 ^ (prefixWord ++ tailWord_1981166).sum := by decide
  have hdescent : baseEnd_1981166 < baseStart_1981166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981180 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_1981180 : Nat := 118140960795 + 1981180 * 2 ^ 59
def prefixEnd_1981180 : Nat := 4983230072969 + 3 ^ 40 * 1981180 * 2
def baseEnd_1981180 : Nat := 452132268033183936817211

theorem tailTrace_1981180 : CollatzResearch.WordTrace tailWord_1981180 prefixEnd_1981180 452132268033183936817211 := by
  unfold tailWord_1981180
  simp only [CollatzResearch.WordTrace]
  refine ⟨36129785481265346725502497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48173047308353795634003329 36129785481265346725502497)
  ·
    refine ⟨27097339110949010044126873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36129785481265346725502497 27097339110949010044126873)
    ·
      refine ⟨20323004333211757533095155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27097339110949010044126873 20323004333211757533095155)
      ·
        refine ⟨30484506499817636299642733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20323004333211757533095155 30484506499817636299642733)
        ·
          refine ⟨11431689937431613612366025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30484506499817636299642733 11431689937431613612366025)
          ·
            refine ⟨8573767453073710209274519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11431689937431613612366025 8573767453073710209274519)
            ·
              refine ⟨12860651179610565313911779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8573767453073710209274519 12860651179610565313911779)
              ·
                refine ⟨19290976769415847970867669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12860651179610565313911779 19290976769415847970867669)
                ·
                  refine ⟨452132268033183936817211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19290976769415847970867669 452132268033183936817211)
                  ·
                    rfl

theorem cell21_1981180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_1981180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981180 prefixEnd_1981180 := by exact prefixLift 1981180
  have htrace : WordTrace (prefixWord ++ tailWord_1981180) baseStart_1981180 baseEnd_1981180 := by
    simpa [prefixWord, tailWord_1981180, baseEnd_1981180] using wordTrace_append hprefix tailTrace_1981180
  have hstable : (prefixWord ++ tailWord_1981180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981180).length < 2 ^ (prefixWord ++ tailWord_1981180).sum := by decide
  have hdescent : baseEnd_1981180 < baseStart_1981180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981228 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 4]
def baseStart_1981228 : Nat := 118140960795 + 1981228 * 2 ^ 59
def prefixEnd_1981228 : Nat := 4983230072969 + 3 ^ 40 * 1981228 * 2
def baseEnd_1981228 : Nat := 452143222287146520017113

theorem tailTrace_1981228 : CollatzResearch.WordTrace tailWord_1981228 prefixEnd_1981228 452143222287146520017113 := by
  unfold tailWord_1981228
  simp only [CollatzResearch.WordTrace]
  refine ⟨36130660833178398824376169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48174214444237865099168225 36130660833178398824376169)
  ·
    refine ⟨27097995624883799118282127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36130660833178398824376169 27097995624883799118282127)
    ·
      refine ⟨40646993437325698677423191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27097995624883799118282127 40646993437325698677423191)
      ·
        refine ⟨60970490155988548016134787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40646993437325698677423191 60970490155988548016134787)
        ·
          refine ⟨91455735233982822024202181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60970490155988548016134787 91455735233982822024202181)
          ·
            refine ⟨17147950356371779129537909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91455735233982822024202181 17147950356371779129537909)
            ·
              refine ⟨1607620345909854293394179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17147950356371779129537909 1607620345909854293394179)
              ·
                refine ⟨2411430518864781440091269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607620345909854293394179 2411430518864781440091269)
                ·
                  refine ⟨452143222287146520017113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2411430518864781440091269 452143222287146520017113)
                  ·
                    rfl

theorem cell21_1981228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_1981228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981228 prefixEnd_1981228 := by exact prefixLift 1981228
  have htrace : WordTrace (prefixWord ++ tailWord_1981228) baseStart_1981228 baseEnd_1981228 := by
    simpa [prefixWord, tailWord_1981228, baseEnd_1981228] using wordTrace_append hprefix tailTrace_1981228
  have hstable : (prefixWord ++ tailWord_1981228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981228).length < 2 ^ (prefixWord ++ tailWord_1981228).sum := by decide
  have hdescent : baseEnd_1981228 < baseStart_1981228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981242 : List Nat := [3, 1, 1, 1, 6, 1, 1, 7]
def baseStart_1981242 : Nat := 118140960795 + 1981242 * 2 ^ 59
def prefixEnd_1981242 : Nat := 4983230072969 + 3 ^ 40 * 1981242 * 2
def baseEnd_1981242 : Nat := 150715472425961868927917

theorem tailTrace_1981242 : CollatzResearch.WordTrace tailWord_1981242 prefixEnd_1981242 150715472425961868927917 := by
  unfold tailWord_1981242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18065458072076519509940495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48174554858870718693174653 18065458072076519509940495)
  ·
    refine ⟨27098187108114779264910743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18065458072076519509940495 27098187108114779264910743)
    ·
      refine ⟨40647280662172168897366115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27098187108114779264910743 40647280662172168897366115)
      ·
        refine ⟨60970920993258253346049173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40647280662172168897366115 60970920993258253346049173)
        ·
          refine ⟨2858011921558980625596055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60970920993258253346049173 2858011921558980625596055)
          ·
            refine ⟨4287017882338470938394083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858011921558980625596055 4287017882338470938394083)
            ·
              refine ⟨6430526823507706407591125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287017882338470938394083 6430526823507706407591125)
              ·
                refine ⟨150715472425961868927917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6430526823507706407591125 150715472425961868927917)
                ·
                  rfl

theorem cell21_1981242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_1981242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981242 prefixEnd_1981242 := by exact prefixLift 1981242
  have htrace : WordTrace (prefixWord ++ tailWord_1981242) baseStart_1981242 baseEnd_1981242 := by
    simpa [prefixWord, tailWord_1981242, baseEnd_1981242] using wordTrace_append hprefix tailTrace_1981242
  have hstable : (prefixWord ++ tailWord_1981242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981242).length < 2 ^ (prefixWord ++ tailWord_1981242).sum := by decide
  have hdescent : baseEnd_1981242 < baseStart_1981242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981273 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 5]
def baseStart_1981273 : Nat := 118140960795 + 1981273 * 2 ^ 59
def prefixEnd_1981273 : Nat := 4983230072969 + 3 ^ 40 * 1981273 * 2
def baseEnd_1981273 : Nat := 452153491900236441767021

theorem tailTrace_1981273 : CollatzResearch.WordTrace tailWord_1981273 prefixEnd_1981273 452153491900236441767021 := by
  unfold tailWord_1981273
  simp only [CollatzResearch.WordTrace]
  refine ⟨72262962951193770334140473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48175308634129180222760315 72262962951193770334140473)
  ·
    refine ⟨54197222213395327750605355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72262962951193770334140473 54197222213395327750605355)
    ·
      refine ⟨81295833320092991625908033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54197222213395327750605355 81295833320092991625908033)
      ·
        refine ⟨60971874990069743719431025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81295833320092991625908033 60971874990069743719431025)
        ·
          refine ⟨45728906242552307789573269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60971874990069743719431025 45728906242552307789573269)
          ·
            refine ⟨2143542480119639427636247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45728906242552307789573269 2143542480119639427636247)
            ·
              refine ⟨3215313720179459141454371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143542480119639427636247 3215313720179459141454371)
              ·
                refine ⟨4822970580269188712181557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215313720179459141454371 4822970580269188712181557)
                ·
                  refine ⟨452153491900236441767021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4822970580269188712181557 452153491900236441767021)
                  ·
                    rfl

theorem cell21_1981273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_1981273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981273 prefixEnd_1981273 := by exact prefixLift 1981273
  have htrace : WordTrace (prefixWord ++ tailWord_1981273) baseStart_1981273 baseEnd_1981273 := by
    simpa [prefixWord, tailWord_1981273, baseEnd_1981273] using wordTrace_append hprefix tailTrace_1981273
  have hstable : (prefixWord ++ tailWord_1981273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981273).length < 2 ^ (prefixWord ++ tailWord_1981273).sum := by decide
  have hdescent : baseEnd_1981273 < baseStart_1981273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981397 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 4]
def baseStart_1981397 : Nat := 118140960795 + 1981397 * 2 ^ 59
def prefixEnd_1981397 : Nat := 4983230072969 + 3 ^ 40 * 1981397 * 2
def baseEnd_1981397 : Nat := 452181790389639781700101

theorem tailTrace_1981397 : CollatzResearch.WordTrace tailWord_1981397 prefixEnd_1981397 452181790389639781700101 := by
  unfold tailWord_1981397
  simp only [CollatzResearch.WordTrace]
  refine ⟨72267485602744539511654445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48178323735163026341102963 72267485602744539511654445)
  ·
    refine ⟨27100307101029202316870417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72267485602744539511654445 27100307101029202316870417)
    ·
      refine ⟨20325230325771901737652813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27100307101029202316870417 20325230325771901737652813)
      ·
        refine ⟨7621961372164463151619805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20325230325771901737652813 7621961372164463151619805)
        ·
          refine ⟨2858235514561673681857427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7621961372164463151619805 2858235514561673681857427)
          ·
            refine ⟨4287353271842510522786141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858235514561673681857427 4287353271842510522786141)
            ·
              refine ⟨1607757476940941446044803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4287353271842510522786141 1607757476940941446044803)
              ·
                refine ⟨2411636215411412169067205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607757476940941446044803 2411636215411412169067205)
                ·
                  refine ⟨452181790389639781700101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2411636215411412169067205 452181790389639781700101)
                  ·
                    rfl

theorem cell21_1981397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_1981397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981397 prefixEnd_1981397 := by exact prefixLift 1981397
  have htrace : WordTrace (prefixWord ++ tailWord_1981397) baseStart_1981397 baseEnd_1981397 := by
    simpa [prefixWord, tailWord_1981397, baseEnd_1981397] using wordTrace_append hprefix tailTrace_1981397
  have hstable : (prefixWord ++ tailWord_1981397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981397).length < 2 ^ (prefixWord ++ tailWord_1981397).sum := by decide
  have hdescent : baseEnd_1981397 < baseStart_1981397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981498 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_1981498 : Nat := 118140960795 + 1981498 * 2 ^ 59
def prefixEnd_1981498 : Nat := 4983230072969 + 3 ^ 40 * 1981498 * 2
def baseEnd_1981498 : Nat := 452204839965686050516561

theorem tailTrace_1981498 : CollatzResearch.WordTrace tailWord_1981498 prefixEnd_1981498 452204839965686050516561 := by
  unfold tailWord_1981498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18067792343844658440270287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48180779583585755840720765 18067792343844658440270287)
  ·
    refine ⟨27101688515766987660405431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18067792343844658440270287 27101688515766987660405431)
    ·
      refine ⟨40652532773650481490608147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27101688515766987660405431 40652532773650481490608147)
      ·
        refine ⟨60978799160475722235912221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40652532773650481490608147 60978799160475722235912221)
        ·
          refine ⟨22867049685178395838467083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60978799160475722235912221 22867049685178395838467083)
          ·
            refine ⟨34300574527767593757700625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22867049685178395838467083 34300574527767593757700625)
            ·
              refine ⟨25725430895825695318275469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34300574527767593757700625 25725430895825695318275469)
              ·
                refine ⟨9647036585934635744353301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25725430895825695318275469 9647036585934635744353301)
                ·
                  refine ⟨452204839965686050516561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9647036585934635744353301 452204839965686050516561)
                  ·
                    rfl

theorem cell21_1981498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_1981498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981498 prefixEnd_1981498 := by exact prefixLift 1981498
  have htrace : WordTrace (prefixWord ++ tailWord_1981498) baseStart_1981498 baseEnd_1981498 := by
    simpa [prefixWord, tailWord_1981498, baseEnd_1981498] using wordTrace_append hprefix tailTrace_1981498
  have hstable : (prefixWord ++ tailWord_1981498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981498).length < 2 ^ (prefixWord ++ tailWord_1981498).sum := by decide
  have hdescent : baseEnd_1981498 < baseStart_1981498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981594 : List Nat := [3, 1, 1, 5, 1, 1, 3, 3, 3]
def baseStart_1981594 : Nat := 118140960795 + 1981594 * 2 ^ 59
def prefixEnd_1981594 : Nat := 4983230072969 + 3 ^ 40 * 1981594 * 2
def baseEnd_1981594 : Nat := 452226748473611216916365

theorem tailTrace_1981594 : CollatzResearch.WordTrace tailWord_1981594 prefixEnd_1981594 452226748473611216916365 := by
  unfold tailWord_1981594
  simp only [CollatzResearch.WordTrace]
  refine ⟨18068667695757710539143959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48183113855353894771050557 18068667695757710539143959)
  ·
    refine ⟨27103001543636565808715939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18068667695757710539143959 27103001543636565808715939)
    ·
      refine ⟨40654502315454848713073909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27103001543636565808715939 40654502315454848713073909)
      ·
        refine ⟨3811359592073892066850679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40654502315454848713073909 3811359592073892066850679)
        ·
          refine ⟨5717039388110838100276019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3811359592073892066850679 5717039388110838100276019)
          ·
            refine ⟨8575559082166257150414029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5717039388110838100276019 8575559082166257150414029)
            ·
              refine ⟨3215834655812346431405261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8575559082166257150414029 3215834655812346431405261)
              ·
                refine ⟨1205937995929629911776973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3215834655812346431405261 1205937995929629911776973)
                ·
                  refine ⟨452226748473611216916365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205937995929629911776973 452226748473611216916365)
                  ·
                    rfl

theorem cell21_1981594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_1981594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981594 prefixEnd_1981594 := by exact prefixLift 1981594
  have htrace : WordTrace (prefixWord ++ tailWord_1981594) baseStart_1981594 baseEnd_1981594 := by
    simpa [prefixWord, tailWord_1981594, baseEnd_1981594] using wordTrace_append hprefix tailTrace_1981594
  have hstable : (prefixWord ++ tailWord_1981594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981594).length < 2 ^ (prefixWord ++ tailWord_1981594).sum := by decide
  have hdescent : baseEnd_1981594 < baseStart_1981594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981605 : List Nat := [1, 3, 1, 2, 1, 6, 7]
def baseStart_1981605 : Nat := 118140960795 + 1981605 * 2 ^ 59
def prefixEnd_1981605 : Nat := 4983230072969 + 3 ^ 40 * 1981605 * 2
def baseEnd_1981605 : Nat := 50247695424830849137001

theorem tailTrace_1981605 : CollatzResearch.WordTrace tailWord_1981605 prefixEnd_1981605 50247695424830849137001 := by
  unfold tailWord_1981605
  simp only [CollatzResearch.WordTrace]
  refine ⟨72275071985990991035226269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48183381323993994023484179 72275071985990991035226269)
  ·
    refine ⟨27103151994746621638209851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72275071985990991035226269 27103151994746621638209851)
    ·
      refine ⟨40654727992119932457314777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27103151994746621638209851 40654727992119932457314777)
      ·
        refine ⟨30491045994089949342986083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40654727992119932457314777 30491045994089949342986083)
        ·
          refine ⟨45736568991134924014479125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30491045994089949342986083 45736568991134924014479125)
          ·
            refine ⟨2143901671459449563178709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45736568991134924014479125 2143901671459449563178709)
            ·
              refine ⟨50247695424830849137001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2143901671459449563178709 50247695424830849137001)
              ·
                rfl

theorem cell21_1981605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 7].length) (baseStart_1981605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981605 prefixEnd_1981605 := by exact prefixLift 1981605
  have htrace : WordTrace (prefixWord ++ tailWord_1981605) baseStart_1981605 baseEnd_1981605 := by
    simpa [prefixWord, tailWord_1981605, baseEnd_1981605] using wordTrace_append hprefix tailTrace_1981605
  have hstable : (prefixWord ++ tailWord_1981605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981605).length < 2 ^ (prefixWord ++ tailWord_1981605).sum := by decide
  have hdescent : baseEnd_1981605 < baseStart_1981605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981664 : List Nat := [2, 1, 1, 3, 1, 13]
def baseStart_1981664 : Nat := 118140960795 + 1981664 * 2 ^ 59
def prefixEnd_1981664 : Nat := 4983230072969 + 3 ^ 40 * 1981664 * 2
def baseEnd_1981664 : Nat := 16749730497307653731465

theorem tailTrace_1981664 : CollatzResearch.WordTrace tailWord_1981664 prefixEnd_1981664 16749730497307653731465 := by
  unfold tailWord_1981664
  simp only [CollatzResearch.WordTrace]
  refine ⟨36138611946388622055812023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48184815928518162741082697 36138611946388622055812023)
  ·
    refine ⟨54207917919582933083718035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36138611946388622055812023 54207917919582933083718035)
    ·
      refine ⟨81311876879374399625577053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54207917919582933083718035 81311876879374399625577053)
      ·
        refine ⟨30491953829765399859591395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81311876879374399625577053 30491953829765399859591395)
        ·
          refine ⟨45737930744648099789387093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30491953829765399859591395 45737930744648099789387093)
          ·
            refine ⟨16749730497307653731465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 45737930744648099789387093 16749730497307653731465)
            ·
              rfl

theorem cell21_1981664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 13].length) (baseStart_1981664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981664 prefixEnd_1981664 := by exact prefixLift 1981664
  have htrace : WordTrace (prefixWord ++ tailWord_1981664) baseStart_1981664 baseEnd_1981664 := by
    simpa [prefixWord, tailWord_1981664, baseEnd_1981664] using wordTrace_append hprefix tailTrace_1981664
  have hstable : (prefixWord ++ tailWord_1981664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981664).length < 2 ^ (prefixWord ++ tailWord_1981664).sum := by decide
  have hdescent : baseEnd_1981664 < baseStart_1981664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981695 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 7]
def baseStart_1981695 : Nat := 118140960795 + 1981695 * 2 ^ 59
def prefixEnd_1981695 : Nat := 4983230072969 + 3 ^ 40 * 1981695 * 2
def baseEnd_1981695 : Nat := 452249798049657485732825

theorem tailTrace_1981695 : CollatzResearch.WordTrace tailWord_1981695 prefixEnd_1981695 452249798049657485732825 := by
  unfold tailWord_1981695
  simp only [CollatzResearch.WordTrace]
  refine ⟨72278354555664936406002539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48185569703776624270668359 72278354555664936406002539)
  ·
    refine ⟨108417531833497404609003809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72278354555664936406002539 108417531833497404609003809)
    ·
      refine ⟨81313148875123053456752857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108417531833497404609003809 81313148875123053456752857)
      ·
        refine ⟨60984861656342290092564643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81313148875123053456752857 60984861656342290092564643)
        ·
          refine ⟨91477292484513435138846965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60984861656342290092564643 91477292484513435138846965)
          ·
            refine ⟨8575996170423134544266903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91477292484513435138846965 8575996170423134544266903)
            ·
              refine ⟨12863994255634701816400355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575996170423134544266903 12863994255634701816400355)
              ·
                refine ⟨19295991383452052724600533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12863994255634701816400355 19295991383452052724600533)
                ·
                  refine ⟨452249798049657485732825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19295991383452052724600533 452249798049657485732825)
                  ·
                    rfl

theorem cell21_1981695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_1981695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981695 prefixEnd_1981695 := by exact prefixLift 1981695
  have htrace : WordTrace (prefixWord ++ tailWord_1981695) baseStart_1981695 baseEnd_1981695 := by
    simpa [prefixWord, tailWord_1981695, baseEnd_1981695] using wordTrace_append hprefix tailTrace_1981695
  have hstable : (prefixWord ++ tailWord_1981695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981695).length < 2 ^ (prefixWord ++ tailWord_1981695).sum := by decide
  have hdescent : baseEnd_1981695 < baseStart_1981695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981740 : List Nat := [2, 2, 1, 1, 1, 3, 1, 10]
def baseStart_1981740 : Nat := 118140960795 + 1981740 * 2 ^ 59
def prefixEnd_1981740 : Nat := 4983230072969 + 3 ^ 40 * 1981740 * 2
def baseEnd_1981740 : Nat := 150753355887582469160911

theorem tailTrace_1981740 : CollatzResearch.WordTrace tailWord_1981740 prefixEnd_1981740 150753355887582469160911 := by
  unfold tailWord_1981740
  simp only [CollatzResearch.WordTrace]
  refine ⟨36139997920250954545695337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48186663893667939394260449 36139997920250954545695337)
  ·
    refine ⟨27104998440188215909271503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36139997920250954545695337 27104998440188215909271503)
    ·
      refine ⟨40657497660282323863907255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27104998440188215909271503 40657497660282323863907255)
      ·
        refine ⟨60986246490423485795860883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40657497660282323863907255 60986246490423485795860883)
        ·
          refine ⟨91479369735635228693791325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60986246490423485795860883 91479369735635228693791325)
          ·
            refine ⟨34304763650863210760171747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91479369735635228693791325 34304763650863210760171747)
            ·
              refine ⟨51457145476294816140257621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34304763650863210760171747 51457145476294816140257621)
              ·
                refine ⟨150753355887582469160911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51457145476294816140257621 150753355887582469160911)
                ·
                  rfl

theorem cell21_1981740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_1981740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981740 prefixEnd_1981740 := by exact prefixLift 1981740
  have htrace : WordTrace (prefixWord ++ tailWord_1981740) baseStart_1981740 baseEnd_1981740 := by
    simpa [prefixWord, tailWord_1981740, baseEnd_1981740] using wordTrace_append hprefix tailTrace_1981740
  have hstable : (prefixWord ++ tailWord_1981740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981740).length < 2 ^ (prefixWord ++ tailWord_1981740).sum := by decide
  have hdescent : baseEnd_1981740 < baseStart_1981740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981833 : List Nat := [1, 2, 1, 1, 8, 8]
def baseStart_1981833 : Nat := 118140960795 + 1981833 * 2 ^ 59
def prefixEnd_1981833 : Nat := 4983230072969 + 3 ^ 40 * 1981833 * 2
def baseEnd_1981833 : Nat := 16751158945548144904909

theorem tailTrace_1981833 : CollatzResearch.WordTrace tailWord_1981833 prefixEnd_1981833 16751158945548144904909 := by
  unfold tailWord_1981833
  simp only [CollatzResearch.WordTrace]
  refine ⟨72283387829164985974526153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48188925219443323983017435 72283387829164985974526153)
  ·
    refine ⟨54212540871873739480894615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72283387829164985974526153 54212540871873739480894615)
    ·
      refine ⟨81318811307810609221341923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54212540871873739480894615 81318811307810609221341923)
      ·
        refine ⟨121978216961715913832012885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81318811307810609221341923 121978216961715913832012885)
        ·
          refine ⟨1429432230020108365218901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 121978216961715913832012885 1429432230020108365218901)
          ·
            refine ⟨16751158945548144904909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1429432230020108365218901 16751158945548144904909)
            ·
              rfl

theorem cell21_1981833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 8].length) (baseStart_1981833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981833 prefixEnd_1981833 := by exact prefixLift 1981833
  have htrace : WordTrace (prefixWord ++ tailWord_1981833) baseStart_1981833 baseEnd_1981833 := by
    simpa [prefixWord, tailWord_1981833, baseEnd_1981833] using wordTrace_append hprefix tailTrace_1981833
  have hstable : (prefixWord ++ tailWord_1981833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981833).length < 2 ^ (prefixWord ++ tailWord_1981833).sum := by decide
  have hdescent : baseEnd_1981833 < baseStart_1981833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981847 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 5]
def baseStart_1981847 : Nat := 118140960795 + 1981847 * 2 ^ 59
def prefixEnd_1981847 : Nat := 4983230072969 + 3 ^ 40 * 1981847 * 2
def baseEnd_1981847 : Nat := 452284486520538999199181

theorem tailTrace_1981847 : CollatzResearch.WordTrace tailWord_1981847 prefixEnd_1981847 452284486520538999199181 := by
  unfold tailWord_1981847
  simp only [CollatzResearch.WordTrace]
  refine ⟨72283898451114266365535795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48189265634076177577023863 72283898451114266365535795)
  ·
    refine ⟨108425847676671399548303693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72283898451114266365535795 108425847676671399548303693)
    ·
      refine ⟨40659692878751774830613885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108425847676671399548303693 40659692878751774830613885)
      ·
        refine ⟨15247384829531915561480207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40659692878751774830613885 15247384829531915561480207)
        ·
          refine ⟨22871077244297873342220311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15247384829531915561480207 22871077244297873342220311)
          ·
            refine ⟨34306615866446810013330467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22871077244297873342220311 34306615866446810013330467)
            ·
              refine ⟨51459923799670215019995701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34306615866446810013330467 51459923799670215019995701)
              ·
                refine ⟨4824367856219082658124597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51459923799670215019995701 4824367856219082658124597)
                ·
                  refine ⟨452284486520538999199181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4824367856219082658124597 452284486520538999199181)
                  ·
                    rfl

theorem cell21_1981847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_1981847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981847 prefixEnd_1981847 := by exact prefixLift 1981847
  have htrace : WordTrace (prefixWord ++ tailWord_1981847) baseStart_1981847 baseEnd_1981847 := by
    simpa [prefixWord, tailWord_1981847, baseEnd_1981847] using wordTrace_append hprefix tailTrace_1981847
  have hstable : (prefixWord ++ tailWord_1981847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981847).length < 2 ^ (prefixWord ++ tailWord_1981847).sum := by decide
  have hdescent : baseEnd_1981847 < baseStart_1981847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981971 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 4]
def baseStart_1981971 : Nat := 118140960795 + 1981971 * 2 ^ 59
def prefixEnd_1981971 : Nat := 4983230072969 + 3 ^ 40 * 1981971 * 2
def baseEnd_1981971 : Nat := 452312785009942339132261

theorem tailTrace_1981971 : CollatzResearch.WordTrace tailWord_1981971 prefixEnd_1981971 452312785009942339132261 := by
  unfold tailWord_1981971
  simp only [CollatzResearch.WordTrace]
  refine ⟨72288421102665035543049767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48192280735110023695366511 72288421102665035543049767)
  ·
    refine ⟨108432631653997553314574651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72288421102665035543049767 108432631653997553314574651)
    ·
      refine ⟨162648947480996329971861977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108432631653997553314574651 162648947480996329971861977)
      ·
        refine ⟨121986710610747247478896483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162648947480996329971861977 121986710610747247478896483)
        ·
          refine ⟨182980065916120871218344725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121986710610747247478896483 182980065916120871218344725)
          ·
            refine ⟨8577190589818165838359909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182980065916120871218344725 8577190589818165838359909)
            ·
              refine ⟨1608223235590906094692483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8577190589818165838359909 1608223235590906094692483)
              ·
                refine ⟨2412334853386359142038725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608223235590906094692483 2412334853386359142038725)
                ·
                  refine ⟨452312785009942339132261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2412334853386359142038725 452312785009942339132261)
                  ·
                    rfl

theorem cell21_1981971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 4].length) (baseStart_1981971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1981971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1981971 prefixEnd_1981971 := by exact prefixLift 1981971
  have htrace : WordTrace (prefixWord ++ tailWord_1981971) baseStart_1981971 baseEnd_1981971 := by
    simpa [prefixWord, tailWord_1981971, baseEnd_1981971] using wordTrace_append hprefix tailTrace_1981971
  have hstable : (prefixWord ++ tailWord_1981971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981971).length < 2 ^ (prefixWord ++ tailWord_1981971).sum := by decide
  have hdescent : baseEnd_1981971 < baseStart_1981971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982061 : List Nat := [1, 5, 1, 1, 4, 1, 8]
def baseStart_1982061 : Nat := 118140960795 + 1982061 * 2 ^ 59
def prefixEnd_1982061 : Nat := 4983230072969 + 3 ^ 40 * 1982061 * 2
def baseEnd_1982061 : Nat := 50259258248458020292453

theorem tailTrace_1982061 : CollatzResearch.WordTrace tailWord_1982061 prefixEnd_1982061 50259258248458020292453 := by
  unfold tailWord_1982061
  simp only [CollatzResearch.WordTrace]
  refine ⟨72291703672338980913826037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48194469114892653942550691 72291703672338980913826037)
  ·
    refine ⟨6777347219281779460671191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72291703672338980913826037 6777347219281779460671191)
    ·
      refine ⟨10166020828922669191006787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6777347219281779460671191 10166020828922669191006787)
      ·
        refine ⟨15249031243384003786510181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10166020828922669191006787 15249031243384003786510181)
        ·
          refine ⟨2859193358134500709970659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15249031243384003786510181 2859193358134500709970659)
          ·
            refine ⟨4288790037201751064955989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2859193358134500709970659 4288790037201751064955989)
            ·
              refine ⟨50259258248458020292453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4288790037201751064955989 50259258248458020292453)
              ·
                rfl

theorem cell21_1982061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 8].length) (baseStart_1982061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982061 prefixEnd_1982061 := by exact prefixLift 1982061
  have htrace : WordTrace (prefixWord ++ tailWord_1982061) baseStart_1982061 baseEnd_1982061 := by
    simpa [prefixWord, tailWord_1982061, baseEnd_1982061] using wordTrace_append hprefix tailTrace_1982061
  have hstable : (prefixWord ++ tailWord_1982061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982061).length < 2 ^ (prefixWord ++ tailWord_1982061).sum := by decide
  have hdescent : baseEnd_1982061 < baseStart_1982061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982075 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 5]
def baseStart_1982075 : Nat := 118140960795 + 1982075 * 2 ^ 59
def prefixEnd_1982075 : Nat := 4983230072969 + 3 ^ 40 * 1982075 * 2
def baseEnd_1982075 : Nat := 452336519226861269398715

theorem tailTrace_1982075 : CollatzResearch.WordTrace tailWord_1982075 prefixEnd_1982075 452336519226861269398715 := by
  unfold tailWord_1982075
  simp only [CollatzResearch.WordTrace]
  refine ⟨72292214294288261304835679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48194809529525507536557119 72292214294288261304835679)
  ·
    refine ⟨108438321441432391957253519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72292214294288261304835679 108438321441432391957253519)
    ·
      refine ⟨162657482162148587935880279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108438321441432391957253519 162657482162148587935880279)
      ·
        refine ⟨243986223243222881903820419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162657482162148587935880279 243986223243222881903820419)
        ·
          refine ⟨365979334864834322855730629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243986223243222881903820419 365979334864834322855730629)
          ·
            refine ⟨68621125287156435535449493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365979334864834322855730629 68621125287156435535449493)
            ·
              refine ⟨3216615247835457915724195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68621125287156435535449493 3216615247835457915724195)
              ·
                refine ⟨4824922871753186873586293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216615247835457915724195 4824922871753186873586293)
                ·
                  refine ⟨452336519226861269398715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4824922871753186873586293 452336519226861269398715)
                  ·
                    rfl

theorem cell21_1982075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 5].length) (baseStart_1982075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982075 prefixEnd_1982075 := by exact prefixLift 1982075
  have htrace : WordTrace (prefixWord ++ tailWord_1982075) baseStart_1982075 baseEnd_1982075 := by
    simpa [prefixWord, tailWord_1982075, baseEnd_1982075] using wordTrace_append hprefix tailTrace_1982075
  have hstable : (prefixWord ++ tailWord_1982075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982075).length < 2 ^ (prefixWord ++ tailWord_1982075).sum := by decide
  have hdescent : baseEnd_1982075 < baseStart_1982075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982126 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_1982126 : Nat := 118140960795 + 1982126 * 2 ^ 59
def prefixEnd_1982126 : Nat := 4983230072969 + 3 ^ 40 * 1982126 * 2
def baseEnd_1982126 : Nat := 452348158121696514048611

theorem tailTrace_1982126 : CollatzResearch.WordTrace tailWord_1982126 prefixEnd_1982126 452348158121696514048611 := by
  unfold tailWord_1982126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036759302137937126867779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48196049611402331343294821 9036759302137937126867779)
  ·
    refine ⟨13555138953206905690301669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9036759302137937126867779 13555138953206905690301669)
    ·
      refine ⟨2541588553726294816931563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13555138953206905690301669 2541588553726294816931563)
      ·
        refine ⟨3812382830589442225397345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2541588553726294816931563 3812382830589442225397345)
        ·
          refine ⟨2859287122942081669048009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3812382830589442225397345 2859287122942081669048009)
          ·
            refine ⟨2144465342206561251786007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2859287122942081669048009 2144465342206561251786007)
            ·
              refine ⟨3216698013309841877679011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144465342206561251786007 3216698013309841877679011)
              ·
                refine ⟨4825047019964762816518517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216698013309841877679011 4825047019964762816518517)
                ·
                  refine ⟨452348158121696514048611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4825047019964762816518517 452348158121696514048611)
                  ·
                    rfl

theorem cell21_1982126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_1982126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982126 prefixEnd_1982126 := by exact prefixLift 1982126
  have htrace : WordTrace (prefixWord ++ tailWord_1982126) baseStart_1982126 baseEnd_1982126 := by
    simpa [prefixWord, tailWord_1982126, baseEnd_1982126] using wordTrace_append hprefix tailTrace_1982126
  have hstable : (prefixWord ++ tailWord_1982126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982126).length < 2 ^ (prefixWord ++ tailWord_1982126).sum := by decide
  have hdescent : baseEnd_1982126 < baseStart_1982126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982140 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 4]
def baseStart_1982140 : Nat := 118140960795 + 1982140 * 2 ^ 59
def prefixEnd_1982140 : Nat := 4983230072969 + 3 ^ 40 * 1982140 * 2
def baseEnd_1982140 : Nat := 452351353112435600815249

theorem tailTrace_1982140 : CollatzResearch.WordTrace tailWord_1982140 prefixEnd_1982140 452351353112435600815249 := by
  unfold tailWord_1982140
  simp only [CollatzResearch.WordTrace]
  refine ⟨36147292519526388702975937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48196390026035184937301249 36147292519526388702975937)
  ·
    refine ⟨27110469389644791527231953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36147292519526388702975937 27110469389644791527231953)
    ·
      refine ⟨20332852042233593645423965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27110469389644791527231953 20332852042233593645423965)
      ·
        refine ⟨7624819515837597617033987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20332852042233593645423965 7624819515837597617033987)
        ·
          refine ⟨11437229273756396425550981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624819515837597617033987 11437229273756396425550981)
          ·
            refine ⟨2144480488829324329790809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11437229273756396425550981 2144480488829324329790809)
            ·
              refine ⟨1608360366621993247343107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2144480488829324329790809 1608360366621993247343107)
              ·
                refine ⟨2412540549932989871014661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608360366621993247343107 2412540549932989871014661)
                ·
                  refine ⟨452351353112435600815249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2412540549932989871014661 452351353112435600815249)
                  ·
                    rfl

theorem cell21_1982140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_1982140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982140 prefixEnd_1982140 := by exact prefixLift 1982140
  have htrace : WordTrace (prefixWord ++ tailWord_1982140) baseStart_1982140 baseEnd_1982140 := by
    simpa [prefixWord, tailWord_1982140, baseEnd_1982140] using wordTrace_append hprefix tailTrace_1982140
  have hstable : (prefixWord ++ tailWord_1982140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982140).length < 2 ^ (prefixWord ++ tailWord_1982140).sum := by decide
  have hdescent : baseEnd_1982140 < baseStart_1982140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982168 : List Nat := [2, 1, 2, 2, 3, 1, 2, 5, 3]
def baseStart_1982168 : Nat := 118140960795 + 1982168 * 2 ^ 59
def prefixEnd_1982168 : Nat := 4983230072969 + 3 ^ 40 * 1982168 * 2
def baseEnd_1982168 : Nat := 452357743093913774348525

theorem tailTrace_1982168 : CollatzResearch.WordTrace tailWord_1982168 prefixEnd_1982168 452357743093913774348525 := by
  unfold tailWord_1982168
  simp only [CollatzResearch.WordTrace]
  refine ⟨36147803141475669093985579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48197070855300892125314105 36147803141475669093985579)
  ·
    refine ⟨54221704712213503640978369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36147803141475669093985579 54221704712213503640978369)
    ·
      refine ⟨40666278534160127730733777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54221704712213503640978369 40666278534160127730733777)
      ·
        refine ⟨30499708900620095798050333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40666278534160127730733777 30499708900620095798050333)
        ·
          refine ⟨11437390837732535924268875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30499708900620095798050333 11437390837732535924268875)
          ·
            refine ⟨17156086256598803886403313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11437390837732535924268875 17156086256598803886403313)
            ·
              refine ⟨12867064692449102914802485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17156086256598803886403313 12867064692449102914802485)
              ·
                refine ⟨1206287314917103398262733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12867064692449102914802485 1206287314917103398262733)
                ·
                  refine ⟨452357743093913774348525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206287314917103398262733 452357743093913774348525)
                  ·
                    rfl

theorem cell21_1982168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 3].length) (baseStart_1982168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982168 prefixEnd_1982168 := by exact prefixLift 1982168
  have htrace : WordTrace (prefixWord ++ tailWord_1982168) baseStart_1982168 baseEnd_1982168 := by
    simpa [prefixWord, tailWord_1982168, baseEnd_1982168] using wordTrace_append hprefix tailTrace_1982168
  have hstable : (prefixWord ++ tailWord_1982168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982168).length < 2 ^ (prefixWord ++ tailWord_1982168).sum := by decide
  have hdescent : baseEnd_1982168 < baseStart_1982168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982244 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1982244 : Nat := 118140960795 + 1982244 * 2 ^ 59
def prefixEnd_1982244 : Nat := 4983230072969 + 3 ^ 40 * 1982244 * 2
def baseEnd_1982244 : Nat := 452375087329354531081703

theorem tailTrace_1982244 : CollatzResearch.WordTrace tailWord_1982244 prefixEnd_1982244 452375087329354531081703 := by
  unfold tailWord_1982244
  simp only [CollatzResearch.WordTrace]
  refine ⟨36149189115338001583868893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48198918820450668778491857 36149189115338001583868893)
  ·
    refine ⟨13555945918251750593950835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36149189115338001583868893 13555945918251750593950835)
    ·
      refine ⟨20333918877377625890926253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13555945918251750593950835 20333918877377625890926253)
      ·
        refine ⟨7625219579016609709097345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20333918877377625890926253 7625219579016609709097345)
        ·
          refine ⟨5718914684262457281823009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7625219579016609709097345 5718914684262457281823009)
          ·
            refine ⟨4289186013196842961367257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5718914684262457281823009 4289186013196842961367257)
            ·
              refine ⟨3216889509897632221025443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4289186013196842961367257 3216889509897632221025443)
              ·
                refine ⟨4825334264846448331538165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216889509897632221025443 4825334264846448331538165)
                ·
                  refine ⟨452375087329354531081703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4825334264846448331538165 452375087329354531081703)
                  ·
                    rfl

theorem cell21_1982244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1982244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982244 prefixEnd_1982244 := by exact prefixLift 1982244
  have htrace : WordTrace (prefixWord ++ tailWord_1982244) baseStart_1982244 baseEnd_1982244 := by
    simpa [prefixWord, tailWord_1982244, baseEnd_1982244] using wordTrace_append hprefix tailTrace_1982244
  have hstable : (prefixWord ++ tailWord_1982244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982244).length < 2 ^ (prefixWord ++ tailWord_1982244).sum := by decide
  have hdescent : baseEnd_1982244 < baseStart_1982244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982303 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 5]
def baseStart_1982303 : Nat := 118140960795 + 1982303 * 2 ^ 59
def prefixEnd_1982303 : Nat := 4983230072969 + 3 ^ 40 * 1982303 * 2
def baseEnd_1982303 : Nat := 452388551933183539598249

theorem tailTrace_1982303 : CollatzResearch.WordTrace tailWord_1982303 prefixEnd_1982303 452388551933183539598249 := by
  unfold tailWord_1982303
  simp only [CollatzResearch.WordTrace]
  refine ⟨72300530137462256244135563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48200353424974837496090375 72300530137462256244135563)
  ·
    refine ⟨108450795206193384366203345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72300530137462256244135563 108450795206193384366203345)
    ·
      refine ⟨81338096404645038274652509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108450795206193384366203345 81338096404645038274652509)
      ·
        refine ⟨30501786151741889352994691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81338096404645038274652509 30501786151741889352994691)
        ·
          refine ⟨45752679227612834029492037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30501786151741889352994691 45752679227612834029492037)
          ·
            refine ⟨8578627355177406380529757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45752679227612834029492037 8578627355177406380529757)
            ·
              refine ⟨3216985258191527392698659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8578627355177406380529757 3216985258191527392698659)
              ·
                refine ⟨4825477887287291089047989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216985258191527392698659 4825477887287291089047989)
                ·
                  refine ⟨452388551933183539598249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4825477887287291089047989 452388551933183539598249)
                  ·
                    rfl

theorem cell21_1982303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 5].length) (baseStart_1982303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982303 prefixEnd_1982303 := by exact prefixLift 1982303
  have htrace : WordTrace (prefixWord ++ tailWord_1982303) baseStart_1982303 baseEnd_1982303 := by
    simpa [prefixWord, tailWord_1982303, baseEnd_1982303] using wordTrace_append hprefix tailTrace_1982303
  have hstable : (prefixWord ++ tailWord_1982303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982303).length < 2 ^ (prefixWord ++ tailWord_1982303).sum := by decide
  have hdescent : baseEnd_1982303 < baseStart_1982303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982354 : List Nat := [3, 2, 3, 2, 1, 1, 4, 2, 3]
def baseStart_1982354 : Nat := 118140960795 + 1982354 * 2 ^ 59
def prefixEnd_1982354 : Nat := 4983230072969 + 3 ^ 40 * 1982354 * 2
def baseEnd_1982354 : Nat := 452400190828018784248145

theorem tailTrace_1982354 : CollatzResearch.WordTrace tailWord_1982354 prefixEnd_1982354 452400190828018784248145 := by
  unfold tailWord_1982354
  simp only [CollatzResearch.WordTrace]
  refine ⟨18075597565069372988560529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48201593506851661302828077 18075597565069372988560529)
  ·
    refine ⟨13556698173802029741420397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18075597565069372988560529 13556698173802029741420397)
    ·
      refine ⟨5083761815175761153032649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13556698173802029741420397 5083761815175761153032649)
      ·
        refine ⟨3812821361381820864774487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5083761815175761153032649 3812821361381820864774487)
        ·
          refine ⟨5719232042072731297161731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3812821361381820864774487 5719232042072731297161731)
          ·
            refine ⟨8578848063109096945742597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5719232042072731297161731 8578848063109096945742597)
            ·
              refine ⟨1608534011832955677326737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8578848063109096945742597 1608534011832955677326737)
              ·
                refine ⟨1206400508874716757995053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1608534011832955677326737 1206400508874716757995053)
                ·
                  refine ⟨452400190828018784248145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206400508874716757995053 452400190828018784248145)
                  ·
                    rfl

theorem cell21_1982354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_1982354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982354 prefixEnd_1982354 := by exact prefixLift 1982354
  have htrace : WordTrace (prefixWord ++ tailWord_1982354) baseStart_1982354 baseEnd_1982354 := by
    simpa [prefixWord, tailWord_1982354, baseEnd_1982354] using wordTrace_append hprefix tailTrace_1982354
  have hstable : (prefixWord ++ tailWord_1982354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982354).length < 2 ^ (prefixWord ++ tailWord_1982354).sum := by decide
  have hdescent : baseEnd_1982354 < baseStart_1982354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982365 : List Nat := [1, 4, 2, 1, 2, 4, 1, 6]
def baseStart_1982365 : Nat := 118140960795 + 1982365 * 2 ^ 59
def prefixEnd_1982365 : Nat := 4983230072969 + 3 ^ 40 * 1982365 * 2
def baseEnd_1982365 : Nat := 150800900392628403188263

theorem tailTrace_1982365 : CollatzResearch.WordTrace tailWord_1982365 prefixEnd_1982365 150800900392628403188263 := by
  unfold tailWord_1982365
  simp only [CollatzResearch.WordTrace]
  refine ⟨72302791463237640832892549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48201860975491760555261699 72302791463237640832892549)
  ·
    refine ⟨13556773399357057656167353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72302791463237640832892549 13556773399357057656167353)
    ·
      refine ⟨10167580049517793242125515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13556773399357057656167353 10167580049517793242125515)
      ·
        refine ⟨15251370074276689863188273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10167580049517793242125515 15251370074276689863188273)
        ·
          refine ⟨11438527555707517397391205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15251370074276689863188273 11438527555707517397391205)
          ·
            refine ⟨2144723916695159512010851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11438527555707517397391205 2144723916695159512010851)
            ·
              refine ⟨3217085875042739268016277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144723916695159512010851 3217085875042739268016277)
              ·
                refine ⟨150800900392628403188263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3217085875042739268016277 150800900392628403188263)
                ·
                  rfl

theorem cell21_1982365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 6].length) (baseStart_1982365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982365 prefixEnd_1982365 := by exact prefixLift 1982365
  have htrace : WordTrace (prefixWord ++ tailWord_1982365) baseStart_1982365 baseEnd_1982365 := by
    simpa [prefixWord, tailWord_1982365, baseEnd_1982365] using wordTrace_append hprefix tailTrace_1982365
  have hstable : (prefixWord ++ tailWord_1982365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982365).length < 2 ^ (prefixWord ++ tailWord_1982365).sum := by decide
  have hdescent : baseEnd_1982365 < baseStart_1982365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982393 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 6]
def baseStart_1982393 : Nat := 118140960795 + 1982393 * 2 ^ 59
def prefixEnd_1982393 : Nat := 4983230072969 + 3 ^ 40 * 1982393 * 2
def baseEnd_1982393 : Nat := 452409091159363383098065

theorem tailTrace_1982393 : CollatzResearch.WordTrace tailWord_1982393 prefixEnd_1982393 452409091159363383098065 := by
  unfold tailWord_1982393
  simp only [CollatzResearch.WordTrace]
  refine ⟨72303812707136201614911833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48202541804757467743274555 72303812707136201614911833)
  ·
    refine ⟨54227859530352151211183875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72303812707136201614911833 54227859530352151211183875)
    ·
      refine ⟨81341789295528226816775813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54227859530352151211183875 81341789295528226816775813)
      ·
        refine ⟨15251585492911542528145465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81341789295528226816775813 15251585492911542528145465)
        ·
          refine ⟨11438689119683656896109099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15251585492911542528145465 11438689119683656896109099)
          ·
            refine ⟨17158033679525485344163649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11438689119683656896109099 17158033679525485344163649)
            ·
              refine ⟨12868525259644114008122737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17158033679525485344163649 12868525259644114008122737)
              ·
                refine ⟨9651393944733085506092053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12868525259644114008122737 9651393944733085506092053)
                ·
                  refine ⟨452409091159363383098065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9651393944733085506092053 452409091159363383098065)
                  ·
                    rfl

theorem cell21_1982393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_1982393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982393 prefixEnd_1982393 := by exact prefixLift 1982393
  have htrace : WordTrace (prefixWord ++ tailWord_1982393) baseStart_1982393 baseEnd_1982393 := by
    simpa [prefixWord, tailWord_1982393, baseEnd_1982393] using wordTrace_append hprefix tailTrace_1982393
  have hstable : (prefixWord ++ tailWord_1982393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982393).length < 2 ^ (prefixWord ++ tailWord_1982393).sum := by decide
  have hdescent : baseEnd_1982393 < baseStart_1982393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982410 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_1982410 : Nat := 118140960795 + 1982410 * 2 ^ 59
def prefixEnd_1982410 : Nat := 4983230072969 + 3 ^ 40 * 1982410 * 2
def baseEnd_1982410 : Nat := 452412970790975131314697

theorem tailTrace_1982410 : CollatzResearch.WordTrace tailWord_1982410 prefixEnd_1982410 452412970790975131314697 := by
  unfold tailWord_1982410
  simp only [CollatzResearch.WordTrace]
  refine ⟨18076108187018653379570171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48202955165383075678853789 18076108187018653379570171)
  ·
    refine ⟨27114162280527980069355257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18076108187018653379570171 27114162280527980069355257)
    ·
      refine ⟨20335621710395985052016443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27114162280527980069355257 20335621710395985052016443)
      ·
        refine ⟨30503432565593977578024665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20335621710395985052016443 30503432565593977578024665)
        ·
          refine ⟨22877574424195483183518499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30503432565593977578024665 22877574424195483183518499)
          ·
            refine ⟨34316361636293224775277749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22877574424195483183518499 34316361636293224775277749)
            ·
              refine ⟨3217158903402489822682289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34316361636293224775277749 3217158903402489822682289)
              ·
                refine ⟨2412869177551867367011717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3217158903402489822682289 2412869177551867367011717)
                ·
                  refine ⟨452412970790975131314697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2412869177551867367011717 452412970790975131314697)
                  ·
                    rfl

theorem cell21_1982410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_1982410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982410 prefixEnd_1982410 := by exact prefixLift 1982410
  have htrace : WordTrace (prefixWord ++ tailWord_1982410) baseStart_1982410 baseEnd_1982410 := by
    simpa [prefixWord, tailWord_1982410, baseEnd_1982410] using wordTrace_append hprefix tailTrace_1982410
  have hstable : (prefixWord ++ tailWord_1982410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982410).length < 2 ^ (prefixWord ++ tailWord_1982410).sum := by decide
  have hdescent : baseEnd_1982410 < baseStart_1982410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982469 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 6]
def baseStart_1982469 : Nat := 118140960795 + 1982469 * 2 ^ 59
def prefixEnd_1982469 : Nat := 4983230072969 + 3 ^ 40 * 1982469 * 2
def baseEnd_1982469 : Nat := 452426435394804139831243

theorem tailTrace_1982469 : CollatzResearch.WordTrace tailWord_1982469 prefixEnd_1982469 452426435394804139831243 := by
  unfold tailWord_1982469
  simp only [CollatzResearch.WordTrace]
  refine ⟨72306584654860866594678461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48204389769907244396452307 72306584654860866594678461)
  ·
    refine ⟨27114969245572824973004423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72306584654860866594678461 27114969245572824973004423)
    ·
      refine ⟨40672453868359237459506635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27114969245572824973004423 40672453868359237459506635)
      ·
        refine ⟨61008680802538856189259953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40672453868359237459506635 61008680802538856189259953)
        ·
          refine ⟨45756510601904142141944965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61008680802538856189259953 45756510601904142141944965)
          ·
            refine ⟨8579345737857026651614681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45756510601904142141944965 8579345737857026651614681)
            ·
              refine ⟨6434509303392769988711011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8579345737857026651614681 6434509303392769988711011)
              ·
                refine ⟨9651763955089154983066517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6434509303392769988711011 9651763955089154983066517)
                ·
                  refine ⟨452426435394804139831243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9651763955089154983066517 452426435394804139831243)
                  ·
                    rfl

theorem cell21_1982469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_1982469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982469 prefixEnd_1982469 := by exact prefixLift 1982469
  have htrace : WordTrace (prefixWord ++ tailWord_1982469) baseStart_1982469 baseEnd_1982469 := by
    simpa [prefixWord, tailWord_1982469, baseEnd_1982469] using wordTrace_append hprefix tailTrace_1982469
  have hstable : (prefixWord ++ tailWord_1982469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982469).length < 2 ^ (prefixWord ++ tailWord_1982469).sum := by decide
  have hdescent : baseEnd_1982469 < baseStart_1982469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982483 : List Nat := [1, 1, 1, 2, 1, 4, 3, 8]
def baseStart_1982483 : Nat := 118140960795 + 1982483 * 2 ^ 59
def prefixEnd_1982483 : Nat := 4983230072969 + 3 ^ 40 * 1982483 * 2
def baseEnd_1982483 : Nat := 150809876795181075532627

theorem tailTrace_1982483 : CollatzResearch.WordTrace tailWord_1982483 prefixEnd_1982483 150809876795181075532627 := by
  unfold tailWord_1982483
  simp only [CollatzResearch.WordTrace]
  refine ⟨72307095276810146985688103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48204730184540097990458735 72307095276810146985688103)
  ·
    refine ⟨108460642915215220478532155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72307095276810146985688103 108460642915215220478532155)
    ·
      refine ⟨162690964372822830717798233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108460642915215220478532155 162690964372822830717798233)
      ·
        refine ⟨122018223279617123038348675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162690964372822830717798233 122018223279617123038348675)
        ·
          refine ⟨183027334919425684557523013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122018223279617123038348675 183027334919425684557523013)
          ·
            refine ⟨34317625297392315854535565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183027334919425684557523013 34317625297392315854535565)
            ·
              refine ⟨12869109486522118445450837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34317625297392315854535565 12869109486522118445450837)
              ·
                refine ⟨150809876795181075532627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12869109486522118445450837 150809876795181075532627)
                ·
                  rfl

theorem cell21_1982483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 8].length) (baseStart_1982483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982483 prefixEnd_1982483 := by exact prefixLift 1982483
  have htrace : WordTrace (prefixWord ++ tailWord_1982483) baseStart_1982483 baseEnd_1982483 := by
    simpa [prefixWord, tailWord_1982483, baseEnd_1982483] using wordTrace_append hprefix tailTrace_1982483
  have hstable : (prefixWord ++ tailWord_1982483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982483).length < 2 ^ (prefixWord ++ tailWord_1982483).sum := by decide
  have hdescent : baseEnd_1982483 < baseStart_1982483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982621 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1982621 : Nat := 118140960795 + 1982621 * 2 ^ 59
def prefixEnd_1982621 : Nat := 4983230072969 + 3 ^ 40 * 1982621 * 2
def baseEnd_1982621 : Nat := 452461123865685653297599

theorem tailTrace_1982621 : CollatzResearch.WordTrace tailWord_1982621 prefixEnd_1982621 452461123865685653297599 := by
  unfold tailWord_1982621
  simp only [CollatzResearch.WordTrace]
  refine ⟨72312128550310196554211717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48208085700206797702807811 72312128550310196554211717)
  ·
    refine ⟨13558524103183161853914697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72312128550310196554211717 13558524103183161853914697)
    ·
      refine ⟨10168893077387371390436023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13558524103183161853914697 10168893077387371390436023)
      ·
        refine ⟨15253339616081057085654035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10168893077387371390436023 15253339616081057085654035)
        ·
          refine ⟨22880009424121585628481053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15253339616081057085654035 22880009424121585628481053)
          ·
            refine ⟨8580003534045594610680395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22880009424121585628481053 8580003534045594610680395)
            ·
              refine ⟨12870005301068391916020593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8580003534045594610680395 12870005301068391916020593)
              ·
                refine ⟨9652503975801293937015445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12870005301068391916020593 9652503975801293937015445)
                ·
                  refine ⟨452461123865685653297599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9652503975801293937015445 452461123865685653297599)
                  ·
                    rfl

theorem cell21_1982621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1982621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982621 prefixEnd_1982621 := by exact prefixLift 1982621
  have htrace : WordTrace (prefixWord ++ tailWord_1982621) baseStart_1982621 baseEnd_1982621 := by
    simpa [prefixWord, tailWord_1982621, baseEnd_1982621] using wordTrace_append hprefix tailTrace_1982621
  have hstable : (prefixWord ++ tailWord_1982621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982621).length < 2 ^ (prefixWord ++ tailWord_1982621).sum := by decide
  have hdescent : baseEnd_1982621 < baseStart_1982621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982624 : List Nat := [2, 1, 1, 4, 2, 2, 3, 3, 3]
def baseStart_1982624 : Nat := 118140960795 + 1982624 * 2 ^ 59
def prefixEnd_1982624 : Nat := 4983230072969 + 3 ^ 40 * 1982624 * 2
def baseEnd_1982624 : Nat := 452461808506558314747593

theorem tailTrace_1982624 : CollatzResearch.WordTrace tailWord_1982624 prefixEnd_1982624 452461808506558314747593 := by
  unfold tailWord_1982624
  simp only [CollatzResearch.WordTrace]
  refine ⟨36156118984649664033285463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48208158646199552044380617 36156118984649664033285463)
  ·
    refine ⟨54234178476974496049928195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36156118984649664033285463 54234178476974496049928195)
    ·
      refine ⟨81351267715461744074892293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54234178476974496049928195 81351267715461744074892293)
      ·
        refine ⟨15253362696649077014042305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81351267715461744074892293 15253362696649077014042305)
        ·
          refine ⟨11440022022486807760531729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15253362696649077014042305 11440022022486807760531729)
          ·
            refine ⟨8580016516865105820398797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11440022022486807760531729 8580016516865105820398797)
            ·
              refine ⟨3217506193824414682649549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8580016516865105820398797 3217506193824414682649549)
              ·
                refine ⟨1206564822684155505993581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3217506193824414682649549 1206564822684155505993581)
                ·
                  refine ⟨452461808506558314747593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206564822684155505993581 452461808506558314747593)
                  ·
                    rfl

theorem cell21_1982624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 3].length) (baseStart_1982624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982624 prefixEnd_1982624 := by exact prefixLift 1982624
  have htrace : WordTrace (prefixWord ++ tailWord_1982624) baseStart_1982624 baseEnd_1982624 := by
    simpa [prefixWord, tailWord_1982624, baseEnd_1982624] using wordTrace_append hprefix tailTrace_1982624
  have hstable : (prefixWord ++ tailWord_1982624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982624).length < 2 ^ (prefixWord ++ tailWord_1982624).sum := by decide
  have hdescent : baseEnd_1982624 < baseStart_1982624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982641 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 5]
def baseStart_1982641 : Nat := 118140960795 + 1982641 * 2 ^ 59
def prefixEnd_1982641 : Nat := 4983230072969 + 3 ^ 40 * 1982641 * 2
def baseEnd_1982641 : Nat := 452465688138170062964225

theorem tailTrace_1982641 : CollatzResearch.WordTrace tailWord_1982641 prefixEnd_1982641 452465688138170062964225 := by
  unfold tailWord_1982641
  simp only [CollatzResearch.WordTrace]
  refine ⟨72312858010237739969939777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48208572006825159979959851 72312858010237739969939777)
  ·
    refine ⟨54234643507678304977454833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72312858010237739969939777 54234643507678304977454833)
    ·
      refine ⟨40675982630758728733091125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54234643507678304977454833 40675982630758728733091125)
      ·
        refine ⟨3813373371633630818727293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40675982630758728733091125 3813373371633630818727293)
        ·
          refine ⟨1430015014362611557022735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3813373371633630818727293 1430015014362611557022735)
          ·
            refine ⟨2145022521543917335534103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430015014362611557022735 2145022521543917335534103)
            ·
              refine ⟨3217533782315876003301155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145022521543917335534103 3217533782315876003301155)
              ·
                refine ⟨4826300673473814004951733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217533782315876003301155 4826300673473814004951733)
                ·
                  refine ⟨452465688138170062964225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4826300673473814004951733 452465688138170062964225)
                  ·
                    rfl

theorem cell21_1982641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 5].length) (baseStart_1982641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982641 prefixEnd_1982641 := by exact prefixLift 1982641
  have htrace : WordTrace (prefixWord ++ tailWord_1982641) baseStart_1982641 baseEnd_1982641 := by
    simpa [prefixWord, tailWord_1982641, baseEnd_1982641] using wordTrace_append hprefix tailTrace_1982641
  have hstable : (prefixWord ++ tailWord_1982641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982641).length < 2 ^ (prefixWord ++ tailWord_1982641).sum := by decide
  have hdescent : baseEnd_1982641 < baseStart_1982641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982666 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_1982666 : Nat := 118140960795 + 1982666 * 2 ^ 59
def prefixEnd_1982666 : Nat := 4983230072969 + 3 ^ 40 * 1982666 * 2
def baseEnd_1982666 : Nat := 452471393478775575047507

theorem tailTrace_1982666 : CollatzResearch.WordTrace tailWord_1982666 prefixEnd_1982666 452471393478775575047507 := by
  unfold tailWord_1982666
  simp only [CollatzResearch.WordTrace]
  refine ⟨18078442458786792309899963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48209179890098112826399901 18078442458786792309899963)
  ·
    refine ⟨27117663688180188464849945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18078442458786792309899963 27117663688180188464849945)
    ·
      refine ⟨20338247766135141348637459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27117663688180188464849945 20338247766135141348637459)
      ·
        refine ⟨30507371649202712022956189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20338247766135141348637459 30507371649202712022956189)
        ·
          refine ⟨11440264368451017008608571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30507371649202712022956189 11440264368451017008608571)
          ·
            refine ⟨17160396552676525512912857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11440264368451017008608571 17160396552676525512912857)
            ·
              refine ⟨12870297414507394134684643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17160396552676525512912857 12870297414507394134684643)
              ·
                refine ⟨19305446121761091202026965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12870297414507394134684643 19305446121761091202026965)
                ·
                  refine ⟨452471393478775575047507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19305446121761091202026965 452471393478775575047507)
                  ·
                    rfl

theorem cell21_1982666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_1982666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982666 prefixEnd_1982666 := by exact prefixLift 1982666
  have htrace : WordTrace (prefixWord ++ tailWord_1982666) baseStart_1982666 baseEnd_1982666 := by
    simpa [prefixWord, tailWord_1982666, baseEnd_1982666] using wordTrace_append hprefix tailTrace_1982666
  have hstable : (prefixWord ++ tailWord_1982666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982666).length < 2 ^ (prefixWord ++ tailWord_1982666).sum := by decide
  have hdescent : baseEnd_1982666 < baseStart_1982666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982804 : List Nat := [2, 4, 1, 1, 2, 4, 7]
def baseStart_1982804 : Nat := 118140960795 + 1982804 * 2 ^ 59
def prefixEnd_1982804 : Nat := 4983230072969 + 3 ^ 40 * 1982804 * 2
def baseEnd_1982804 : Nat := 50278098550990889083025

theorem tailTrace_1982804 : CollatzResearch.WordTrace tailWord_1982804 prefixEnd_1982804 50278098550990889083025 := by
  unfold tailWord_1982804
  simp only [CollatzResearch.WordTrace]
  refine ⟨36159401554323609404061733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48212535405764812538748977 36159401554323609404061733)
  ·
    refine ⟨6779887791435676763261575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36159401554323609404061733 6779887791435676763261575)
    ·
      refine ⟨10169831687153515144892363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6779887791435676763261575 10169831687153515144892363)
      ·
        refine ⟨15254747530730272717338545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10169831687153515144892363 15254747530730272717338545)
        ·
          refine ⟨11441060648047704538003909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15254747530730272717338545 11441060648047704538003909)
          ·
            refine ⟨2145198871508944600875733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11441060648047704538003909 2145198871508944600875733)
            ·
              refine ⟨50278098550990889083025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2145198871508944600875733 50278098550990889083025)
              ·
                rfl

theorem cell21_1982804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 7].length) (baseStart_1982804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982804 prefixEnd_1982804 := by exact prefixLift 1982804
  have htrace : WordTrace (prefixWord ++ tailWord_1982804) baseStart_1982804 baseEnd_1982804 := by
    simpa [prefixWord, tailWord_1982804, baseEnd_1982804] using wordTrace_append hprefix tailTrace_1982804
  have hstable : (prefixWord ++ tailWord_1982804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982804).length < 2 ^ (prefixWord ++ tailWord_1982804).sum := by decide
  have hdescent : baseEnd_1982804 < baseStart_1982804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982880 : List Nat := [2, 1, 1, 4, 1, 5, 1, 6]
def baseStart_1982880 : Nat := 118140960795 + 1982880 * 2 ^ 59
def prefixEnd_1982880 : Nat := 4983230072969 + 3 ^ 40 * 1982880 * 2
def baseEnd_1982880 : Nat := 150840077064786252826801

theorem tailTrace_1982880 : CollatzResearch.WordTrace tailWord_1982880 prefixEnd_1982880 150840077064786252826801 := by
  unfold tailWord_1982880
  simp only [CollatzResearch.WordTrace]
  refine ⟨36160787528185941893945047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48214383370914589191926729 36160787528185941893945047)
  ·
    refine ⟨54241181292278912840917571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36160787528185941893945047 54241181292278912840917571)
    ·
      refine ⟨81361771938418369261376357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54241181292278912840917571 81361771938418369261376357)
      ·
        refine ⟨15255332238453444236508067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81361771938418369261376357 15255332238453444236508067)
        ·
          refine ⟨22882998357680166354762101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15255332238453444236508067 22882998357680166354762101)
          ·
            refine ⟨2145281096032515595758947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22882998357680166354762101 2145281096032515595758947)
            ·
              refine ⟨3217921644048773393638421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145281096032515595758947 3217921644048773393638421)
              ·
                refine ⟨150840077064786252826801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3217921644048773393638421 150840077064786252826801)
                ·
                  rfl

theorem cell21_1982880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_1982880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982880 prefixEnd_1982880 := by exact prefixLift 1982880
  have htrace : WordTrace (prefixWord ++ tailWord_1982880) baseStart_1982880 baseEnd_1982880 := by
    simpa [prefixWord, tailWord_1982880, baseEnd_1982880] using wordTrace_append hprefix tailTrace_1982880
  have hstable : (prefixWord ++ tailWord_1982880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982880).length < 2 ^ (prefixWord ++ tailWord_1982880).sum := by decide
  have hdescent : baseEnd_1982880 < baseStart_1982880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982953 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 7]
def baseStart_1982953 : Nat := 118140960795 + 1982953 * 2 ^ 59
def prefixEnd_1982953 : Nat := 4983230072969 + 3 ^ 40 * 1982953 * 2
def baseEnd_1982953 : Nat := 452536890788926853763587

theorem tailTrace_1982953 : CollatzResearch.WordTrace tailWord_1982953 prefixEnd_1982953 452536890788926853763587 := by
  unfold tailWord_1982953
  simp only [CollatzResearch.WordTrace]
  refine ⟨72324237585107417255297513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48216158390071611503531675 72324237585107417255297513)
  ·
    refine ⟨54243178188830562941473135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72324237585107417255297513 54243178188830562941473135)
    ·
      refine ⟨81364767283245844412209703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54243178188830562941473135 81364767283245844412209703)
      ·
        refine ⟨122047150924868766618314555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81364767283245844412209703 122047150924868766618314555)
        ·
          refine ⟨183070726387303149927471833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122047150924868766618314555 183070726387303149927471833)
          ·
            refine ⟨137303044790477362445603875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183070726387303149927471833 137303044790477362445603875)
            ·
              refine ⟨205954567185716043668405813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137303044790477362445603875 205954567185716043668405813)
              ·
                refine ⟨19308240673660879093913045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205954567185716043668405813 19308240673660879093913045)
                ·
                  refine ⟨452536890788926853763587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19308240673660879093913045 452536890788926853763587)
                  ·
                    rfl

theorem cell21_1982953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_1982953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982953 prefixEnd_1982953 := by exact prefixLift 1982953
  have htrace : WordTrace (prefixWord ++ tailWord_1982953) baseStart_1982953 baseEnd_1982953 := by
    simpa [prefixWord, tailWord_1982953, baseEnd_1982953] using wordTrace_append hprefix tailTrace_1982953
  have hstable : (prefixWord ++ tailWord_1982953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982953).length < 2 ^ (prefixWord ++ tailWord_1982953).sum := by decide
  have hdescent : baseEnd_1982953 < baseStart_1982953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982962 : List Nat := [3, 2, 1, 4, 3, 1, 1, 3, 3]
def baseStart_1982962 : Nat := 118140960795 + 1982962 * 2 ^ 59
def prefixEnd_1982962 : Nat := 4983230072969 + 3 ^ 40 * 1982962 * 2
def baseEnd_1982962 : Nat := 452538944711544838113569

theorem tailTrace_1982962 : CollatzResearch.WordTrace tailWord_1982962 prefixEnd_1982962 452538944711544838113569 := by
  unfold tailWord_1982962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18081141460518702948093785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48216377228049874528250093 18081141460518702948093785)
  ·
    refine ⟨13560856095389027211070339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18081141460518702948093785 13560856095389027211070339)
    ·
      refine ⟨20341284143083540816605509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13560856095389027211070339 20341284143083540816605509)
      ·
        refine ⟨3813990776828163903113533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20341284143083540816605509 3813990776828163903113533)
        ·
          refine ⟨1430246541310561463667575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3813990776828163903113533 1430246541310561463667575)
          ·
            refine ⟨2145369811965842195501363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430246541310561463667575 2145369811965842195501363)
            ·
              refine ⟨3218054717948763293252045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145369811965842195501363 3218054717948763293252045)
              ·
                refine ⟨1206770519230786234969517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3218054717948763293252045 1206770519230786234969517)
                ·
                  refine ⟨452538944711544838113569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206770519230786234969517 452538944711544838113569)
                  ·
                    rfl

theorem cell21_1982962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_1982962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982962 prefixEnd_1982962 := by exact prefixLift 1982962
  have htrace : WordTrace (prefixWord ++ tailWord_1982962) baseStart_1982962 baseEnd_1982962 := by
    simpa [prefixWord, tailWord_1982962, baseEnd_1982962] using wordTrace_append hprefix tailTrace_1982962
  have hstable : (prefixWord ++ tailWord_1982962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982962).length < 2 ^ (prefixWord ++ tailWord_1982962).sum := by decide
  have hdescent : baseEnd_1982962 < baseStart_1982962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982987 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 5]
def baseStart_1982987 : Nat := 118140960795 + 1982987 * 2 ^ 59
def prefixEnd_1982987 : Nat := 4983230072969 + 3 ^ 40 * 1982987 * 2
def baseEnd_1982987 : Nat := 452544650052150350196851

theorem tailTrace_1982987 : CollatzResearch.WordTrace tailWord_1982987 prefixEnd_1982987 452544650052150350196851 := by
  unfold tailWord_1982987
  simp only [CollatzResearch.WordTrace]
  refine ⟨72325477666984241062035215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48216985111322827374690143 72325477666984241062035215)
  ·
    refine ⟨108488216500476361593052823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72325477666984241062035215 108488216500476361593052823)
    ·
      refine ⟨162732324750714542389579235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108488216500476361593052823 162732324750714542389579235)
      ·
        refine ⟨244098487126071813584368853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162732324750714542389579235 244098487126071813584368853)
        ·
          refine ⟨5721058292017308130883645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 244098487126071813584368853 5721058292017308130883645)
          ·
            refine ⟨2145396859506490549081367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5721058292017308130883645 2145396859506490549081367)
            ·
              refine ⟨3218095289259735823622051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145396859506490549081367 3218095289259735823622051)
              ·
                refine ⟨4827142933889603735433077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218095289259735823622051 4827142933889603735433077)
                ·
                  refine ⟨452544650052150350196851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4827142933889603735433077 452544650052150350196851)
                  ·
                    rfl

theorem cell21_1982987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 5].length) (baseStart_1982987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1982987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1982987 prefixEnd_1982987 := by exact prefixLift 1982987
  have htrace : WordTrace (prefixWord ++ tailWord_1982987) baseStart_1982987 baseEnd_1982987 := by
    simpa [prefixWord, tailWord_1982987, baseEnd_1982987] using wordTrace_append hprefix tailTrace_1982987
  have hstable : (prefixWord ++ tailWord_1982987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982987).length < 2 ^ (prefixWord ++ tailWord_1982987).sum := by decide
  have hdescent : baseEnd_1982987 < baseStart_1982987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983094 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1983094 : Nat := 118140960795 + 1983094 * 2 ^ 59
def prefixEnd_1983094 : Nat := 4983230072969 + 3 ^ 40 * 1983094 * 2
def baseEnd_1983094 : Nat := 452569068909941941913299

theorem tailTrace_1983094 : CollatzResearch.WordTrace tailWord_1983094 prefixEnd_1983094 452569068909941941913299 := by
  unfold tailWord_1983094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4520586267349787396011271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48219586851731065557453557 4520586267349787396011271)
  ·
    refine ⟨6780879401024681094016907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4520586267349787396011271 6780879401024681094016907)
    ·
      refine ⟨10171319101537021641025361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6780879401024681094016907 10171319101537021641025361)
      ·
        refine ⟨7628489326152766230769021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10171319101537021641025361 7628489326152766230769021)
        ·
          refine ⟨2860683497307287336538383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7628489326152766230769021 2860683497307287336538383)
          ·
            refine ⟨4291025245960931004807575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860683497307287336538383 4291025245960931004807575)
            ·
              refine ⟨6436537868941396507211363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4291025245960931004807575 6436537868941396507211363)
              ·
                refine ⟨9654806803412094760817045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6436537868941396507211363 9654806803412094760817045)
                ·
                  refine ⟨452569068909941941913299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9654806803412094760817045 452569068909941941913299)
                  ·
                    rfl

theorem cell21_1983094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1983094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983094 prefixEnd_1983094 := by exact prefixLift 1983094
  have htrace : WordTrace (prefixWord ++ tailWord_1983094) baseStart_1983094 baseEnd_1983094 := by
    simpa [prefixWord, tailWord_1983094, baseEnd_1983094] using wordTrace_append hprefix tailTrace_1983094
  have hstable : (prefixWord ++ tailWord_1983094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983094).length < 2 ^ (prefixWord ++ tailWord_1983094).sum := by decide
  have hdescent : baseEnd_1983094 < baseStart_1983094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983167 : List Nat := [1, 1, 2, 2, 2, 5, 2, 6]
def baseStart_1983167 : Nat := 118140960795 + 1983167 * 2 ^ 59
def prefixEnd_1983167 : Nat := 4983230072969 + 3 ^ 40 * 1983167 * 2
def baseEnd_1983167 : Nat := 150861909501503345732161

theorem tailTrace_1983167 : CollatzResearch.WordTrace tailWord_1983167 prefixEnd_1983167 150861909501503345732161 := by
  unfold tailWord_1983167
  simp only [CollatzResearch.WordTrace]
  refine ⟨72332042806332131803587755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48221361870888087869058503 72332042806332131803587755)
  ·
    refine ⟨108498064209498197705381633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72332042806332131803587755 108498064209498197705381633)
    ·
      refine ⟨81373548157123648279036225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108498064209498197705381633 81373548157123648279036225)
      ·
        refine ⟨61030161117842736209277169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81373548157123648279036225 61030161117842736209277169)
        ·
          refine ⟨45772620838382052156957877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61030161117842736209277169 45772620838382052156957877)
          ·
            refine ⟨4291183203598317389714801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45772620838382052156957877 4291183203598317389714801)
            ·
              refine ⟨3218387402698738042286101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4291183203598317389714801 3218387402698738042286101)
              ·
                refine ⟨150861909501503345732161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3218387402698738042286101 150861909501503345732161)
                ·
                  rfl

theorem cell21_1983167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 6].length) (baseStart_1983167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983167 prefixEnd_1983167 := by exact prefixLift 1983167
  have htrace : WordTrace (prefixWord ++ tailWord_1983167) baseStart_1983167 baseEnd_1983167 := by
    simpa [prefixWord, tailWord_1983167, baseEnd_1983167] using wordTrace_append hprefix tailTrace_1983167
  have hstable : (prefixWord ++ tailWord_1983167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983167).length < 2 ^ (prefixWord ++ tailWord_1983167).sum := by decide
  have hdescent : baseEnd_1983167 < baseStart_1983167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983215 : List Nat := [1, 1, 2, 1, 5, 3, 1, 4, 3]
def baseStart_1983215 : Nat := 118140960795 + 1983215 * 2 ^ 59
def prefixEnd_1983215 : Nat := 4983230072969 + 3 ^ 40 * 1983215 * 2
def baseEnd_1983215 : Nat := 452596682758472620396385

theorem tailTrace_1983215 : CollatzResearch.WordTrace tailWord_1983215 prefixEnd_1983215 452596682758472620396385 := by
  unfold tailWord_1983215
  simp only [CollatzResearch.WordTrace]
  refine ⟨72333793510158236001335099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48222529006772157334223399 72333793510158236001335099)
  ·
    refine ⟨108500690265237354002002649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72333793510158236001335099 108500690265237354002002649)
    ·
      refine ⟨81375517698928015501501987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108500690265237354002002649 81375517698928015501501987)
      ·
        refine ⟨122063276548392023252252981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81375517698928015501501987 122063276548392023252252981)
        ·
          refine ⟨11443432176411752179898717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122063276548392023252252981 11443432176411752179898717)
          ·
            refine ⟨4291287066154407067462019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11443432176411752179898717 4291287066154407067462019)
            ·
              refine ⟨6436930599231610601193029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4291287066154407067462019 6436930599231610601193029)
              ·
                refine ⟨1206924487355926987723693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6436930599231610601193029 1206924487355926987723693)
                ·
                  refine ⟨452596682758472620396385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206924487355926987723693 452596682758472620396385)
                  ·
                    rfl

theorem cell21_1983215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 3].length) (baseStart_1983215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983215 prefixEnd_1983215 := by exact prefixLift 1983215
  have htrace : WordTrace (prefixWord ++ tailWord_1983215) baseStart_1983215 baseEnd_1983215 := by
    simpa [prefixWord, tailWord_1983215, baseEnd_1983215] using wordTrace_append hprefix tailTrace_1983215
  have hstable : (prefixWord ++ tailWord_1983215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983215).length < 2 ^ (prefixWord ++ tailWord_1983215).sum := by decide
  have hdescent : baseEnd_1983215 < baseStart_1983215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983294 : List Nat := [4, 2, 1, 2, 4, 1, 2, 5]
def baseStart_1983294 : Nat := 118140960795 + 1983294 * 2 ^ 59
def prefixEnd_1983294 : Nat := 4983230072969 + 3 ^ 40 * 1983294 * 2
def baseEnd_1983294 : Nat := 150871570544928679526519

theorem tailTrace_1983294 : CollatzResearch.WordTrace tailWord_1983294 prefixEnd_1983294 150871570544928679526519 := by
  unfold tailWord_1983294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9042084359609004061682617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48224449917914688328973957 9042084359609004061682617)
  ·
    refine ⟨6781563269706753046261963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9042084359609004061682617 6781563269706753046261963)
    ·
      refine ⟨10172344904560129569392945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6781563269706753046261963 10172344904560129569392945)
      ·
        refine ⟨7629258678420097177044709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10172344904560129569392945 7629258678420097177044709)
        ·
          refine ⟨1430486002203768220695883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7629258678420097177044709 1430486002203768220695883)
          ·
            refine ⟨2145729003305652331043825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430486002203768220695883 2145729003305652331043825)
            ·
              refine ⟨1609296752479239248282869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2145729003305652331043825 1609296752479239248282869)
              ·
                refine ⟨150871570544928679526519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1609296752479239248282869 150871570544928679526519)
                ·
                  rfl

theorem cell21_1983294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_1983294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983294 prefixEnd_1983294 := by exact prefixLift 1983294
  have htrace : WordTrace (prefixWord ++ tailWord_1983294) baseStart_1983294 baseEnd_1983294 := by
    simpa [prefixWord, tailWord_1983294, baseEnd_1983294] using wordTrace_append hprefix tailTrace_1983294
  have hstable : (prefixWord ++ tailWord_1983294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983294).length < 2 ^ (prefixWord ++ tailWord_1983294).sum := by decide
  have hdescent : baseEnd_1983294 < baseStart_1983294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983308 : List Nat := [2, 2, 1, 3, 3, 3, 1, 3, 3]
def baseStart_1983308 : Nat := 118140960795 + 1983308 * 2 ^ 59
def prefixEnd_1983308 : Nat := 4983230072969 + 3 ^ 40 * 1983308 * 2
def baseEnd_1983308 : Nat := 452617906625525125346195

theorem tailTrace_1983308 : CollatzResearch.WordTrace tailWord_1983308 prefixEnd_1983308 452617906625525125346195 := by
  unfold tailWord_1983308
  simp only [CollatzResearch.WordTrace]
  refine ⟨36168592749410656442235289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48224790332547541922980385 36168592749410656442235289)
  ·
    refine ⟨27126444562057992331676467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36168592749410656442235289 27126444562057992331676467)
    ·
      refine ⟨40689666843086988497514701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27126444562057992331676467 40689666843086988497514701)
      ·
        refine ⟨15258625066157620686568013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40689666843086988497514701 15258625066157620686568013)
        ·
          refine ⟨5721984399809107757463005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15258625066157620686568013 5721984399809107757463005)
          ·
            refine ⟨2145744149928415409048627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5721984399809107757463005 2145744149928415409048627)
            ·
              refine ⟨3218616224892623113572941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145744149928415409048627 3218616224892623113572941)
              ·
                refine ⟨1206981084334733667589853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3218616224892623113572941 1206981084334733667589853)
                ·
                  refine ⟨452617906625525125346195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206981084334733667589853 452617906625525125346195)
                  ·
                    rfl

theorem cell21_1983308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_1983308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983308 prefixEnd_1983308 := by exact prefixLift 1983308
  have htrace : WordTrace (prefixWord ++ tailWord_1983308) baseStart_1983308 baseEnd_1983308 := by
    simpa [prefixWord, tailWord_1983308, baseEnd_1983308] using wordTrace_append hprefix tailTrace_1983308
  have hstable : (prefixWord ++ tailWord_1983308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983308).length < 2 ^ (prefixWord ++ tailWord_1983308).sum := by decide
  have hdescent : baseEnd_1983308 < baseStart_1983308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983319 : List Nat := [1, 1, 3, 2, 4, 3, 7]
def baseStart_1983319 : Nat := 118140960795 + 1983319 * 2 ^ 59
def prefixEnd_1983319 : Nat := 4983230072969 + 3 ^ 40 * 1983319 * 2
def baseEnd_1983319 : Nat := 50291157441710172295871

theorem tailTrace_1983319 : CollatzResearch.WordTrace tailWord_1983319 prefixEnd_1983319 50291157441710172295871 := by
  unfold tailWord_1983319
  simp only [CollatzResearch.WordTrace]
  refine ⟨72337586701781461763121011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48225057801187641175414007 72337586701781461763121011)
  ·
    refine ⟨108506380052672192644681517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72337586701781461763121011 108506380052672192644681517)
    ·
      refine ⟨40689892519752072241755569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108506380052672192644681517 40689892519752072241755569)
      ·
        refine ⟨30517419389814054181316677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40689892519752072241755569 30517419389814054181316677)
        ·
          refine ⟨5722016135590135158996877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30517419389814054181316677 5722016135590135158996877)
          ·
            refine ⟨2145756050846300684623829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5722016135590135158996877 2145756050846300684623829)
            ·
              refine ⟨50291157441710172295871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2145756050846300684623829 50291157441710172295871)
              ·
                rfl

theorem cell21_1983319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 7].length) (baseStart_1983319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983319 prefixEnd_1983319 := by exact prefixLift 1983319
  have htrace : WordTrace (prefixWord ++ tailWord_1983319) baseStart_1983319 baseEnd_1983319 := by
    simpa [prefixWord, tailWord_1983319, baseEnd_1983319] using wordTrace_append hprefix tailTrace_1983319
  have hstable : (prefixWord ++ tailWord_1983319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983319).length < 2 ^ (prefixWord ++ tailWord_1983319).sum := by decide
  have hdescent : baseEnd_1983319 < baseStart_1983319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983381 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 4]
def baseStart_1983381 : Nat := 118140960795 + 1983381 * 2 ^ 59
def prefixEnd_1983381 : Nat := 4983230072969 + 3 ^ 40 * 1983381 * 2
def baseEnd_1983381 : Nat := 452634566220093220629379

theorem tailTrace_1983381 : CollatzResearch.WordTrace tailWord_1983381 prefixEnd_1983381 452634566220093220629379 := by
  unfold tailWord_1983381
  simp only [CollatzResearch.WordTrace]
  refine ⟨72339848027556846351877997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48226565351704564234585331 72339848027556846351877997)
  ·
    refine ⟨27127443010333817381954249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72339848027556846351877997 27127443010333817381954249)
    ·
      refine ⟨20345582257750363036465687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27127443010333817381954249 20345582257750363036465687)
      ·
        refine ⟨30518373386625544554698531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20345582257750363036465687 30518373386625544554698531)
        ·
          refine ⟨45777560079938316832047797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30518373386625544554698531 45777560079938316832047797)
          ·
            refine ⟨4291646257494217203004481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45777560079938316832047797 4291646257494217203004481)
            ·
              refine ⟨3218734693120662902253361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4291646257494217203004481 3218734693120662902253361)
              ·
                refine ⟨2414051019840497176690021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218734693120662902253361 2414051019840497176690021)
                ·
                  refine ⟨452634566220093220629379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2414051019840497176690021 452634566220093220629379)
                  ·
                    rfl

theorem cell21_1983381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_1983381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983381 prefixEnd_1983381 := by exact prefixLift 1983381
  have htrace : WordTrace (prefixWord ++ tailWord_1983381) baseStart_1983381 baseEnd_1983381 := by
    simpa [prefixWord, tailWord_1983381, baseEnd_1983381] using wordTrace_append hprefix tailTrace_1983381
  have hstable : (prefixWord ++ tailWord_1983381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983381).length < 2 ^ (prefixWord ++ tailWord_1983381).sum := by decide
  have hdescent : baseEnd_1983381 < baseStart_1983381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983471 : List Nat := [1, 1, 2, 1, 4, 3, 4, 5]
def baseStart_1983471 : Nat := 118140960795 + 1983471 * 2 ^ 59
def prefixEnd_1983471 : Nat := 4983230072969 + 3 ^ 40 * 1983471 * 2
def baseEnd_1983471 : Nat := 150885035148757688043065

theorem tailTrace_1983471 : CollatzResearch.WordTrace tailWord_1983471 prefixEnd_1983471 150885035148757688043065 := by
  unfold tailWord_1983471
  simp only [CollatzResearch.WordTrace]
  refine ⟨72343130597230791722654267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48228753731487194481769511 72343130597230791722654267)
  ·
    refine ⟨108514695895846187583981401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72343130597230791722654267 108514695895846187583981401)
    ·
      refine ⟨81386021921884640687986051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108514695895846187583981401 81386021921884640687986051)
      ·
        refine ⟨122079032882826961031979077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81386021921884640687986051 122079032882826961031979077)
        ·
          refine ⟨22889818665530055193496077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122079032882826961031979077 22889818665530055193496077)
          ·
            refine ⟨8583681999573770697561029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22889818665530055193496077 8583681999573770697561029)
            ·
              refine ⟨1609440374920082005792693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8583681999573770697561029 1609440374920082005792693)
              ·
                refine ⟨150885035148757688043065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1609440374920082005792693 150885035148757688043065)
                ·
                  rfl

theorem cell21_1983471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 5].length) (baseStart_1983471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983471 prefixEnd_1983471 := by exact prefixLift 1983471
  have htrace : WordTrace (prefixWord ++ tailWord_1983471) baseStart_1983471 baseEnd_1983471 := by
    simpa [prefixWord, tailWord_1983471, baseEnd_1983471] using wordTrace_append hprefix tailTrace_1983471
  have hstable : (prefixWord ++ tailWord_1983471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983471).length < 2 ^ (prefixWord ++ tailWord_1983471).sum := by decide
  have hdescent : baseEnd_1983471 < baseStart_1983471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983502 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_1983502 : Nat := 118140960795 + 1983502 * 2 ^ 59
def prefixEnd_1983502 : Nat := 4983230072969 + 3 ^ 40 * 1983502 * 2
def baseEnd_1983502 : Nat := 452662180068623899112465

theorem tailTrace_1983502 : CollatzResearch.WordTrace tailWord_1983502 prefixEnd_1983502 452662180068623899112465 := by
  unfold tailWord_1983502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9043032657514810502129095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48229507506745656011355173 9043032657514810502129095)
  ·
    refine ⟨13564548986272215753193643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9043032657514810502129095 13564548986272215753193643)
    ·
      refine ⟨20346823479408323629790465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13564548986272215753193643 20346823479408323629790465)
      ·
        refine ⟨15260117609556242722342849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20346823479408323629790465 15260117609556242722342849)
        ·
          refine ⟨11445088207167182041757137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15260117609556242722342849 11445088207167182041757137)
          ·
            refine ⟨8583816155375386531317853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11445088207167182041757137 8583816155375386531317853)
            ·
              refine ⟨3218931058265769949244195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8583816155375386531317853 3218931058265769949244195)
              ·
                refine ⟨4828396587398654923866293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218931058265769949244195 4828396587398654923866293)
                ·
                  refine ⟨452662180068623899112465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4828396587398654923866293 452662180068623899112465)
                  ·
                    rfl

theorem cell21_1983502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_1983502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983502 prefixEnd_1983502 := by exact prefixLift 1983502
  have htrace : WordTrace (prefixWord ++ tailWord_1983502) baseStart_1983502 baseEnd_1983502 := by
    simpa [prefixWord, tailWord_1983502, baseEnd_1983502] using wordTrace_append hprefix tailTrace_1983502
  have hstable : (prefixWord ++ tailWord_1983502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983502).length < 2 ^ (prefixWord ++ tailWord_1983502).sum := by decide
  have hdescent : baseEnd_1983502 < baseStart_1983502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983550 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1983550 : Nat := 118140960795 + 1983550 * 2 ^ 59
def prefixEnd_1983550 : Nat := 4983230072969 + 3 ^ 40 * 1983550 * 2
def baseEnd_1983550 : Nat := 452673134322586482312367

theorem tailTrace_1983550 : CollatzResearch.WordTrace tailWord_1983550 prefixEnd_1983550 452673134322586482312367 := by
  unfold tailWord_1983550
  simp only [CollatzResearch.WordTrace]
  refine ⟨9043251495493073526847513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48230674642629725476520069 9043251495493073526847513)
  ·
    refine ⟨6782438621619805145135635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9043251495493073526847513 6782438621619805145135635)
    ·
      refine ⟨10173657932429707717703453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6782438621619805145135635 10173657932429707717703453)
      ·
        refine ⟨3815121724661140394138795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10173657932429707717703453 3815121724661140394138795)
        ·
          refine ⟨5722682586991710591208193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815121724661140394138795 5722682586991710591208193)
          ·
            refine ⟨4292011940243782943406145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5722682586991710591208193 4292011940243782943406145)
            ·
              refine ⟨3219008955182837207554609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4292011940243782943406145 3219008955182837207554609)
              ·
                refine ⟨2414256716387127905665957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219008955182837207554609 2414256716387127905665957)
                ·
                  refine ⟨452673134322586482312367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2414256716387127905665957 452673134322586482312367)
                  ·
                    rfl

theorem cell21_1983550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1983550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983550 prefixEnd_1983550 := by exact prefixLift 1983550
  have htrace : WordTrace (prefixWord ++ tailWord_1983550) baseStart_1983550 baseEnd_1983550 := by
    simpa [prefixWord, tailWord_1983550, baseEnd_1983550] using wordTrace_append hprefix tailTrace_1983550
  have hstable : (prefixWord ++ tailWord_1983550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983550).length < 2 ^ (prefixWord ++ tailWord_1983550).sum := by decide
  have hdescent : baseEnd_1983550 < baseStart_1983550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983553 : List Nat := [1, 2, 5, 1, 3, 2, 2, 2, 3]
def baseStart_1983553 : Nat := 118140960795 + 1983553 * 2 ^ 59
def prefixEnd_1983553 : Nat := 4983230072969 + 3 ^ 40 * 1983553 * 2
def baseEnd_1983553 : Nat := 452673818963459143762361

theorem tailTrace_1983553 : CollatzResearch.WordTrace tailWord_1983553 prefixEnd_1983553 452673818963459143762361 := by
  unfold tailWord_1983553
  simp only [CollatzResearch.WordTrace]
  refine ⟨72346121382933719727139313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48230747588622479818092875 72346121382933719727139313)
  ·
    refine ⟨54259591037200289795354485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72346121382933719727139313 54259591037200289795354485)
    ·
      refine ⟨5086836659737527168314483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54259591037200289795354485 5086836659737527168314483)
      ·
        refine ⟨7630254989606290752471725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5086836659737527168314483 7630254989606290752471725)
        ·
          refine ⟨2861345621102359032176897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7630254989606290752471725 2861345621102359032176897)
          ·
            refine ⟨2146009215826769274132673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2861345621102359032176897 2146009215826769274132673)
            ·
              refine ⟨1609506911870076955599505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2146009215826769274132673 1609506911870076955599505)
              ·
                refine ⟨1207130183902557716699629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609506911870076955599505 1207130183902557716699629)
                ·
                  refine ⟨452673818963459143762361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207130183902557716699629 452673818963459143762361)
                  ·
                    rfl

theorem cell21_1983553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 3].length) (baseStart_1983553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983553 prefixEnd_1983553 := by exact prefixLift 1983553
  have htrace : WordTrace (prefixWord ++ tailWord_1983553) baseStart_1983553 baseEnd_1983553 := by
    simpa [prefixWord, tailWord_1983553, baseEnd_1983553] using wordTrace_append hprefix tailTrace_1983553
  have hstable : (prefixWord ++ tailWord_1983553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983553).length < 2 ^ (prefixWord ++ tailWord_1983553).sum := by decide
  have hdescent : baseEnd_1983553 < baseStart_1983553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983575 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 8]
def baseStart_1983575 : Nat := 118140960795 + 1983575 * 2 ^ 59
def prefixEnd_1983575 : Nat := 4983230072969 + 3 ^ 40 * 1983575 * 2
def baseEnd_1983575 : Nat := 452678839663191994395649

theorem tailTrace_1983575 : CollatzResearch.WordTrace tailWord_1983575 prefixEnd_1983575 452678839663191994395649 := by
  unfold tailWord_1983575
  simp only [CollatzResearch.WordTrace]
  refine ⟨72346923788854017484440179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48231282525902678322960119 72346923788854017484440179)
  ·
    refine ⟨108520385683281026226660269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72346923788854017484440179 108520385683281026226660269)
    ·
      refine ⟨40695144631230384834997601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108520385683281026226660269 40695144631230384834997601)
      ·
        refine ⟨30521358473422788626248201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40695144631230384834997601 30521358473422788626248201)
        ·
          refine ⟨22891018855067091469686151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30521358473422788626248201 22891018855067091469686151)
          ·
            refine ⟨34336528282600637204529227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22891018855067091469686151 34336528282600637204529227)
            ·
              refine ⟨51504792423900955806793841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34336528282600637204529227 51504792423900955806793841)
              ·
                refine ⟨38628594317925716855095381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51504792423900955806793841 38628594317925716855095381)
                ·
                  refine ⟨452678839663191994395649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38628594317925716855095381 452678839663191994395649)
                  ·
                    rfl

theorem cell21_1983575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_1983575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983575 prefixEnd_1983575 := by exact prefixLift 1983575
  have htrace : WordTrace (prefixWord ++ tailWord_1983575) baseStart_1983575 baseEnd_1983575 := by
    simpa [prefixWord, tailWord_1983575, baseEnd_1983575] using wordTrace_append hprefix tailTrace_1983575
  have hstable : (prefixWord ++ tailWord_1983575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983575).length < 2 ^ (prefixWord ++ tailWord_1983575).sum := by decide
  have hdescent : baseEnd_1983575 < baseStart_1983575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983581 : List Nat := [1, 4, 4, 1, 2, 1, 3, 5]
def baseStart_1983581 : Nat := 118140960795 + 1983581 * 2 ^ 59
def prefixEnd_1983581 : Nat := 4983230072969 + 3 ^ 40 * 1983581 * 2
def baseEnd_1983581 : Nat := 150893402981645772431879

theorem tailTrace_1983581 : CollatzResearch.WordTrace tailWord_1983581 prefixEnd_1983581 150893402981645772431879 := by
  unfold tailWord_1983581
  simp only [CollatzResearch.WordTrace]
  refine ⟨72347142626832280509158597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48231428417888187006105731 72347142626832280509158597)
  ·
    refine ⟨13565089242531052595467237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72347142626832280509158597 13565089242531052595467237)
    ·
      refine ⟨2543454232974572361650107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13565089242531052595467237 2543454232974572361650107)
      ·
        refine ⟨3815181349461858542475161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543454232974572361650107 3815181349461858542475161)
        ·
          refine ⟨2861386012096393906856371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3815181349461858542475161 2861386012096393906856371)
          ·
            refine ⟨4292079018144590860284557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861386012096393906856371 4292079018144590860284557)
            ·
              refine ⟨1609529631804221572606709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4292079018144590860284557 1609529631804221572606709)
              ·
                refine ⟨150893402981645772431879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1609529631804221572606709 150893402981645772431879)
                ·
                  rfl

theorem cell21_1983581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 5].length) (baseStart_1983581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983581 prefixEnd_1983581 := by exact prefixLift 1983581
  have htrace : WordTrace (prefixWord ++ tailWord_1983581) baseStart_1983581 baseEnd_1983581 := by
    simpa [prefixWord, tailWord_1983581, baseEnd_1983581] using wordTrace_append hprefix tailTrace_1983581
  have hstable : (prefixWord ++ tailWord_1983581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983581).length < 2 ^ (prefixWord ++ tailWord_1983581).sum := by decide
  have hdescent : baseEnd_1983581 < baseStart_1983581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983640 : List Nat := [2, 1, 2, 4, 2, 3, 2, 5]
def baseStart_1983640 : Nat := 118140960795 + 1983640 * 2 ^ 59
def prefixEnd_1983640 : Nat := 4983230072969 + 3 ^ 40 * 1983640 * 2
def baseEnd_1983640 : Nat := 150897891182922108604061

theorem tailTrace_1983640 : CollatzResearch.WordTrace tailWord_1983640 prefixEnd_1983640 150897891182922108604061 := by
  unfold tailWord_1983640
  simp only [CollatzResearch.WordTrace]
  refine ⟨36174647266809266792778187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48232863022412355723704249 36174647266809266792778187)
  ·
    refine ⟨54261970900213900189167281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36174647266809266792778187 54261970900213900189167281)
    ·
      refine ⟨40696478175160425141875461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54261970900213900189167281 40696478175160425141875461)
      ·
        refine ⟨7630589657842579714101649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40696478175160425141875461 7630589657842579714101649)
        ·
          refine ⟨5722942243381934785576237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7630589657842579714101649 5722942243381934785576237)
          ·
            refine ⟨2146103341268225544591089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5722942243381934785576237 2146103341268225544591089)
            ·
              refine ⟨1609577505951169158443317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2146103341268225544591089 1609577505951169158443317)
              ·
                refine ⟨150897891182922108604061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1609577505951169158443317 150897891182922108604061)
                ·
                  rfl

theorem cell21_1983640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_1983640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983640 prefixEnd_1983640 := by exact prefixLift 1983640
  have htrace : WordTrace (prefixWord ++ tailWord_1983640) baseStart_1983640 baseEnd_1983640 := by
    simpa [prefixWord, tailWord_1983640, baseEnd_1983640] using wordTrace_append hprefix tailTrace_1983640
  have hstable : (prefixWord ++ tailWord_1983640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983640).length < 2 ^ (prefixWord ++ tailWord_1983640).sum := by decide
  have hdescent : baseEnd_1983640 < baseStart_1983640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983671 : List Nat := [1, 1, 3, 1, 4, 1, 5, 2, 3]
def baseStart_1983671 : Nat := 118140960795 + 1983671 * 2 ^ 59
def prefixEnd_1983671 : Nat := 4983230072969 + 3 ^ 40 * 1983671 * 2
def baseEnd_1983671 : Nat := 452700748171117160795453

theorem tailTrace_1983671 : CollatzResearch.WordTrace tailWord_1983671 prefixEnd_1983671 452700748171117160795453 := by
  unfold tailWord_1983671
  simp only [CollatzResearch.WordTrace]
  refine ⟨72350425196506225879934867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48233616797670817253289911 72350425196506225879934867)
  ·
    refine ⟨108525637794759338819902301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72350425196506225879934867 108525637794759338819902301)
    ·
      refine ⟨40697114173034752057463363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108525637794759338819902301 40697114173034752057463363)
      ·
        refine ⟨61045671259552128086195045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40697114173034752057463363 61045671259552128086195045)
        ·
          refine ⟨11446063361166024016161571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61045671259552128086195045 11446063361166024016161571)
          ·
            refine ⟨17169095041749036024242357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11446063361166024016161571 17169095041749036024242357)
            ·
              refine ⟨1609602660163972127272721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17169095041749036024242357 1609602660163972127272721)
              ·
                refine ⟨1207201995122979095454541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609602660163972127272721 1207201995122979095454541)
                ·
                  refine ⟨452700748171117160795453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207201995122979095454541 452700748171117160795453)
                  ·
                    rfl

theorem cell21_1983671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 3].length) (baseStart_1983671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983671 prefixEnd_1983671 := by exact prefixLift 1983671
  have htrace : WordTrace (prefixWord ++ tailWord_1983671) baseStart_1983671 baseEnd_1983671 := by
    simpa [prefixWord, tailWord_1983671, baseEnd_1983671] using wordTrace_append hprefix tailTrace_1983671
  have hstable : (prefixWord ++ tailWord_1983671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983671).length < 2 ^ (prefixWord ++ tailWord_1983671).sum := by decide
  have hdescent : baseEnd_1983671 < baseStart_1983671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983778 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1983778 : Nat := 118140960795 + 1983778 * 2 ^ 59
def prefixEnd_1983778 : Nat := 4983230072969 + 3 ^ 40 * 1983778 * 2
def baseEnd_1983778 : Nat := 452725167028908752511901

theorem tailTrace_1983778 : CollatzResearch.WordTrace tailWord_1983778 prefixEnd_1983778 452725167028908752511901 := by
  unfold tailWord_1983778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18088581951779645788519997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48236218538079055436053325 18088581951779645788519997)
  ·
    refine ⟨6783218231917367170694999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18088581951779645788519997 6783218231917367170694999)
    ·
      refine ⟨10174827347876050756042499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6783218231917367170694999 10174827347876050756042499)
      ·
        refine ⟨15262241021814076134063749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174827347876050756042499 15262241021814076134063749)
        ·
          refine ⟨2861670191590139275136953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15262241021814076134063749 2861670191590139275136953)
          ·
            refine ⟨2146252643692604456352715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2861670191590139275136953 2146252643692604456352715)
            ·
              refine ⟨3219378965538906684529073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146252643692604456352715 3219378965538906684529073)
              ·
                refine ⟨2414534224154180013396805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219378965538906684529073 2414534224154180013396805)
                ·
                  refine ⟨452725167028908752511901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2414534224154180013396805 452725167028908752511901)
                  ·
                    rfl

theorem cell21_1983778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1983778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983778 prefixEnd_1983778 := by exact prefixLift 1983778
  have htrace : WordTrace (prefixWord ++ tailWord_1983778) baseStart_1983778 baseEnd_1983778 := by
    simpa [prefixWord, tailWord_1983778, baseEnd_1983778] using wordTrace_append hprefix tailTrace_1983778
  have hstable : (prefixWord ++ tailWord_1983778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983778).length < 2 ^ (prefixWord ++ tailWord_1983778).sum := by decide
  have hdescent : baseEnd_1983778 < baseStart_1983778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983854 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_1983854 : Nat := 118140960795 + 1983854 * 2 ^ 59
def prefixEnd_1983854 : Nat := 4983230072969 + 3 ^ 40 * 1983854 * 2
def baseEnd_1983854 : Nat := 452742511264349509245079

theorem tailTrace_1983854 : CollatzResearch.WordTrace tailWord_1983854 prefixEnd_1983854 452742511264349509245079 := by
  unfold tailWord_1983854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9044637469355406016730827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48238066503228832089231077 9044637469355406016730827)
  ·
    refine ⟨13566956204033109025096241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9044637469355406016730827 13566956204033109025096241)
    ·
      refine ⟨10175217153024831768822181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13566956204033109025096241 10175217153024831768822181)
      ·
        refine ⟨1907853216192155956654159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10175217153024831768822181 1907853216192155956654159)
        ·
          refine ⟨2861779824288233934981239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907853216192155956654159 2861779824288233934981239)
          ·
            refine ⟨4292669736432350902471859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861779824288233934981239 4292669736432350902471859)
            ·
              refine ⟨6439004604648526353707789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4292669736432350902471859 6439004604648526353707789)
              ·
                refine ⟨2414626726743197382640421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6439004604648526353707789 2414626726743197382640421)
                ·
                  refine ⟨452742511264349509245079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2414626726743197382640421 452742511264349509245079)
                  ·
                    rfl

theorem cell21_1983854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_1983854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983854 prefixEnd_1983854 := by exact prefixLift 1983854
  have htrace : WordTrace (prefixWord ++ tailWord_1983854) baseStart_1983854 baseEnd_1983854 := by
    simpa [prefixWord, tailWord_1983854, baseEnd_1983854] using wordTrace_append hprefix tailTrace_1983854
  have hstable : (prefixWord ++ tailWord_1983854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983854).length < 2 ^ (prefixWord ++ tailWord_1983854).sum := by decide
  have hdescent : baseEnd_1983854 < baseStart_1983854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983958 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1983958 : Nat := 118140960795 + 1983958 * 2 ^ 59
def prefixEnd_1983958 : Nat := 4983230072969 + 3 ^ 40 * 1983958 * 2
def baseEnd_1983958 : Nat := 452766245481268439511533

theorem tailTrace_1983958 : CollatzResearch.WordTrace tailWord_1983958 prefixEnd_1983958 452766245481268439511533 := by
  unfold tailWord_1983958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522555809154154618477033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48240595297644315930421685 4522555809154154618477033)
  ·
    refine ⟨3391916856865615963857775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4522555809154154618477033 3391916856865615963857775)
    ·
      refine ⟨5087875285298423945786663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3391916856865615963857775 5087875285298423945786663)
      ·
        refine ⟨7631812927947635918679995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5087875285298423945786663 7631812927947635918679995)
        ·
          refine ⟨11447719391921453878019993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7631812927947635918679995 11447719391921453878019993)
          ·
            refine ⟨8585789543941090408514995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11447719391921453878019993 8585789543941090408514995)
            ·
              refine ⟨12878684315911635612772493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585789543941090408514995 12878684315911635612772493)
              ·
                refine ⟨4829506618466863354789685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12878684315911635612772493 4829506618466863354789685)
                ·
                  refine ⟨452766245481268439511533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4829506618466863354789685 452766245481268439511533)
                  ·
                    rfl

theorem cell21_1983958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1983958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1983958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1983958 prefixEnd_1983958 := by exact prefixLift 1983958
  have htrace : WordTrace (prefixWord ++ tailWord_1983958) baseStart_1983958 baseEnd_1983958 := by
    simpa [prefixWord, tailWord_1983958, baseEnd_1983958] using wordTrace_append hprefix tailTrace_1983958
  have hstable : (prefixWord ++ tailWord_1983958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983958).length < 2 ^ (prefixWord ++ tailWord_1983958).sum := by decide
  have hdescent : baseEnd_1983958 < baseStart_1983958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984020 : List Nat := [2, 4, 3, 1, 2, 1, 2, 6]
def baseStart_1984020 : Nat := 118140960795 + 1984020 * 2 ^ 59
def prefixEnd_1984020 : Nat := 4983230072969 + 3 ^ 40 * 1984020 * 2
def baseEnd_1984020 : Nat := 150926798241990036492691

theorem tailTrace_1984020 : CollatzResearch.WordTrace tailWord_1984020 prefixEnd_1984020 150926798241990036492691 := by
  unfold tailWord_1984020
  simp only [CollatzResearch.WordTrace]
  refine ⟨36181577136120929242194757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48242102848161238989593009 36181577136120929242194757)
  ·
    refine ⟨6784045713022674232911517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36181577136120929242194757 6784045713022674232911517)
    ·
      refine ⟨2544017142383502837341819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6784045713022674232911517 2544017142383502837341819)
      ·
        refine ⟨3816025713575254256012729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2544017142383502837341819 3816025713575254256012729)
        ·
          refine ⟨2862019285181440692009547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3816025713575254256012729 2862019285181440692009547)
          ·
            refine ⟨4293028927772161038014321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862019285181440692009547 4293028927772161038014321)
            ·
              refine ⟨3219771695829120778510741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4293028927772161038014321 3219771695829120778510741)
              ·
                refine ⟨150926798241990036492691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3219771695829120778510741 150926798241990036492691)
                ·
                  rfl

theorem cell21_1984020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_1984020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984020 prefixEnd_1984020 := by exact prefixLift 1984020
  have htrace : WordTrace (prefixWord ++ tailWord_1984020) baseStart_1984020 baseEnd_1984020 := by
    simpa [prefixWord, tailWord_1984020, baseEnd_1984020] using wordTrace_append hprefix tailTrace_1984020
  have hstable : (prefixWord ++ tailWord_1984020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984020).length < 2 ^ (prefixWord ++ tailWord_1984020).sum := by decide
  have hdescent : baseEnd_1984020 < baseStart_1984020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984121 : List Nat := [1, 2, 1, 3, 3, 1, 10]
def baseStart_1984121 : Nat := 118140960795 + 1984121 * 2 ^ 59
def prefixEnd_1984121 : Nat := 4983230072969 + 3 ^ 40 * 1984121 * 2
def baseEnd_1984121 : Nat := 50311493811335153143837

theorem tailTrace_1984121 : CollatzResearch.WordTrace tailWord_1984121 prefixEnd_1984121 50311493811335153143837 := by
  unfold tailWord_1984121
  simp only [CollatzResearch.WordTrace]
  refine ⟨72366838044875952733816217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48244558696583968489210811 72366838044875952733816217)
  ·
    refine ⟨54275128533656964550362163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72366838044875952733816217 54275128533656964550362163)
    ·
      refine ⟨81412692800485446825543245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54275128533656964550362163 81412692800485446825543245)
      ·
        refine ⟨30529759800182042559578717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81412692800485446825543245 30529759800182042559578717)
        ·
          refine ⟨11448659925068265959842019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30529759800182042559578717 11448659925068265959842019)
          ·
            refine ⟨17172989887602398939763029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11448659925068265959842019 17172989887602398939763029)
            ·
              refine ⟨50311493811335153143837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17172989887602398939763029 50311493811335153143837)
              ·
                rfl

theorem cell21_1984121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 10].length) (baseStart_1984121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984121 prefixEnd_1984121 := by exact prefixLift 1984121
  have htrace : WordTrace (prefixWord ++ tailWord_1984121) baseStart_1984121 baseEnd_1984121 := by
    simpa [prefixWord, tailWord_1984121, baseEnd_1984121] using wordTrace_append hprefix tailTrace_1984121
  have hstable : (prefixWord ++ tailWord_1984121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984121).length < 2 ^ (prefixWord ++ tailWord_1984121).sum := by decide
  have hdescent : baseEnd_1984121 < baseStart_1984121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984183 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 6]
def baseStart_1984183 : Nat := 118140960795 + 1984183 * 2 ^ 59
def prefixEnd_1984183 : Nat := 4983230072969 + 3 ^ 40 * 1984183 * 2
def baseEnd_1984183 : Nat := 452817593546718048261073

theorem tailTrace_1984183 : CollatzResearch.WordTrace tailWord_1984183 prefixEnd_1984183 452817593546718048261073 := by
  unfold tailWord_1984183
  simp only [CollatzResearch.WordTrace]
  refine ⟨72369099370651337322573203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48246066247100891548382135 72369099370651337322573203)
  ·
    refine ⟨108553649055977005983859805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72369099370651337322573203 108553649055977005983859805)
    ·
      refine ⟨40707618395991377243947427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108553649055977005983859805 40707618395991377243947427)
      ·
        refine ⟨61061427593987065865921141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40707618395991377243947427 61061427593987065865921141)
        ·
          refine ⟨5724508836936287424930107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61061427593987065865921141 5724508836936287424930107)
          ·
            refine ⟨8586763255404431137395161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5724508836936287424930107 8586763255404431137395161)
            ·
              refine ⟨6440072441553323353046371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8586763255404431137395161 6440072441553323353046371)
              ·
                refine ⟨9660108662329985029569557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440072441553323353046371 9660108662329985029569557)
                ·
                  refine ⟨452817593546718048261073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9660108662329985029569557 452817593546718048261073)
                  ·
                    rfl

theorem cell21_1984183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_1984183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984183 prefixEnd_1984183 := by exact prefixLift 1984183
  have htrace : WordTrace (prefixWord ++ tailWord_1984183) baseStart_1984183 baseEnd_1984183 := by
    simpa [prefixWord, tailWord_1984183, baseEnd_1984183] using wordTrace_append hprefix tailTrace_1984183
  have hstable : (prefixWord ++ tailWord_1984183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984183).length < 2 ^ (prefixWord ++ tailWord_1984183).sum := by decide
  have hdescent : baseEnd_1984183 < baseStart_1984183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984231 : List Nat := [1, 1, 5, 4, 2, 8]
def baseStart_1984231 : Nat := 118140960795 + 1984231 * 2 ^ 59
def prefixEnd_1984231 : Nat := 4983230072969 + 3 ^ 40 * 1984231 * 2
def baseEnd_1984231 : Nat := 16771427696321504868925

theorem tailTrace_1984231 : CollatzResearch.WordTrace tailWord_1984231 prefixEnd_1984231 16771427696321504868925 := by
  unfold tailWord_1984231
  simp only [CollatzResearch.WordTrace]
  refine ⟨72370850074477441520320547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48247233382984961013547031 72370850074477441520320547)
  ·
    refine ⟨108556275111716162280480821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72370850074477441520320547 108556275111716162280480821)
    ·
      refine ⟨10177150791723390213795077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108556275111716162280480821 10177150791723390213795077)
      ·
        refine ⟨1908215773448135665086577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10177150791723390213795077 1908215773448135665086577)
        ·
          refine ⟨1431161830086101748814933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1908215773448135665086577 1431161830086101748814933)
          ·
            refine ⟨16771427696321504868925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1431161830086101748814933 16771427696321504868925)
            ·
              rfl

theorem cell21_1984231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 8].length) (baseStart_1984231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984231 prefixEnd_1984231 := by exact prefixLift 1984231
  have htrace : WordTrace (prefixWord ++ tailWord_1984231) baseStart_1984231 baseEnd_1984231 := by
    simpa [prefixWord, tailWord_1984231, baseEnd_1984231] using wordTrace_append hprefix tailTrace_1984231
  have hstable : (prefixWord ++ tailWord_1984231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984231).length < 2 ^ (prefixWord ++ tailWord_1984231).sum := by decide
  have hdescent : baseEnd_1984231 < baseStart_1984231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984259 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 4]
def baseStart_1984259 : Nat := 118140960795 + 1984259 * 2 ^ 59
def prefixEnd_1984259 : Nat := 4983230072969 + 3 ^ 40 * 1984259 * 2
def baseEnd_1984259 : Nat := 452834937782158804994251

theorem tailTrace_1984259 : CollatzResearch.WordTrace tailWord_1984259 prefixEnd_1984259 452834937782158804994251 := by
  unfold tailWord_1984259
  simp only [CollatzResearch.WordTrace]
  refine ⟨72371871318376002302339831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48247914212250668201559887 72371871318376002302339831)
  ·
    refine ⟨108557806977564003453509747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72371871318376002302339831 108557806977564003453509747)
    ·
      refine ⟨162836710466346005180264621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108557806977564003453509747 162836710466346005180264621)
      ·
        refine ⟨61063766424879751942599233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162836710466346005180264621 61063766424879751942599233)
        ·
          refine ⟨45797824818659813956949425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61063766424879751942599233 45797824818659813956949425)
          ·
            refine ⟨34348368613994860467712069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45797824818659813956949425 34348368613994860467712069)
            ·
              refine ⟨6440319115124036337696013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34348368613994860467712069 6440319115124036337696013)
              ·
                refine ⟨2415119668171513626636005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6440319115124036337696013 2415119668171513626636005)
                ·
                  refine ⟨452834937782158804994251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415119668171513626636005 452834937782158804994251)
                  ·
                    rfl

theorem cell21_1984259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 4].length) (baseStart_1984259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984259 prefixEnd_1984259 := by exact prefixLift 1984259
  have htrace : WordTrace (prefixWord ++ tailWord_1984259) baseStart_1984259 baseEnd_1984259 := by
    simpa [prefixWord, tailWord_1984259, baseEnd_1984259] using wordTrace_append hprefix tailTrace_1984259
  have hstable : (prefixWord ++ tailWord_1984259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984259).length < 2 ^ (prefixWord ++ tailWord_1984259).sum := by decide
  have hdescent : baseEnd_1984259 < baseStart_1984259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984310 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_1984310 : Nat := 118140960795 + 1984310 * 2 ^ 59
def prefixEnd_1984310 : Nat := 4983230072969 + 3 ^ 40 * 1984310 * 2
def baseEnd_1984310 : Nat := 452846576676994049644147

theorem tailTrace_1984310 : CollatzResearch.WordTrace tailWord_1984310 prefixEnd_1984310 452846576676994049644147 := by
  unfold tailWord_1984310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523358215074452375777899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48249154294127492008297589 4523358215074452375777899)
  ·
    refine ⟨6785037322611678563666849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4523358215074452375777899 6785037322611678563666849)
    ·
      refine ⟨5088777991958758922750137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6785037322611678563666849 5088777991958758922750137)
      ·
        refine ⟨3816583493969069192062603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5088777991958758922750137 3816583493969069192062603)
        ·
          refine ⟨5724875240953603788093905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3816583493969069192062603 5724875240953603788093905)
          ·
            refine ⟨4293656430715202841070429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5724875240953603788093905 4293656430715202841070429)
            ·
              refine ⟨1610121161518201065401411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4293656430715202841070429 1610121161518201065401411)
              ·
                refine ⟨2415181742277301598102117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610121161518201065401411 2415181742277301598102117)
                ·
                  refine ⟨452846576676994049644147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415181742277301598102117 452846576676994049644147)
                  ·
                    rfl

theorem cell21_1984310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_1984310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984310 prefixEnd_1984310 := by exact prefixLift 1984310
  have htrace : WordTrace (prefixWord ++ tailWord_1984310) baseStart_1984310 baseEnd_1984310 := by
    simpa [prefixWord, tailWord_1984310, baseEnd_1984310] using wordTrace_append hprefix tailTrace_1984310
  have hstable : (prefixWord ++ tailWord_1984310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984310).length < 2 ^ (prefixWord ++ tailWord_1984310).sum := by decide
  have hdescent : baseEnd_1984310 < baseStart_1984310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984338 : List Nat := [3, 2, 2, 1, 1, 3, 3, 3, 3]
def baseStart_1984338 : Nat := 118140960795 + 1984338 * 2 ^ 59
def prefixEnd_1984338 : Nat := 4983230072969 + 3 ^ 40 * 1984338 * 2
def baseEnd_1984338 : Nat := 452852966658472223177423

theorem tailTrace_1984338 : CollatzResearch.WordTrace tailWord_1984338 prefixEnd_1984338 452852966658472223177423 := by
  unfold tailWord_1984338
  simp only [CollatzResearch.WordTrace]
  refine ⟨18093688171272449698616417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48249835123393199196310445 18093688171272449698616417)
  ·
    refine ⟨13570266128454337273962313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18093688171272449698616417 13570266128454337273962313)
    ·
      refine ⟨10177699596340752955471735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13570266128454337273962313 10177699596340752955471735)
      ·
        refine ⟨15266549394511129433207603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10177699596340752955471735 15266549394511129433207603)
        ·
          refine ⟨22899824091766694149811405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15266549394511129433207603 22899824091766694149811405)
          ·
            refine ⟨8587434034412510306179277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22899824091766694149811405 8587434034412510306179277)
            ·
              refine ⟨3220287762904691364817229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8587434034412510306179277 3220287762904691364817229)
              ·
                refine ⟨1207607911089259261806461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3220287762904691364817229 1207607911089259261806461)
                ·
                  refine ⟨452852966658472223177423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207607911089259261806461 452852966658472223177423)
                  ·
                    rfl

theorem cell21_1984338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_1984338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984338 prefixEnd_1984338 := by exact prefixLift 1984338
  have htrace : WordTrace (prefixWord ++ tailWord_1984338) baseStart_1984338 baseEnd_1984338 := by
    simpa [prefixWord, tailWord_1984338, baseEnd_1984338] using wordTrace_append hprefix tailTrace_1984338
  have hstable : (prefixWord ++ tailWord_1984338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984338).length < 2 ^ (prefixWord ++ tailWord_1984338).sum := by decide
  have hdescent : baseEnd_1984338 < baseStart_1984338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984355 : List Nat := [1, 1, 1, 5, 4, 1, 3, 2, 3]
def baseStart_1984355 : Nat := 118140960795 + 1984355 * 2 ^ 59
def prefixEnd_1984355 : Nat := 4983230072969 + 3 ^ 40 * 1984355 * 2
def baseEnd_1984355 : Nat := 452856846290083971394055

theorem tailTrace_1984355 : CollatzResearch.WordTrace tailWord_1984355 prefixEnd_1984355 452856846290083971394055 := by
  unfold tailWord_1984355
  simp only [CollatzResearch.WordTrace]
  refine ⟨72375372726028210697834519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48250248484018807131889679 72375372726028210697834519)
  ·
    refine ⟨108563059089042316046751779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72375372726028210697834519 108563059089042316046751779)
    ·
      refine ⟨162844588633563474070127669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108563059089042316046751779 162844588633563474070127669)
      ·
        refine ⟨15266680184396575694074469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162844588633563474070127669 15266680184396575694074469)
        ·
          refine ⟨2862502534574357942638963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15266680184396575694074469 2862502534574357942638963)
          ·
            refine ⟨4293753801861536913958445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862502534574357942638963 4293753801861536913958445)
            ·
              refine ⟨1610157675698076342734417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4293753801861536913958445 1610157675698076342734417)
              ·
                refine ⟨1207618256773557257050813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610157675698076342734417 1207618256773557257050813)
                ·
                  refine ⟨452856846290083971394055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207618256773557257050813 452856846290083971394055)
                  ·
                    rfl

theorem cell21_1984355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 3].length) (baseStart_1984355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984355 prefixEnd_1984355 := by exact prefixLift 1984355
  have htrace : WordTrace (prefixWord ++ tailWord_1984355) baseStart_1984355 baseEnd_1984355 := by
    simpa [prefixWord, tailWord_1984355, baseEnd_1984355] using wordTrace_append hprefix tailTrace_1984355
  have hstable : (prefixWord ++ tailWord_1984355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984355).length < 2 ^ (prefixWord ++ tailWord_1984355).sum := by decide
  have hdescent : baseEnd_1984355 < baseStart_1984355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984366 : List Nat := [4, 1, 2, 3, 1, 1, 1, 8]
def baseStart_1984366 : Nat := 118140960795 + 1984366 * 2 ^ 59
def prefixEnd_1984366 : Nat := 4983230072969 + 3 ^ 40 * 1984366 * 2
def baseEnd_1984366 : Nat := 150953118879983465570233

theorem tailTrace_1984366 : CollatzResearch.WordTrace tailWord_1984366 prefixEnd_1984366 150953118879983465570233 := by
  unfold tailWord_1984366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9046971741123544947060619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48250515952658906384323301 9046971741123544947060619)
  ·
    refine ⟨13570457611685317420590929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9046971741123544947060619 13570457611685317420590929)
    ·
      refine ⟨10177843208763988065443197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13570457611685317420590929 10177843208763988065443197)
      ·
        refine ⟨3816691203286495524541199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10177843208763988065443197 3816691203286495524541199)
        ·
          refine ⟨5725036804929743286811799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3816691203286495524541199 5725036804929743286811799)
          ·
            refine ⟨8587555207394614930217699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5725036804929743286811799 8587555207394614930217699)
            ·
              refine ⟨12881332811091922395326549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8587555207394614930217699 12881332811091922395326549)
              ·
                refine ⟨150953118879983465570233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12881332811091922395326549 150953118879983465570233)
                ·
                  rfl

theorem cell21_1984366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_1984366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984366 prefixEnd_1984366 := by exact prefixLift 1984366
  have htrace : WordTrace (prefixWord ++ tailWord_1984366) baseStart_1984366 baseEnd_1984366 := by
    simpa [prefixWord, tailWord_1984366, baseEnd_1984366] using wordTrace_append hprefix tailTrace_1984366
  have hstable : (prefixWord ++ tailWord_1984366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984366).length < 2 ^ (prefixWord ++ tailWord_1984366).sum := by decide
  have hdescent : baseEnd_1984366 < baseStart_1984366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984406 : List Nat := [5, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1984406 : Nat := 118140960795 + 1984406 * 2 ^ 59
def prefixEnd_1984406 : Nat := 4983230072969 + 3 ^ 40 * 1984406 * 2
def baseEnd_1984406 : Nat := 452868485184919216043951

theorem tailTrace_1984406 : CollatzResearch.WordTrace tailWord_1984406 prefixEnd_1984406 452868485184919216043951 := by
  unfold tailWord_1984406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523577053052715400496317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48251488565895630938627381 4523577053052715400496317)
  ·
    refine ⟨1696341394894768275186119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4523577053052715400496317 1696341394894768275186119)
    ·
      refine ⟨2544512092342152412779179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696341394894768275186119 2544512092342152412779179)
      ·
        refine ⟨3816768138513228619168769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2544512092342152412779179 3816768138513228619168769)
        ·
          refine ⟨2862576103884921464376577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3816768138513228619168769 2862576103884921464376577)
          ·
            refine ⟨2146932077913691098282433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2862576103884921464376577 2146932077913691098282433)
            ·
              refine ⟨1610199058435268323711825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2146932077913691098282433 1610199058435268323711825)
              ·
                refine ⟨1207649293826451242783869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610199058435268323711825 1207649293826451242783869)
                ·
                  refine ⟨452868485184919216043951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207649293826451242783869 452868485184919216043951)
                  ·
                    rfl

theorem cell21_1984406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1984406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984406 prefixEnd_1984406 := by exact prefixLift 1984406
  have htrace : WordTrace (prefixWord ++ tailWord_1984406) baseStart_1984406 baseEnd_1984406 := by
    simpa [prefixWord, tailWord_1984406, baseEnd_1984406] using wordTrace_append hprefix tailTrace_1984406
  have hstable : (prefixWord ++ tailWord_1984406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984406).length < 2 ^ (prefixWord ++ tailWord_1984406).sum := by decide
  have hdescent : baseEnd_1984406 < baseStart_1984406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984473 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 5]
def baseStart_1984473 : Nat := 118140960795 + 1984473 * 2 ^ 59
def prefixEnd_1984473 : Nat := 4983230072969 + 3 ^ 40 * 1984473 * 2
def baseEnd_1984473 : Nat := 452883775497741988427147

theorem tailTrace_1984473 : CollatzResearch.WordTrace tailWord_1984473 prefixEnd_1984473 452883775497741988427147 := by
  unfold tailWord_1984473
  simp only [CollatzResearch.WordTrace]
  refine ⟨72379676539600716850630073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48253117693067144567086715 72379676539600716850630073)
  ·
    refine ⟨54284757404700537637972555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72379676539600716850630073 54284757404700537637972555)
    ·
      refine ⟨81427136107050806456958833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54284757404700537637972555 81427136107050806456958833)
      ·
        refine ⟨61070352080288104842719125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81427136107050806456958833 61070352080288104842719125)
        ·
          refine ⟨2862672753763504914502459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61070352080288104842719125 2862672753763504914502459)
          ·
            refine ⟨4294009130645257371753689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862672753763504914502459 4294009130645257371753689)
            ·
              refine ⟨3220506847983943028815267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4294009130645257371753689 3220506847983943028815267)
              ·
                refine ⟨4830760271975914543222901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220506847983943028815267 4830760271975914543222901)
                ·
                  refine ⟨452883775497741988427147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4830760271975914543222901 452883775497741988427147)
                  ·
                    rfl

theorem cell21_1984473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_1984473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984473 prefixEnd_1984473 := by exact prefixLift 1984473
  have htrace : WordTrace (prefixWord ++ tailWord_1984473) baseStart_1984473 baseEnd_1984473 := by
    simpa [prefixWord, tailWord_1984473, baseEnd_1984473] using wordTrace_append hprefix tailTrace_1984473
  have hstable : (prefixWord ++ tailWord_1984473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984473).length < 2 ^ (prefixWord ++ tailWord_1984473).sum := by decide
  have hdescent : baseEnd_1984473 < baseStart_1984473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984493 : List Nat := [1, 5, 1, 4, 2, 1, 2, 5]
def baseStart_1984493 : Nat := 118140960795 + 1984493 * 2 ^ 59
def prefixEnd_1984493 : Nat := 4983230072969 + 3 ^ 40 * 1984493 * 2
def baseEnd_1984493 : Nat := 150962779923408799364591

theorem tailTrace_1984493 : CollatzResearch.WordTrace tailWord_1984493 prefixEnd_1984493 150962779923408799364591 := by
  unfold tailWord_1984493
  simp only [CollatzResearch.WordTrace]
  refine ⟨72380405999528260266358133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48253603999685506844238755 72380405999528260266358133)
  ·
    refine ⟨6785663062455774399971075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72380405999528260266358133 6785663062455774399971075)
    ·
      refine ⟨10178494593683661599956613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6785663062455774399971075 10178494593683661599956613)
      ·
        refine ⟨1908467736315686549991865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10178494593683661599956613 1908467736315686549991865)
        ·
          refine ⟨1431350802236764912493899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1908467736315686549991865 1431350802236764912493899)
          ·
            refine ⟨2147026203355147368740849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431350802236764912493899 2147026203355147368740849)
            ·
              refine ⟨1610269652516360526555637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147026203355147368740849 1610269652516360526555637)
              ·
                refine ⟨150962779923408799364591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1610269652516360526555637 150962779923408799364591)
                ·
                  rfl

theorem cell21_1984493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 5].length) (baseStart_1984493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984493 prefixEnd_1984493 := by exact prefixLift 1984493
  have htrace : WordTrace (prefixWord ++ tailWord_1984493) baseStart_1984493 baseEnd_1984493 := by
    simpa [prefixWord, tailWord_1984493, baseEnd_1984493] using wordTrace_append hprefix tailTrace_1984493
  have hstable : (prefixWord ++ tailWord_1984493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984493).length < 2 ^ (prefixWord ++ tailWord_1984493).sum := by decide
  have hdescent : baseEnd_1984493 < baseStart_1984493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984515 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 7]
def baseStart_1984515 : Nat := 118140960795 + 1984515 * 2 ^ 59
def prefixEnd_1984515 : Nat := 4983230072969 + 3 ^ 40 * 1984515 * 2
def baseEnd_1984515 : Nat := 452893360469959248727061

theorem tailTrace_1984515 : CollatzResearch.WordTrace tailWord_1984515 prefixEnd_1984515 452893360469959248727061 := by
  unfold tailWord_1984515
  simp only [CollatzResearch.WordTrace]
  refine ⟨72381208405448558023658999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48254138936965705349105999 72381208405448558023658999)
  ·
    refine ⟨108571812608172837035488499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72381208405448558023658999 108571812608172837035488499)
    ·
      refine ⟨162857718912259255553232749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108571812608172837035488499 162857718912259255553232749)
      ·
        refine ⟨61071644592097220832462281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162857718912259255553232749 61071644592097220832462281)
        ·
          refine ⟨45803733444072915624346711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61071644592097220832462281 45803733444072915624346711)
          ·
            refine ⟨68705600166109373436520067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45803733444072915624346711 68705600166109373436520067)
            ·
              refine ⟨103058400249164060154780101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68705600166109373436520067 103058400249164060154780101)
              ·
                refine ⟨19323450046718261279021269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103058400249164060154780101 19323450046718261279021269)
                ·
                  refine ⟨452893360469959248727061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19323450046718261279021269 452893360469959248727061)
                  ·
                    rfl

theorem cell21_1984515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_1984515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984515 prefixEnd_1984515 := by exact prefixLift 1984515
  have htrace : WordTrace (prefixWord ++ tailWord_1984515) baseStart_1984515 baseEnd_1984515 := by
    simpa [prefixWord, tailWord_1984515, baseEnd_1984515] using wordTrace_append hprefix tailTrace_1984515
  have hstable : (prefixWord ++ tailWord_1984515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984515).length < 2 ^ (prefixWord ++ tailWord_1984515).sum := by decide
  have hdescent : baseEnd_1984515 < baseStart_1984515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984566 : List Nat := [5, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_1984566 : Nat := 118140960795 + 1984566 * 2 ^ 59
def prefixEnd_1984566 : Nat := 4983230072969 + 3 ^ 40 * 1984566 * 2
def baseEnd_1984566 : Nat := 452904999364794493376957

theorem tailTrace_1984566 : CollatzResearch.WordTrace tailWord_1984566 prefixEnd_1984566 452904999364794493376957 := by
  unfold tailWord_1984566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523941783016487108360347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48255379018842529155843701 4523941783016487108360347)
  ·
    refine ⟨6785912674524730662540521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4523941783016487108360347 6785912674524730662540521)
    ·
      refine ⟨5089434505893547996905391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6785912674524730662540521 5089434505893547996905391)
      ·
        refine ⟨7634151758840321995358087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5089434505893547996905391 7634151758840321995358087)
        ·
          refine ⟨11451227638260482993037131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7634151758840321995358087 11451227638260482993037131)
          ·
            refine ⟨17176841457390724489555697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11451227638260482993037131 17176841457390724489555697)
            ·
              refine ⟨12882631093043043367166773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17176841457390724489555697 12882631093043043367166773)
              ·
                refine ⟨1207746664972785315671885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12882631093043043367166773 1207746664972785315671885)
                ·
                  refine ⟨452904999364794493376957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207746664972785315671885 452904999364794493376957)
                  ·
                    rfl

theorem cell21_1984566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_1984566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984566 prefixEnd_1984566 := by exact prefixLift 1984566
  have htrace : WordTrace (prefixWord ++ tailWord_1984566) baseStart_1984566 baseEnd_1984566 := by
    simpa [prefixWord, tailWord_1984566, baseEnd_1984566] using wordTrace_append hprefix tailTrace_1984566
  have hstable : (prefixWord ++ tailWord_1984566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984566).length < 2 ^ (prefixWord ++ tailWord_1984566).sum := by decide
  have hdescent : baseEnd_1984566 < baseStart_1984566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984577 : List Nat := [1, 2, 5, 1, 2, 10]
def baseStart_1984577 : Nat := 118140960795 + 1984577 * 2 ^ 59
def prefixEnd_1984577 : Nat := 4983230072969 + 3 ^ 40 * 1984577 * 2
def baseEnd_1984577 : Nat := 16774352211654108099763

theorem tailTrace_1984577 : CollatzResearch.WordTrace tailWord_1984577 prefixEnd_1984577 16774352211654108099763 := by
  unfold tailWord_1984577
  simp only [CollatzResearch.WordTrace]
  refine ⟨72383469731223942612415985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48255646487482628408277323 72383469731223942612415985)
  ·
    refine ⟨54287602298417956959311989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72383469731223942612415985 54287602298417956959311989)
    ·
      refine ⟨5089462715476683464935499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54287602298417956959311989 5089462715476683464935499)
      ·
        refine ⟨7634194073215025197403249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5089462715476683464935499 7634194073215025197403249)
        ·
          refine ⟨5725645554911268898052437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7634194073215025197403249 5725645554911268898052437)
          ·
            refine ⟨16774352211654108099763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5725645554911268898052437 16774352211654108099763)
            ·
              rfl

theorem cell21_1984577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 10].length) (baseStart_1984577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984577 prefixEnd_1984577 := by exact prefixLift 1984577
  have htrace : WordTrace (prefixWord ++ tailWord_1984577) baseStart_1984577 baseEnd_1984577 := by
    simpa [prefixWord, tailWord_1984577, baseEnd_1984577] using wordTrace_append hprefix tailTrace_1984577
  have hstable : (prefixWord ++ tailWord_1984577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984577).length < 2 ^ (prefixWord ++ tailWord_1984577).sum := by decide
  have hdescent : baseEnd_1984577 < baseStart_1984577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984608 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 5]
def baseStart_1984608 : Nat := 118140960795 + 1984608 * 2 ^ 59
def prefixEnd_1984608 : Nat := 4983230072969 + 3 ^ 40 * 1984608 * 2
def baseEnd_1984608 : Nat := 452914584337011753676871

theorem tailTrace_1984608 : CollatzResearch.WordTrace tailWord_1984608 prefixEnd_1984608 452914584337011753676871 := by
  unfold tailWord_1984608
  simp only [CollatzResearch.WordTrace]
  refine ⟨36192300197055817453397239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48256400262741089937862985 36192300197055817453397239)
  ·
    refine ⟨54288450295583726180095859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36192300197055817453397239 54288450295583726180095859)
    ·
      refine ⟨81432675443375589270143789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54288450295583726180095859 81432675443375589270143789)
      ·
        refine ⟨30537253291265845976303921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81432675443375589270143789 30537253291265845976303921)
        ·
          refine ⟨22902939968449384482227941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30537253291265845976303921 22902939968449384482227941)
          ·
            refine ⟨4294301244084259590417739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22902939968449384482227941 4294301244084259590417739)
            ·
              refine ⟨6441451866126389385626609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294301244084259590417739 6441451866126389385626609)
              ·
                refine ⟨4831088899594792039219957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6441451866126389385626609 4831088899594792039219957)
                ·
                  refine ⟨452914584337011753676871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4831088899594792039219957 452914584337011753676871)
                  ·
                    rfl

theorem cell21_1984608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_1984608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984608 prefixEnd_1984608 := by exact prefixLift 1984608
  have htrace : WordTrace (prefixWord ++ tailWord_1984608) baseStart_1984608 baseEnd_1984608 := by
    simpa [prefixWord, tailWord_1984608, baseEnd_1984608] using wordTrace_append hprefix tailTrace_1984608
  have hstable : (prefixWord ++ tailWord_1984608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984608).length < 2 ^ (prefixWord ++ tailWord_1984608).sum := by decide
  have hdescent : baseEnd_1984608 < baseStart_1984608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984625 : List Nat := [1, 2, 2, 2, 1, 1, 6, 3, 3]
def baseStart_1984625 : Nat := 118140960795 + 1984625 * 2 ^ 59
def prefixEnd_1984625 : Nat := 4983230072969 + 3 ^ 40 * 1984625 * 2
def baseEnd_1984625 : Nat := 452918463968623501893503

theorem tailTrace_1984625 : CollatzResearch.WordTrace tailWord_1984625 prefixEnd_1984625 452918463968623501893503 := by
  unfold tailWord_1984625
  simp only [CollatzResearch.WordTrace]
  refine ⟨72385220435050046810163329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48256813623366697873442219 72385220435050046810163329)
  ·
    refine ⟨54288915326287535107622497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72385220435050046810163329 54288915326287535107622497)
    ·
      refine ⟨40716686494715651330716873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54288915326287535107622497 40716686494715651330716873)
      ·
        refine ⟨30537514871036738498037655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40716686494715651330716873 30537514871036738498037655)
        ·
          refine ⟨45806272306555107747056483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30537514871036738498037655 45806272306555107747056483)
          ·
            refine ⟨68709408459832661620584725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45806272306555107747056483 68709408459832661620584725)
            ·
              refine ⟨3220753521554656013464909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68709408459832661620584725 3220753521554656013464909)
              ·
                refine ⟨1207782570582996005049341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3220753521554656013464909 1207782570582996005049341)
                ·
                  refine ⟨452918463968623501893503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207782570582996005049341 452918463968623501893503)
                  ·
                    rfl

theorem cell21_1984625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 3].length) (baseStart_1984625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984625 prefixEnd_1984625 := by exact prefixLift 1984625
  have htrace : WordTrace (prefixWord ++ tailWord_1984625) baseStart_1984625 baseEnd_1984625 := by
    simpa [prefixWord, tailWord_1984625, baseEnd_1984625] using wordTrace_append hprefix tailTrace_1984625
  have hstable : (prefixWord ++ tailWord_1984625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984625).length < 2 ^ (prefixWord ++ tailWord_1984625).sum := by decide
  have hdescent : baseEnd_1984625 < baseStart_1984625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984667 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 5]
def baseStart_1984667 : Nat := 118140960795 + 1984667 * 2 ^ 59
def prefixEnd_1984667 : Nat := 4983230072969 + 3 ^ 40 * 1984667 * 2
def baseEnd_1984667 : Nat := 452928048940840762193417

theorem tailTrace_1984667 : CollatzResearch.WordTrace tailWord_1984667 prefixEnd_1984667 452928048940840762193417 := by
  unfold tailWord_1984667
  simp only [CollatzResearch.WordTrace]
  refine ⟨72386752300897887983192255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48257834867265258655461503 72386752300897887983192255)
  ·
    refine ⟨108580128451346831974788383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72386752300897887983192255 108580128451346831974788383)
    ·
      refine ⟨162870192677020247962182575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108580128451346831974788383 162870192677020247962182575)
      ·
        refine ⟨244305289015530371943273863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162870192677020247962182575 244305289015530371943273863)
        ·
          refine ⟨366457933523295557914910795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244305289015530371943273863 366457933523295557914910795)
          ·
            refine ⟨549686900284943336872366193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366457933523295557914910795 549686900284943336872366193)
            ·
              refine ⟨412265175213707502654274645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549686900284943336872366193 412265175213707502654274645)
              ·
                refine ⟨4831232522035634796729781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 412265175213707502654274645 4831232522035634796729781)
                ·
                  refine ⟨452928048940840762193417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4831232522035634796729781 452928048940840762193417)
                  ·
                    rfl

theorem cell21_1984667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_1984667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984667 prefixEnd_1984667 := by exact prefixLift 1984667
  have htrace : WordTrace (prefixWord ++ tailWord_1984667) baseStart_1984667 baseEnd_1984667 := by
    simpa [prefixWord, tailWord_1984667, baseEnd_1984667] using wordTrace_append hprefix tailTrace_1984667
  have hstable : (prefixWord ++ tailWord_1984667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984667).length < 2 ^ (prefixWord ++ tailWord_1984667).sum := by decide
  have hdescent : baseEnd_1984667 < baseStart_1984667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984698 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_1984698 : Nat := 118140960795 + 1984698 * 2 ^ 59
def prefixEnd_1984698 : Nat := 4983230072969 + 3 ^ 40 * 1984698 * 2
def baseEnd_1984698 : Nat := 452935123563191597176687

theorem tailTrace_1984698 : CollatzResearch.WordTrace tailWord_1984698 prefixEnd_1984698 452935123563191597176687 := by
  unfold tailWord_1984698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18096970740946395069392687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48258588642523720185047165 18096970740946395069392687)
  ·
    refine ⟨27145456111419592604089031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18096970740946395069392687 27145456111419592604089031)
    ·
      refine ⟨40718184167129388906133547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27145456111419592604089031 40718184167129388906133547)
      ·
        refine ⟨61077276250694083359200321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40718184167129388906133547 61077276250694083359200321)
        ·
          refine ⟨45807957188020562519400241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61077276250694083359200321 45807957188020562519400241)
          ·
            refine ⟨34355967891015421889550181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45807957188020562519400241 34355967891015421889550181)
            ·
              refine ⟨6441743979565391604290659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34355967891015421889550181 6441743979565391604290659)
              ·
                refine ⟨9662615969348087406435989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6441743979565391604290659 9662615969348087406435989)
                ·
                  refine ⟨452935123563191597176687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9662615969348087406435989 452935123563191597176687)
                  ·
                    rfl

theorem cell21_1984698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_1984698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984698 prefixEnd_1984698 := by exact prefixLift 1984698
  have htrace : WordTrace (prefixWord ++ tailWord_1984698) baseStart_1984698 baseEnd_1984698 := by
    simpa [prefixWord, tailWord_1984698, baseEnd_1984698] using wordTrace_append hprefix tailTrace_1984698
  have hstable : (prefixWord ++ tailWord_1984698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984698).length < 2 ^ (prefixWord ++ tailWord_1984698).sum := by decide
  have hdescent : baseEnd_1984698 < baseStart_1984698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984794 : List Nat := [3, 1, 1, 3, 4, 1, 2, 3, 3]
def baseStart_1984794 : Nat := 118140960795 + 1984794 * 2 ^ 59
def prefixEnd_1984794 : Nat := 4983230072969 + 3 ^ 40 * 1984794 * 2
def baseEnd_1984794 : Nat := 452957032071116763576491

theorem tailTrace_1984794 : CollatzResearch.WordTrace tailWord_1984794 prefixEnd_1984794 452957032071116763576491 := by
  unfold tailWord_1984794
  simp only [CollatzResearch.WordTrace]
  refine ⟨18097846092859447168266359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48260922914291859115376957 18097846092859447168266359)
  ·
    refine ⟨27146769139289170752399539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18097846092859447168266359 27146769139289170752399539)
    ·
      refine ⟨40720153708933756128599309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27146769139289170752399539 40720153708933756128599309)
      ·
        refine ⟨15270057640850158548224741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40720153708933756128599309 15270057640850158548224741)
        ·
          refine ⟨2863135807659404727792139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15270057640850158548224741 2863135807659404727792139)
          ·
            refine ⟨4294703711489107091688209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863135807659404727792139 4294703711489107091688209)
            ·
              refine ⟨3221027783616830318766157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4294703711489107091688209 3221027783616830318766157)
              ·
                refine ⟨1207885418856311369537309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3221027783616830318766157 1207885418856311369537309)
                ·
                  refine ⟨452957032071116763576491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207885418856311369537309 452957032071116763576491)
                  ·
                    rfl

theorem cell21_1984794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_1984794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984794 prefixEnd_1984794 := by exact prefixLift 1984794
  have htrace : WordTrace (prefixWord ++ tailWord_1984794) baseStart_1984794 baseEnd_1984794 := by
    simpa [prefixWord, tailWord_1984794, baseEnd_1984794] using wordTrace_append hprefix tailTrace_1984794
  have hstable : (prefixWord ++ tailWord_1984794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984794).length < 2 ^ (prefixWord ++ tailWord_1984794).sum := by decide
  have hdescent : baseEnd_1984794 < baseStart_1984794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984805 : List Nat := [1, 3, 1, 2, 5, 1, 8]
def baseStart_1984805 : Nat := 118140960795 + 1984805 * 2 ^ 59
def prefixEnd_1984805 : Nat := 4983230072969 + 3 ^ 40 * 1984805 * 2
def baseEnd_1984805 : Nat := 50328838046775909877015

theorem tailTrace_1984805 : CollatzResearch.WordTrace tailWord_1984805 prefixEnd_1984805 50328838046775909877015 := by
  unfold tailWord_1984805
  simp only [CollatzResearch.WordTrace]
  refine ⟨72391785574397937551715869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48261190382931958367810579 72391785574397937551715869)
  ·
    refine ⟨27146919590399226581893451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72391785574397937551715869 27146919590399226581893451)
    ·
      refine ⟨40720379385598839872840177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27146919590399226581893451 40720379385598839872840177)
      ·
        refine ⟨30540284539199129904630133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40720379385598839872840177 30540284539199129904630133)
        ·
          refine ⟨2863151675549918428559075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30540284539199129904630133 2863151675549918428559075)
          ·
            refine ⟨4294727513324877642838613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863151675549918428559075 4294727513324877642838613)
            ·
              refine ⟨50328838046775909877015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4294727513324877642838613 50328838046775909877015)
              ·
                rfl

theorem cell21_1984805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 8].length) (baseStart_1984805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984805 prefixEnd_1984805 := by exact prefixLift 1984805
  have htrace : WordTrace (prefixWord ++ tailWord_1984805) baseStart_1984805 baseEnd_1984805 := by
    simpa [prefixWord, tailWord_1984805, baseEnd_1984805] using wordTrace_append hprefix tailTrace_1984805
  have hstable : (prefixWord ++ tailWord_1984805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984805).length < 2 ^ (prefixWord ++ tailWord_1984805).sum := by decide
  have hdescent : baseEnd_1984805 < baseStart_1984805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984850 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_1984850 : Nat := 118140960795 + 1984850 * 2 ^ 59
def prefixEnd_1984850 : Nat := 4983230072969 + 3 ^ 40 * 1984850 * 2
def baseEnd_1984850 : Nat := 452969812034073110643043

theorem tailTrace_1984850 : CollatzResearch.WordTrace tailWord_1984850 prefixEnd_1984850 452969812034073110643043 := by
  unfold tailWord_1984850
  simp only [CollatzResearch.WordTrace]
  refine ⟨18098356714808727559276001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48262284572823273491402669 18098356714808727559276001)
  ·
    refine ⟨13573767536106545669457001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18098356714808727559276001 13573767536106545669457001)
    ·
      refine ⟨10180325652079909252092751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13573767536106545669457001 10180325652079909252092751)
      ·
        refine ⟨15270488478119863878139127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180325652079909252092751 15270488478119863878139127)
        ·
          refine ⟨22905732717179795817208691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15270488478119863878139127 22905732717179795817208691)
          ·
            refine ⟨34358599075769693725813037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22905732717179795817208691 34358599075769693725813037)
            ·
              refine ⟨12884474653413635147179889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34358599075769693725813037 12884474653413635147179889)
              ·
                refine ⟨9663355990060226360384917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12884474653413635147179889 9663355990060226360384917)
                ·
                  refine ⟨452969812034073110643043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9663355990060226360384917 452969812034073110643043)
                  ·
                    rfl

theorem cell21_1984850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1984850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984850 prefixEnd_1984850 := by exact prefixLift 1984850
  have htrace : WordTrace (prefixWord ++ tailWord_1984850) baseStart_1984850 baseEnd_1984850 := by
    simpa [prefixWord, tailWord_1984850, baseEnd_1984850] using wordTrace_append hprefix tailTrace_1984850
  have hstable : (prefixWord ++ tailWord_1984850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984850).length < 2 ^ (prefixWord ++ tailWord_1984850).sum := by decide
  have hdescent : baseEnd_1984850 < baseStart_1984850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984862 : List Nat := [4, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1984862 : Nat := 118140960795 + 1984862 * 2 ^ 59
def prefixEnd_1984862 : Nat := 4983230072969 + 3 ^ 40 * 1984862 * 2
def baseEnd_1984862 : Nat := 452972550597563756443019

theorem tailTrace_1984862 : CollatzResearch.WordTrace tailWord_1984862 prefixEnd_1984862 452972550597563756443019 := by
  unfold tailWord_1984862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049233066898929535817605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48262576356794290857693893 9049233066898929535817605)
  ·
    refine ⟨1696731200043549287965801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9049233066898929535817605 1696731200043549287965801)
    ·
      refine ⟨1272548400032661965974351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1696731200043549287965801 1272548400032661965974351)
      ·
        refine ⟨1908822600048992948961527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272548400032661965974351 1908822600048992948961527)
        ·
          refine ⟨2863233900073489423442291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908822600048992948961527 2863233900073489423442291)
          ·
            refine ⟨4294850850110234135163437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863233900073489423442291 4294850850110234135163437)
            ·
              refine ⟨1610569068791337800686289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4294850850110234135163437 1610569068791337800686289)
              ·
                refine ⟨1207926801593503350514717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610569068791337800686289 1207926801593503350514717)
                ·
                  refine ⟨452972550597563756443019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207926801593503350514717 452972550597563756443019)
                  ·
                    rfl

theorem cell21_1984862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1984862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984862 prefixEnd_1984862 := by exact prefixLift 1984862
  have htrace : WordTrace (prefixWord ++ tailWord_1984862) baseStart_1984862 baseEnd_1984862 := by
    simpa [prefixWord, tailWord_1984862, baseEnd_1984862] using wordTrace_append hprefix tailTrace_1984862
  have hstable : (prefixWord ++ tailWord_1984862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984862).length < 2 ^ (prefixWord ++ tailWord_1984862).sum := by decide
  have hdescent : baseEnd_1984862 < baseStart_1984862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984994 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1984994 : Nat := 118140960795 + 1984994 * 2 ^ 59
def prefixEnd_1984994 : Nat := 4983230072969 + 3 ^ 40 * 1984994 * 2
def baseEnd_1984994 : Nat := 453002674795960860242749

theorem tailTrace_1984994 : CollatzResearch.WordTrace tailWord_1984994 prefixEnd_1984994 453002674795960860242749 := by
  unfold tailWord_1984994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18099669742678305707586509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48265785980475481886897357 18099669742678305707586509)
  ·
    refine ⟨6787376153504364640344941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18099669742678305707586509 6787376153504364640344941)
    ·
      refine ⟨2545266057564136740129353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6787376153504364640344941 2545266057564136740129353)
      ·
        refine ⟨1908949543173102555097015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2545266057564136740129353 1908949543173102555097015)
        ·
          refine ⟨2863424314759653832645523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908949543173102555097015 2863424314759653832645523)
          ·
            refine ⟨4295136472139480748968285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863424314759653832645523 4295136472139480748968285)
            ·
              refine ⟨1610676177052305280863107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4295136472139480748968285 1610676177052305280863107)
              ·
                refine ⟨2416014265578457921294661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610676177052305280863107 2416014265578457921294661)
                ·
                  refine ⟨453002674795960860242749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2416014265578457921294661 453002674795960860242749)
                  ·
                    rfl

theorem cell21_1984994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1984994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1984994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1984994 prefixEnd_1984994 := by exact prefixLift 1984994
  have htrace : WordTrace (prefixWord ++ tailWord_1984994) baseStart_1984994 baseEnd_1984994 := by
    simpa [prefixWord, tailWord_1984994, baseEnd_1984994] using wordTrace_append hprefix tailTrace_1984994
  have hstable : (prefixWord ++ tailWord_1984994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984994).length < 2 ^ (prefixWord ++ tailWord_1984994).sum := by decide
  have hdescent : baseEnd_1984994 < baseStart_1984994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985016 : List Nat := [2, 1, 2, 1, 1, 4, 3, 7]
def baseStart_1985016 : Nat := 118140960795 + 1985016 * 2 ^ 59
def prefixEnd_1985016 : Nat := 4983230072969 + 3 ^ 40 * 1985016 * 2
def baseEnd_1985016 : Nat := 151002565165231236958679

theorem tailTrace_1985016 : CollatzResearch.WordTrace tailWord_1985016 prefixEnd_1985016 151002565165231236958679 := by
  unfold tailWord_1985016
  simp only [CollatzResearch.WordTrace]
  refine ⟨36199740688316760293823451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48266320917755680391764601 36199740688316760293823451)
  ·
    refine ⟨54299611032475140440735177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36199740688316760293823451 54299611032475140440735177)
    ·
      refine ⟨40724708274356355330551383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54299611032475140440735177 40724708274356355330551383)
      ·
        refine ⟨61087062411534532995827075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40724708274356355330551383 61087062411534532995827075)
        ·
          refine ⟨91630593617301799493740613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61087062411534532995827075 91630593617301799493740613)
          ·
            refine ⟨17180736303244087405076365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91630593617301799493740613 17180736303244087405076365)
            ·
              refine ⟨6442776113716532776903637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17180736303244087405076365 6442776113716532776903637)
              ·
                refine ⟨151002565165231236958679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6442776113716532776903637 151002565165231236958679)
                ·
                  rfl

theorem cell21_1985016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_1985016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985016 prefixEnd_1985016 := by exact prefixLift 1985016
  have htrace : WordTrace (prefixWord ++ tailWord_1985016) baseStart_1985016 baseEnd_1985016 := by
    simpa [prefixWord, tailWord_1985016, baseEnd_1985016] using wordTrace_append hprefix tailTrace_1985016
  have hstable : (prefixWord ++ tailWord_1985016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985016).length < 2 ^ (prefixWord ++ tailWord_1985016).sum := by decide
  have hdescent : baseEnd_1985016 < baseStart_1985016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985095 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 4]
def baseStart_1985095 : Nat := 118140960795 + 1985095 * 2 ^ 59
def prefixEnd_1985095 : Nat := 4983230072969 + 3 ^ 40 * 1985095 * 2
def baseEnd_1985095 : Nat := 453025724372007129059209

theorem tailTrace_1985095 : CollatzResearch.WordTrace tailWord_1985095 prefixEnd_1985095 453025724372007129059209 := by
  unfold tailWord_1985095
  simp only [CollatzResearch.WordTrace]
  refine ⟨72402362743347317079772739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48268241828898211386515159 72402362743347317079772739)
  ·
    refine ⟨108603544115020975619659109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72402362743347317079772739 108603544115020975619659109)
    ·
      refine ⟨20363164521566432928686083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108603544115020975619659109 20363164521566432928686083)
      ·
        refine ⟨30544746782349649393029125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20363164521566432928686083 30544746782349649393029125)
        ·
          refine ⟨5727140021690559261192961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30544746782349649393029125 5727140021690559261192961)
          ·
            refine ⟨4295355016267919445894721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5727140021690559261192961 4295355016267919445894721)
            ·
              refine ⟨3221516262200939584421041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4295355016267919445894721 3221516262200939584421041)
              ·
                refine ⟨2416137196650704688315781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3221516262200939584421041 2416137196650704688315781)
                ·
                  refine ⟨453025724372007129059209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2416137196650704688315781 453025724372007129059209)
                  ·
                    rfl

theorem cell21_1985095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 4].length) (baseStart_1985095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985095 prefixEnd_1985095 := by exact prefixLift 1985095
  have htrace : WordTrace (prefixWord ++ tailWord_1985095) baseStart_1985095 baseEnd_1985095 := by
    simpa [prefixWord, tailWord_1985095, baseEnd_1985095] using wordTrace_append hprefix tailTrace_1985095
  have hstable : (prefixWord ++ tailWord_1985095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985095).length < 2 ^ (prefixWord ++ tailWord_1985095).sum := by decide
  have hdescent : baseEnd_1985095 < baseStart_1985095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985098 : List Nat := [3, 1, 2, 1, 1, 6, 2, 2, 3]
def baseStart_1985098 : Nat := 118140960795 + 1985098 * 2 ^ 59
def prefixEnd_1985098 : Nat := 4983230072969 + 3 ^ 40 * 1985098 * 2
def baseEnd_1985098 : Nat := 453026409012879790509203

theorem tailTrace_1985098 : CollatzResearch.WordTrace tailWord_1985098 prefixEnd_1985098 453026409012879790509203 := by
  unfold tailWord_1985098
  simp only [CollatzResearch.WordTrace]
  refine ⟨18100618040584112148032987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48268314774890965728087965 18100618040584112148032987)
  ·
    refine ⟨27150927060876168222049481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18100618040584112148032987 27150927060876168222049481)
    ·
      refine ⟨20363195295657126166537111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27150927060876168222049481 20363195295657126166537111)
      ·
        refine ⟨30544792943485689249805667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20363195295657126166537111 30544792943485689249805667)
        ·
          refine ⟨45817189415228533874708501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30544792943485689249805667 45817189415228533874708501)
          ·
            refine ⟨2147680753838837525376961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45817189415228533874708501 2147680753838837525376961)
            ·
              refine ⟨1610760565379128144032721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147680753838837525376961 1610760565379128144032721)
              ·
                refine ⟨1208070424034346108024541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610760565379128144032721 1208070424034346108024541)
                ·
                  refine ⟨453026409012879790509203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208070424034346108024541 453026409012879790509203)
                  ·
                    rfl

theorem cell21_1985098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_1985098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985098 prefixEnd_1985098 := by exact prefixLift 1985098
  have htrace : WordTrace (prefixWord ++ tailWord_1985098) baseStart_1985098 baseEnd_1985098 := by
    simpa [prefixWord, tailWord_1985098, baseEnd_1985098] using wordTrace_append hprefix tailTrace_1985098
  have hstable : (prefixWord ++ tailWord_1985098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985098).length < 2 ^ (prefixWord ++ tailWord_1985098).sum := by decide
  have hdescent : baseEnd_1985098 < baseStart_1985098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985123 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 5]
def baseStart_1985123 : Nat := 118140960795 + 1985123 * 2 ^ 59
def prefixEnd_1985123 : Nat := 4983230072969 + 3 ^ 40 * 1985123 * 2
def baseEnd_1985123 : Nat := 453032114353485302592485

theorem tailTrace_1985123 : CollatzResearch.WordTrace tailWord_1985123 prefixEnd_1985123 453032114353485302592485 := by
  unfold tailWord_1985123
  simp only [CollatzResearch.WordTrace]
  refine ⟨72403383987245877861792023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48268922658163918574528015 72403383987245877861792023)
  ·
    refine ⟨108605075980868816792688035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72403383987245877861792023 108605075980868816792688035)
    ·
      refine ⟨162907613971303225189032053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108605075980868816792688035 162907613971303225189032053)
      ·
        refine ⟨15272588809809677361471755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162907613971303225189032053 15272588809809677361471755)
        ·
          refine ⟨22908883214714516042207633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15272588809809677361471755 22908883214714516042207633)
          ·
            refine ⟨17181662411035887031655725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22908883214714516042207633 17181662411035887031655725)
            ·
              refine ⟨6443123404138457636870897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17181662411035887031655725 6443123404138457636870897)
              ·
                refine ⟨4832342553103843227653173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6443123404138457636870897 4832342553103843227653173)
                ·
                  refine ⟨453032114353485302592485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4832342553103843227653173 453032114353485302592485)
                  ·
                    rfl

theorem cell21_1985123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_1985123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985123 prefixEnd_1985123 := by exact prefixLift 1985123
  have htrace : WordTrace (prefixWord ++ tailWord_1985123) baseStart_1985123 baseEnd_1985123 := by
    simpa [prefixWord, tailWord_1985123, baseEnd_1985123] using wordTrace_append hprefix tailTrace_1985123
  have hstable : (prefixWord ++ tailWord_1985123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985123).length < 2 ^ (prefixWord ++ tailWord_1985123).sum := by decide
  have hdescent : baseEnd_1985123 < baseStart_1985123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985185 : List Nat := [1, 2, 3, 3, 3, 1, 1, 7]
def baseStart_1985185 : Nat := 118140960795 + 1985185 * 2 ^ 59
def prefixEnd_1985185 : Nat := 4983230072969 + 3 ^ 40 * 1985185 * 2
def baseEnd_1985185 : Nat := 151015421199395657519675

theorem tailTrace_1985185 : CollatzResearch.WordTrace tailWord_1985185 prefixEnd_1985185 151015421199395657519675 := by
  unfold tailWord_1985185
  simp only [CollatzResearch.WordTrace]
  refine ⟨72405645313021262450549009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48270430208680841633699339 72405645313021262450549009)
  ·
    refine ⟨54304233984765946837911757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72405645313021262450549009 54304233984765946837911757)
    ·
      refine ⟨20364087744287230064216909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54304233984765946837911757 20364087744287230064216909)
      ·
        refine ⟨7636532904107711274081341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20364087744287230064216909 7636532904107711274081341)
        ·
          refine ⟨2863699839040391727780503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7636532904107711274081341 2863699839040391727780503)
          ·
            refine ⟨4295549758560587591670755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863699839040391727780503 4295549758560587591670755)
            ·
              refine ⟨6443324637840881387506133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4295549758560587591670755 6443324637840881387506133)
              ·
                refine ⟨151015421199395657519675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6443324637840881387506133 151015421199395657519675)
                ·
                  rfl

theorem cell21_1985185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 7].length) (baseStart_1985185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985185 prefixEnd_1985185 := by exact prefixLift 1985185
  have htrace : WordTrace (prefixWord ++ tailWord_1985185) baseStart_1985185 baseEnd_1985185 := by
    simpa [prefixWord, tailWord_1985185, baseEnd_1985185] using wordTrace_append hprefix tailTrace_1985185
  have hstable : (prefixWord ++ tailWord_1985185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985185).length < 2 ^ (prefixWord ++ tailWord_1985185).sum := by decide
  have hdescent : baseEnd_1985185 < baseStart_1985185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985191 : List Nat := [1, 1, 6, 3, 1, 2, 1, 3, 3]
def baseStart_1985191 : Nat := 118140960795 + 1985191 * 2 ^ 59
def prefixEnd_1985191 : Nat := 4983230072969 + 3 ^ 40 * 1985191 * 2
def baseEnd_1985191 : Nat := 453047632879932295459013

theorem tailTrace_1985191 : CollatzResearch.WordTrace tailWord_1985191 prefixEnd_1985191 453047632879932295459013 := by
  unfold tailWord_1985191
  simp only [CollatzResearch.WordTrace]
  refine ⟨72405864150999525475267427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48270576100666350316844951 72405864150999525475267427)
  ·
    refine ⟨108608796226499288212901141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72405864150999525475267427 108608796226499288212901141)
    ·
      refine ⟨5091037323117154134979741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108608796226499288212901141 5091037323117154134979741)
      ·
        refine ⟨1909138996168932800617403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5091037323117154134979741 1909138996168932800617403)
        ·
          refine ⟨2863708494253399200926105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909138996168932800617403 2863708494253399200926105)
          ·
            refine ⟨2147781370690049400694579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2863708494253399200926105 2147781370690049400694579)
            ·
              refine ⟨3221672056035074101041869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147781370690049400694579 3221672056035074101041869)
              ·
                refine ⟨1208127021013152787890701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3221672056035074101041869 1208127021013152787890701)
                ·
                  refine ⟨453047632879932295459013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208127021013152787890701 453047632879932295459013)
                  ·
                    rfl

theorem cell21_1985191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 3].length) (baseStart_1985191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985191 prefixEnd_1985191 := by exact prefixLift 1985191
  have htrace : WordTrace (prefixWord ++ tailWord_1985191) baseStart_1985191 baseEnd_1985191 := by
    simpa [prefixWord, tailWord_1985191, baseEnd_1985191] using wordTrace_append hprefix tailTrace_1985191
  have hstable : (prefixWord ++ tailWord_1985191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985191).length < 2 ^ (prefixWord ++ tailWord_1985191).sum := by decide
  have hdescent : baseEnd_1985191 < baseStart_1985191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985216 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 5]
def baseStart_1985216 : Nat := 118140960795 + 1985216 * 2 ^ 59
def prefixEnd_1985216 : Nat := 4983230072969 + 3 ^ 40 * 1985216 * 2
def baseEnd_1985216 : Nat := 453053338220537807542295

theorem tailTrace_1985216 : CollatzResearch.WordTrace tailWord_1985216 prefixEnd_1985216 453053338220537807542295 := by
  unfold tailWord_1985216
  simp only [CollatzResearch.WordTrace]
  refine ⟨36203387987954477372463751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48271183983939303163285001 36203387987954477372463751)
  ·
    refine ⟨54305081981931716058695627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36203387987954477372463751 54305081981931716058695627)
    ·
      refine ⟨81457622972897574088043441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54305081981931716058695627 81457622972897574088043441)
      ·
        refine ⟨61093217229673180566032581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81457622972897574088043441 61093217229673180566032581)
        ·
          refine ⟨11454978230563721356131109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61093217229673180566032581 11454978230563721356131109)
          ·
            refine ⟨2147808418230697754274583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11454978230563721356131109 2147808418230697754274583)
            ·
              refine ⟨3221712627346046631411875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147808418230697754274583 3221712627346046631411875)
              ·
                refine ⟨4832568941019069947117813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3221712627346046631411875 4832568941019069947117813)
                ·
                  refine ⟨453053338220537807542295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4832568941019069947117813 453053338220537807542295)
                  ·
                    rfl

theorem cell21_1985216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_1985216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985216 prefixEnd_1985216 := by exact prefixLift 1985216
  have htrace : WordTrace (prefixWord ++ tailWord_1985216) baseStart_1985216 baseEnd_1985216 := by
    simpa [prefixWord, tailWord_1985216, baseEnd_1985216] using wordTrace_append hprefix tailTrace_1985216
  have hstable : (prefixWord ++ tailWord_1985216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985216).length < 2 ^ (prefixWord ++ tailWord_1985216).sum := by decide
  have hdescent : baseEnd_1985216 < baseStart_1985216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985278 : List Nat := [4, 2, 2, 1, 2, 3, 1, 6]
def baseStart_1985278 : Nat := 118140960795 + 1985278 * 2 ^ 59
def prefixEnd_1985278 : Nat := 4983230072969 + 3 ^ 40 * 1985278 * 2
def baseEnd_1985278 : Nat := 151022495821746492502945

theorem tailTrace_1985278 : CollatzResearch.WordTrace tailWord_1985278 prefixEnd_1985278 151022495821746492502945 := by
  unfold tailWord_1985278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9051129662710542416710561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48272691534456226222456325 9051129662710542416710561)
  ·
    refine ⟨6788347247032906812532921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9051129662710542416710561 6788347247032906812532921)
    ·
      refine ⟨5091260435274680109399691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6788347247032906812532921 5091260435274680109399691)
      ·
        refine ⟨7636890652912020164099537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5091260435274680109399691 7636890652912020164099537)
        ·
          refine ⟨5727667989684015123074653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7636890652912020164099537 5727667989684015123074653)
          ·
            refine ⟨2147875496131505671152995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5727667989684015123074653 2147875496131505671152995)
            ·
              refine ⟨3221813244197258506729493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147875496131505671152995 3221813244197258506729493)
              ·
                refine ⟨151022495821746492502945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3221813244197258506729493 151022495821746492502945)
                ·
                  rfl

theorem cell21_1985278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_1985278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985278 prefixEnd_1985278 := by exact prefixLift 1985278
  have htrace : WordTrace (prefixWord ++ tailWord_1985278) baseStart_1985278 baseEnd_1985278 := by
    simpa [prefixWord, tailWord_1985278, baseEnd_1985278] using wordTrace_append hprefix tailTrace_1985278
  have hstable : (prefixWord ++ tailWord_1985278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985278).length < 2 ^ (prefixWord ++ tailWord_1985278).sum := by decide
  have hdescent : baseEnd_1985278 < baseStart_1985278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985320 : List Nat := [2, 1, 5, 1, 1, 1, 10]
def baseStart_1985320 : Nat := 118140960795 + 1985320 * 2 ^ 59
def prefixEnd_1985320 : Nat := 4983230072969 + 3 ^ 40 * 1985320 * 2
def baseEnd_1985320 : Nat := 50341896937495193089861

theorem tailTrace_1985320 : CollatzResearch.WordTrace tailWord_1985320 prefixEnd_1985320 50341896937495193089861 := by
  unfold tailWord_1985320
  simp only [CollatzResearch.WordTrace]
  refine ⟨36205284583766090253356707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48273712778354787004475609 36205284583766090253356707)
  ·
    refine ⟨54307926875649135380035061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36205284583766090253356707 54307926875649135380035061)
    ·
      refine ⟨5091368144592106441878287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54307926875649135380035061 5091368144592106441878287)
      ·
        refine ⟨7637052216888159662817431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5091368144592106441878287 7637052216888159662817431)
        ·
          refine ⟨11455578325332239494226147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7637052216888159662817431 11455578325332239494226147)
          ·
            refine ⟨17183367487998359241339221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11455578325332239494226147 17183367487998359241339221)
            ·
              refine ⟨50341896937495193089861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17183367487998359241339221 50341896937495193089861)
              ·
                rfl

theorem cell21_1985320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 10].length) (baseStart_1985320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985320 prefixEnd_1985320 := by exact prefixLift 1985320
  have htrace : WordTrace (prefixWord ++ tailWord_1985320) baseStart_1985320 baseEnd_1985320 := by
    simpa [prefixWord, tailWord_1985320, baseEnd_1985320] using wordTrace_append hprefix tailTrace_1985320
  have hstable : (prefixWord ++ tailWord_1985320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985320).length < 2 ^ (prefixWord ++ tailWord_1985320).sum := by decide
  have hdescent : baseEnd_1985320 < baseStart_1985320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985365 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 8]
def baseStart_1985365 : Nat := 118140960795 + 1985365 * 2 ^ 59
def prefixEnd_1985365 : Nat := 4983230072969 + 3 ^ 40 * 1985365 * 2
def baseEnd_1985365 : Nat := 453087342050546659558657

theorem tailTrace_1985365 : CollatzResearch.WordTrace tailWord_1985365 prefixEnd_1985365 453087342050546659558657 := by
  unfold tailWord_1985365
  simp only [CollatzResearch.WordTrace]
  refine ⟨72412210452369153192101549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48274806968246102128067699 72412210452369153192101549)
  ·
    refine ⟨27154578919638432447038081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72412210452369153192101549 27154578919638432447038081)
    ·
      refine ⟨20365934189728824335278561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27154578919638432447038081 20365934189728824335278561)
      ·
        refine ⟨15274450642296618251458921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20365934189728824335278561 15274450642296618251458921)
        ·
          refine ⟨11455837981722463688594191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15274450642296618251458921 11455837981722463688594191)
          ·
            refine ⟨17183756972583695532891287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11455837981722463688594191 17183756972583695532891287)
            ·
              refine ⟨25775635458875543299336931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17183756972583695532891287 25775635458875543299336931)
              ·
                refine ⟨38663453188313314949005397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25775635458875543299336931 38663453188313314949005397)
                ·
                  refine ⟨453087342050546659558657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38663453188313314949005397 453087342050546659558657)
                  ·
                    rfl

theorem cell21_1985365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_1985365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985365 prefixEnd_1985365 := by exact prefixLift 1985365
  have htrace : WordTrace (prefixWord ++ tailWord_1985365) baseStart_1985365 baseEnd_1985365 := by
    simpa [prefixWord, tailWord_1985365, baseEnd_1985365] using wordTrace_append hprefix tailTrace_1985365
  have hstable : (prefixWord ++ tailWord_1985365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985365).length < 2 ^ (prefixWord ++ tailWord_1985365).sum := by decide
  have hdescent : baseEnd_1985365 < baseStart_1985365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985430 : List Nat := [5, 3, 1, 1, 1, 10]
def baseStart_1985430 : Nat := 118140960795 + 1985430 * 2 ^ 59
def prefixEnd_1985430 : Nat := 4983230072969 + 3 ^ 40 * 1985430 * 2
def baseEnd_1985430 : Nat := 16781562071708184850933

theorem tailTrace_1985430 : CollatzResearch.WordTrace tailWord_1985430 prefixEnd_1985430 16781562071708184850933 := by
  unfold tailWord_1985430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4525911324820854330826109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48276387464755779528811829 4525911324820854330826109)
  ·
    refine ⟨1697216746807820374059791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4525911324820854330826109 1697216746807820374059791)
    ·
      refine ⟨2545825120211730561089687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1697216746807820374059791 2545825120211730561089687)
      ·
        refine ⟨3818737680317595841634531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545825120211730561089687 3818737680317595841634531)
        ·
          refine ⟨5728106520476393762451797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818737680317595841634531 5728106520476393762451797)
          ·
            refine ⟨16781562071708184850933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5728106520476393762451797 16781562071708184850933)
            ·
              rfl

theorem cell21_1985430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 10].length) (baseStart_1985430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985430 prefixEnd_1985430 := by exact prefixLift 1985430
  have htrace : WordTrace (prefixWord ++ tailWord_1985430) baseStart_1985430 baseEnd_1985430 := by
    simpa [prefixWord, tailWord_1985430, baseEnd_1985430] using wordTrace_append hprefix tailTrace_1985430
  have hstable : (prefixWord ++ tailWord_1985430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985430).length < 2 ^ (prefixWord ++ tailWord_1985430).sum := by decide
  have hdescent : baseEnd_1985430 < baseStart_1985430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985444 : List Nat := [2, 3, 1, 2, 1, 2, 3, 4, 3]
def baseStart_1985444 : Nat := 118140960795 + 1985444 * 2 ^ 59
def prefixEnd_1985444 : Nat := 4983230072969 + 3 ^ 40 * 1985444 * 2
def baseEnd_1985444 : Nat := 453105370926860077741829

theorem tailTrace_1985444 : CollatzResearch.WordTrace tailWord_1985444 prefixEnd_1985444 453105370926860077741829 := by
  unfold tailWord_1985444
  simp only [CollatzResearch.WordTrace]
  refine ⟨36207545909541474842113693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48276727879388633122818257 36207545909541474842113693)
  ·
    refine ⟨13577829716078053065792635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36207545909541474842113693 13577829716078053065792635)
    ·
      refine ⟨20366744574117079598688953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13577829716078053065792635 20366744574117079598688953)
      ·
        refine ⟨15275058430587809699016715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20366744574117079598688953 15275058430587809699016715)
        ·
          refine ⟨22912587645881714548525073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15275058430587809699016715 22912587645881714548525073)
          ·
            refine ⟨17184440734411285911393805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22912587645881714548525073 17184440734411285911393805)
            ·
              refine ⟨6444165275404232216772677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17184440734411285911393805 6444165275404232216772677)
              ·
                refine ⟨1208280989138293540644877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6444165275404232216772677 1208280989138293540644877)
                ·
                  refine ⟨453105370926860077741829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208280989138293540644877 453105370926860077741829)
                  ·
                    rfl

theorem cell21_1985444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_1985444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985444 prefixEnd_1985444 := by exact prefixLift 1985444
  have htrace : WordTrace (prefixWord ++ tailWord_1985444) baseStart_1985444 baseEnd_1985444 := by
    simpa [prefixWord, tailWord_1985444, baseEnd_1985444] using wordTrace_append hprefix tailTrace_1985444
  have hstable : (prefixWord ++ tailWord_1985444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985444).length < 2 ^ (prefixWord ++ tailWord_1985444).sum := by decide
  have hdescent : baseEnd_1985444 < baseStart_1985444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985455 : List Nat := [1, 1, 2, 1, 2, 2, 2, 10]
def baseStart_1985455 : Nat := 118140960795 + 1985455 * 2 ^ 59
def prefixEnd_1985455 : Nat := 4983230072969 + 3 ^ 40 * 1985455 * 2
def baseEnd_1985455 : Nat := 151035960425575501019491

theorem tailTrace_1985455 : CollatzResearch.WordTrace tailWord_1985455 prefixEnd_1985455 151035960425575501019491 := by
  unfold tailWord_1985455
  simp only [CollatzResearch.WordTrace]
  refine ⟨72415493022043098562877819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48276995348028732375251879 72415493022043098562877819)
  ·
    refine ⟨108623239533064647844316729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72415493022043098562877819 108623239533064647844316729)
    ·
      refine ⟨81467429649798485883237547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108623239533064647844316729 81467429649798485883237547)
      ·
        refine ⟨122201144474697728824856321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81467429649798485883237547 122201144474697728824856321)
        ·
          refine ⟨91650858356023296618642241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122201144474697728824856321 91650858356023296618642241)
          ·
            refine ⟨68738143767017472463981681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91650858356023296618642241 68738143767017472463981681)
            ·
              refine ⟨51553607825263104347986261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68738143767017472463981681 51553607825263104347986261)
              ·
                refine ⟨151035960425575501019491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51553607825263104347986261 151035960425575501019491)
                ·
                  rfl

theorem cell21_1985455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 10].length) (baseStart_1985455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985455 prefixEnd_1985455 := by exact prefixLift 1985455
  have htrace : WordTrace (prefixWord ++ tailWord_1985455) baseStart_1985455 baseEnd_1985455 := by
    simpa [prefixWord, tailWord_1985455, baseEnd_1985455] using wordTrace_append hprefix tailTrace_1985455
  have hstable : (prefixWord ++ tailWord_1985455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985455).length < 2 ^ (prefixWord ++ tailWord_1985455).sum := by decide
  have hdescent : baseEnd_1985455 < baseStart_1985455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985537 : List Nat := [1, 2, 4, 1, 2, 4, 1, 3, 3]
def baseStart_1985537 : Nat := 118140960795 + 1985537 * 2 ^ 59
def prefixEnd_1985537 : Nat := 4983230072969 + 3 ^ 40 * 1985537 * 2
def baseEnd_1985537 : Nat := 453126594793912582691639

theorem tailTrace_1985537 : CollatzResearch.WordTrace tailWord_1985537 prefixEnd_1985537 453126594793912582691639 := by
  unfold tailWord_1985537
  simp only [CollatzResearch.WordTrace]
  refine ⟨72418483807746026567362865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48278989205164017711575243 72418483807746026567362865)
  ·
    refine ⟨54313862855809519925522149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72418483807746026567362865 54313862855809519925522149)
    ·
      refine ⟨10183849285464284986035403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54313862855809519925522149 10183849285464284986035403)
      ·
        refine ⟨15275773928196427479053105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10183849285464284986035403 15275773928196427479053105)
        ·
          refine ⟨11456830446147320609289829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15275773928196427479053105 11456830446147320609289829)
          ·
            refine ⟨2148155708652622614241843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11456830446147320609289829 2148155708652622614241843)
            ·
              refine ⟨3222233562978933921362765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148155708652622614241843 3222233562978933921362765)
              ·
                refine ⟨1208337586117100220511037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3222233562978933921362765 1208337586117100220511037)
                ·
                  refine ⟨453126594793912582691639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208337586117100220511037 453126594793912582691639)
                  ·
                    rfl

theorem cell21_1985537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 3].length) (baseStart_1985537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985537 prefixEnd_1985537 := by exact prefixLift 1985537
  have htrace : WordTrace (prefixWord ++ tailWord_1985537) baseStart_1985537 baseEnd_1985537 := by
    simpa [prefixWord, tailWord_1985537, baseEnd_1985537] using wordTrace_append hprefix tailTrace_1985537
  have hstable : (prefixWord ++ tailWord_1985537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985537).length < 2 ^ (prefixWord ++ tailWord_1985537).sum := by decide
  have hdescent : baseEnd_1985537 < baseStart_1985537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985548 : List Nat := [2, 2, 1, 2, 3, 4, 7]
def baseStart_1985548 : Nat := 118140960795 + 1985548 * 2 ^ 59
def prefixEnd_1985548 : Nat := 4983230072969 + 3 ^ 40 * 1985548 * 2
def baseEnd_1985548 : Nat := 50347678349308778667587

theorem tailTrace_1985548 : CollatzResearch.WordTrace tailWord_1985548 prefixEnd_1985548 50347678349308778667587 := by
  unfold tailWord_1985548
  simp only [CollatzResearch.WordTrace]
  refine ⟨36209442505353087723006649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48279256673804116964008865 36209442505353087723006649)
  ·
    refine ⟨27157081879014815792254987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36209442505353087723006649 27157081879014815792254987)
    ·
      refine ⟨40735622818522223688382481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27157081879014815792254987 40735622818522223688382481)
      ·
        refine ⟨30551717113891667766286861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40735622818522223688382481 30551717113891667766286861)
        ·
          refine ⟨11456893917709375412357573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30551717113891667766286861 11456893917709375412357573)
          ·
            refine ⟨2148167609570507889817045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11456893917709375412357573 2148167609570507889817045)
            ·
              refine ⟨50347678349308778667587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2148167609570507889817045 50347678349308778667587)
              ·
                rfl

theorem cell21_1985548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 7].length) (baseStart_1985548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985548 prefixEnd_1985548 := by exact prefixLift 1985548
  have htrace : WordTrace (prefixWord ++ tailWord_1985548) baseStart_1985548 baseEnd_1985548 := by
    simpa [prefixWord, tailWord_1985548, baseEnd_1985548] using wordTrace_append hprefix tailTrace_1985548
  have hstable : (prefixWord ++ tailWord_1985548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985548).length < 2 ^ (prefixWord ++ tailWord_1985548).sum := by decide
  have hdescent : baseEnd_1985548 < baseStart_1985548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985565 : List Nat := [1, 4, 2, 2, 3, 1, 2, 6]
def baseStart_1985565 : Nat := 118140960795 + 1985565 * 2 ^ 59
def prefixEnd_1985565 : Nat := 4983230072969 + 3 ^ 40 * 1985565 * 2
def baseEnd_1985565 : Nat := 151044328258463585408305

theorem tailTrace_1985565 : CollatzResearch.WordTrace tailWord_1985565 prefixEnd_1985565 151044328258463585408305 := by
  unfold tailWord_1985565
  simp only [CollatzResearch.WordTrace]
  refine ⟨72419505051644587349382149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48279670034429724899588099 72419505051644587349382149)
  ·
    refine ⟨13578657197183360128009153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72419505051644587349382149 13578657197183360128009153)
    ·
      refine ⟨10183992897887520096006865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13578657197183360128009153 10183992897887520096006865)
      ·
        refine ⟨7637994673415640072005149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10183992897887520096006865 7637994673415640072005149)
        ·
          refine ⟨2864248002530865027001931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7637994673415640072005149 2864248002530865027001931)
          ·
            refine ⟨4296372003796297540502897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864248002530865027001931 4296372003796297540502897)
            ·
              refine ⟨3222279002847223155377173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4296372003796297540502897 3222279002847223155377173)
              ·
                refine ⟨151044328258463585408305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3222279002847223155377173 151044328258463585408305)
                ·
                  rfl

theorem cell21_1985565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 6].length) (baseStart_1985565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985565 prefixEnd_1985565 := by exact prefixLift 1985565
  have htrace : WordTrace (prefixWord ++ tailWord_1985565) baseStart_1985565 baseEnd_1985565 := by
    simpa [prefixWord, tailWord_1985565, baseEnd_1985565] using wordTrace_append hprefix tailTrace_1985565
  have hstable : (prefixWord ++ tailWord_1985565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985565).length < 2 ^ (prefixWord ++ tailWord_1985565).sum := by decide
  have hdescent : baseEnd_1985565 < baseStart_1985565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985607 : List Nat := [1, 1, 4, 1, 3, 11]
def baseStart_1985607 : Nat := 118140960795 + 1985607 * 2 ^ 59
def prefixEnd_1985607 : Nat := 4983230072969 + 3 ^ 40 * 1985607 * 2
def baseEnd_1985607 : Nat := 16783058138800296908327

theorem tailTrace_1985607 : CollatzResearch.WordTrace tailWord_1985607 prefixEnd_1985607 16783058138800296908327 := by
  unfold tailWord_1985607
  simp only [CollatzResearch.WordTrace]
  refine ⟨72421036917492428522411075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48280691278328285681607383 72421036917492428522411075)
  ·
    refine ⟨108631555376238642783616613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72421036917492428522411075 108631555376238642783616613)
    ·
      refine ⟨20368416633044745521928115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108631555376238642783616613 20368416633044745521928115)
      ·
        refine ⟨30552624949567118282892173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20368416633044745521928115 30552624949567118282892173)
        ·
          refine ⟨11457234356087669356084565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30552624949567118282892173 11457234356087669356084565)
          ·
            refine ⟨16783058138800296908327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11457234356087669356084565 16783058138800296908327)
            ·
              rfl

theorem cell21_1985607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 11].length) (baseStart_1985607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985607 prefixEnd_1985607 := by exact prefixLift 1985607
  have htrace : WordTrace (prefixWord ++ tailWord_1985607) baseStart_1985607 baseEnd_1985607 := by
    simpa [prefixWord, tailWord_1985607, baseEnd_1985607] using wordTrace_append hprefix tailTrace_1985607
  have hstable : (prefixWord ++ tailWord_1985607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985607).length < 2 ^ (prefixWord ++ tailWord_1985607).sum := by decide
  have hdescent : baseEnd_1985607 < baseStart_1985607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985613 : List Nat := [1, 6, 1, 1, 1, 3, 1, 4, 3]
def baseStart_1985613 : Nat := 118140960795 + 1985613 * 2 ^ 59
def prefixEnd_1985613 : Nat := 4983230072969 + 3 ^ 40 * 1985613 * 2
def baseEnd_1985613 : Nat := 453143939029353339424817

theorem tailTrace_1985613 : CollatzResearch.WordTrace tailWord_1985613 prefixEnd_1985613 453143939029353339424817 := by
  unfold tailWord_1985613
  simp only [CollatzResearch.WordTrace]
  refine ⟨72421255755470691547129493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48280837170313794364752995 72421255755470691547129493)
  ·
    refine ⟨3394746363537688666271695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72421255755470691547129493 3394746363537688666271695)
    ·
      refine ⟨5092119545306532999407543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3394746363537688666271695 5092119545306532999407543)
      ·
        refine ⟨7638179317959799499111315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092119545306532999407543 7638179317959799499111315)
        ·
          refine ⟨11457268976939699248666973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7638179317959799499111315 11457268976939699248666973)
          ·
            refine ⟨4296475866352387218250115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11457268976939699248666973 4296475866352387218250115)
            ·
              refine ⟨6444713799528580827375173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296475866352387218250115 6444713799528580827375173)
              ·
                refine ⟨1208383837411608905132845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6444713799528580827375173 1208383837411608905132845)
                ·
                  refine ⟨453143939029353339424817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208383837411608905132845 453143939029353339424817)
                  ·
                    rfl

theorem cell21_1985613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_1985613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985613 prefixEnd_1985613 := by exact prefixLift 1985613
  have htrace : WordTrace (prefixWord ++ tailWord_1985613) baseStart_1985613 baseEnd_1985613 := by
    simpa [prefixWord, tailWord_1985613, baseEnd_1985613] using wordTrace_append hprefix tailTrace_1985613
  have hstable : (prefixWord ++ tailWord_1985613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985613).length < 2 ^ (prefixWord ++ tailWord_1985613).sum := by decide
  have hdescent : baseEnd_1985613 < baseStart_1985613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985672 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 5]
def baseStart_1985672 : Nat := 118140960795 + 1985672 * 2 ^ 59
def prefixEnd_1985672 : Nat := 4983230072969 + 3 ^ 40 * 1985672 * 2
def baseEnd_1985672 : Nat := 453157403633182347941363

theorem tailTrace_1985672 : CollatzResearch.WordTrace tailWord_1985672 prefixEnd_1985672 453157403633182347941363 := by
  unfold tailWord_1985672
  simp only [CollatzResearch.WordTrace]
  refine ⟨36211703831128472311763635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48282271774837963082351513 36211703831128472311763635)
  ·
    refine ⟨54317555746692708467645453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36211703831128472311763635 54317555746692708467645453)
    ·
      refine ⟨20369083405009765675367045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54317555746692708467645453 20369083405009765675367045)
      ·
        refine ⟨3819203138439331064131321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20369083405009765675367045 3819203138439331064131321)
        ·
          refine ⟨2864402353829498298098491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3819203138439331064131321 2864402353829498298098491)
          ·
            refine ⟨4296603530744247447147737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864402353829498298098491 4296603530744247447147737)
            ·
              refine ⟨3222452648058185585360803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4296603530744247447147737 3222452648058185585360803)
              ·
                refine ⟨4833678972087278378041205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222452648058185585360803 4833678972087278378041205)
                ·
                  refine ⟨453157403633182347941363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4833678972087278378041205 453157403633182347941363)
                  ·
                    rfl

theorem cell21_1985672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_1985672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985672 prefixEnd_1985672 := by exact prefixLift 1985672
  have htrace : WordTrace (prefixWord ++ tailWord_1985672) baseStart_1985672 baseEnd_1985672 := by
    simpa [prefixWord, tailWord_1985672, baseEnd_1985672] using wordTrace_append hprefix tailTrace_1985672
  have hstable : (prefixWord ++ tailWord_1985672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985672).length < 2 ^ (prefixWord ++ tailWord_1985672).sum := by decide
  have hdescent : baseEnd_1985672 < baseStart_1985672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985700 : List Nat := [2, 3, 1, 2, 3, 2, 1, 7]
def baseStart_1985700 : Nat := 118140960795 + 1985700 * 2 ^ 59
def prefixEnd_1985700 : Nat := 4983230072969 + 3 ^ 40 * 1985700 * 2
def baseEnd_1985700 : Nat := 151054597871553507158213

theorem tailTrace_1985700 : CollatzResearch.WordTrace tailWord_1985700 prefixEnd_1985700 151054597871553507158213 := by
  unfold tailWord_1985700
  simp only [CollatzResearch.WordTrace]
  refine ⟨36212214453077752702773277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48282952604103670270364369 36212214453077752702773277)
  ·
    refine ⟨13579580419904157263539979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36212214453077752702773277 13579580419904157263539979)
    ·
      refine ⟨20369370629856235895309969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13579580419904157263539979 20369370629856235895309969)
      ·
        refine ⟨15277027972392176921482477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20369370629856235895309969 15277027972392176921482477)
        ·
          refine ⟨5728885489647066345555929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15277027972392176921482477 5728885489647066345555929)
          ·
            refine ⟨4296664117235299759166947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5728885489647066345555929 4296664117235299759166947)
            ·
              refine ⟨6444996175852949638750421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296664117235299759166947 6444996175852949638750421)
              ·
                refine ⟨151054597871553507158213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6444996175852949638750421 151054597871553507158213)
                ·
                  rfl

theorem cell21_1985700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_1985700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985700 prefixEnd_1985700 := by exact prefixLift 1985700
  have htrace : WordTrace (prefixWord ++ tailWord_1985700) baseStart_1985700 baseEnd_1985700 := by
    simpa [prefixWord, tailWord_1985700, baseEnd_1985700] using wordTrace_append hprefix tailTrace_1985700
  have hstable : (prefixWord ++ tailWord_1985700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985700).length < 2 ^ (prefixWord ++ tailWord_1985700).sum := by decide
  have hdescent : baseEnd_1985700 < baseStart_1985700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985706 : List Nat := [3, 1, 5, 1, 1, 3, 1, 3, 3]
def baseStart_1985706 : Nat := 118140960795 + 1985706 * 2 ^ 59
def prefixEnd_1985706 : Nat := 4983230072969 + 3 ^ 40 * 1985706 * 2
def baseEnd_1985706 : Nat := 453165162896405844374627

theorem tailTrace_1985706 : CollatzResearch.WordTrace tailWord_1985706 prefixEnd_1985706 453165162896405844374627 := by
  unfold tailWord_1985706
  simp only [CollatzResearch.WordTrace]
  refine ⟨18106161936033442107566243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48283098496089178953509981 18106161936033442107566243)
  ·
    refine ⟨27159242904050163161349365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18106161936033442107566243 27159242904050163161349365)
    ·
      refine ⟨2546179022254702796376503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27159242904050163161349365 2546179022254702796376503)
      ·
        refine ⟨3819268533382054194564755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2546179022254702796376503 3819268533382054194564755)
        ·
          refine ⟨5728902800073081291847133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819268533382054194564755 5728902800073081291847133)
          ·
            refine ⟨2148338550027405484442675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5728902800073081291847133 2148338550027405484442675)
            ·
              refine ⟨3222507825041108226664013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148338550027405484442675 3222507825041108226664013)
              ·
                refine ⟨1208440434390415584999005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3222507825041108226664013 1208440434390415584999005)
                ·
                  refine ⟨453165162896405844374627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208440434390415584999005 453165162896405844374627)
                  ·
                    rfl

theorem cell21_1985706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_1985706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985706 prefixEnd_1985706 := by exact prefixLift 1985706
  have htrace : WordTrace (prefixWord ++ tailWord_1985706) baseStart_1985706 baseEnd_1985706 := by
    simpa [prefixWord, tailWord_1985706, baseEnd_1985706] using wordTrace_append hprefix tailTrace_1985706
  have hstable : (prefixWord ++ tailWord_1985706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985706).length < 2 ^ (prefixWord ++ tailWord_1985706).sum := by decide
  have hdescent : baseEnd_1985706 < baseStart_1985706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985759 : List Nat := [1, 1, 2, 3, 2, 1, 4, 7]
def baseStart_1985759 : Nat := 118140960795 + 1985759 * 2 ^ 59
def prefixEnd_1985759 : Nat := 4983230072969 + 3 ^ 40 * 1985759 * 2
def baseEnd_1985759 : Nat := 151059086072829843330395

theorem tailTrace_1985759 : CollatzResearch.WordTrace tailWord_1985759 prefixEnd_1985759 151059086072829843330395 := by
  unfold tailWord_1985759
  simp only [CollatzResearch.WordTrace]
  refine ⟨72426580812941758481944331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48284387208627838987962887 72426580812941758481944331)
  ·
    refine ⟨108639871219412637722916497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72426580812941758481944331 108639871219412637722916497)
    ·
      refine ⟨81479903414559478292187373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108639871219412637722916497 81479903414559478292187373)
      ·
        refine ⟨30554963780459804359570265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81479903414559478292187373 30554963780459804359570265)
        ·
          refine ⟨22916222835344853269677699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30554963780459804359570265 22916222835344853269677699)
          ·
            refine ⟨34374334253017279904516549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22916222835344853269677699 34374334253017279904516549)
            ·
              refine ⟨6445187672440739982096853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34374334253017279904516549 6445187672440739982096853)
              ·
                refine ⟨151059086072829843330395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6445187672440739982096853 151059086072829843330395)
                ·
                  rfl

theorem cell21_1985759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 7].length) (baseStart_1985759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985759 prefixEnd_1985759 := by exact prefixLift 1985759
  have htrace : WordTrace (prefixWord ++ tailWord_1985759) baseStart_1985759 baseEnd_1985759 := by
    simpa [prefixWord, tailWord_1985759, baseEnd_1985759] using wordTrace_append hprefix tailTrace_1985759
  have hstable : (prefixWord ++ tailWord_1985759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985759).length < 2 ^ (prefixWord ++ tailWord_1985759).sum := by decide
  have hdescent : baseEnd_1985759 < baseStart_1985759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985880 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_1985880 : Nat := 118140960795 + 1985880 * 2 ^ 59
def prefixEnd_1985880 : Nat := 4983230072969 + 3 ^ 40 * 1985880 * 2
def baseEnd_1985880 : Nat := 453204872067020208474271

theorem tailTrace_1985880 : CollatzResearch.WordTrace tailWord_1985880 prefixEnd_1985880 453204872067020208474271 := by
  unfold tailWord_1985880
  simp only [CollatzResearch.WordTrace]
  refine ⟨36215497022751698073549547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48287329363668930764732729 36215497022751698073549547)
  ·
    refine ⟨54323245534127547110324321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36215497022751698073549547 54323245534127547110324321)
    ·
      refine ⟨40742434150595660332743241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54323245534127547110324321 40742434150595660332743241)
      ·
        refine ⟨30556825612946745249557431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40742434150595660332743241 30556825612946745249557431)
        ·
          refine ⟨45835238419420117874336147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30556825612946745249557431 45835238419420117874336147)
          ·
            refine ⟨68752857629130176811504221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45835238419420117874336147 68752857629130176811504221)
            ·
              refine ⟨25782321610923816304314083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68752857629130176811504221 25782321610923816304314083)
              ·
                refine ⟨38673482416385724456471125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25782321610923816304314083 38673482416385724456471125)
                ·
                  refine ⟨453204872067020208474271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38673482416385724456471125 453204872067020208474271)
                  ·
                    rfl

theorem cell21_1985880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_1985880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985880 prefixEnd_1985880 := by exact prefixLift 1985880
  have htrace : WordTrace (prefixWord ++ tailWord_1985880) baseStart_1985880 baseEnd_1985880 := by
    simpa [prefixWord, tailWord_1985880, baseEnd_1985880] using wordTrace_append hprefix tailTrace_1985880
  have hstable : (prefixWord ++ tailWord_1985880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985880).length < 2 ^ (prefixWord ++ tailWord_1985880).sum := by decide
  have hdescent : baseEnd_1985880 < baseStart_1985880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985911 : List Nat := [1, 1, 3, 1, 1, 2, 6, 6]
def baseStart_1985911 : Nat := 118140960795 + 1985911 * 2 ^ 59
def prefixEnd_1985911 : Nat := 4983230072969 + 3 ^ 40 * 1985911 * 2
def baseEnd_1985911 : Nat := 151070648896457014485847

theorem tailTrace_1985911 : CollatzResearch.WordTrace tailWord_1985911 prefixEnd_1985911 151070648896457014485847 := by
  unfold tailWord_1985911
  simp only [CollatzResearch.WordTrace]
  refine ⟨72432124708391088441477587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48288083138927392294318391 72432124708391088441477587)
  ·
    refine ⟨108648187062586632662216381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72432124708391088441477587 108648187062586632662216381)
    ·
      refine ⟨40743070148469987248331143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108648187062586632662216381 40743070148469987248331143)
      ·
        refine ⟨61114605222704980872496715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40743070148469987248331143 61114605222704980872496715)
        ·
          refine ⟨91671907834057471308745073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61114605222704980872496715 91671907834057471308745073)
          ·
            refine ⟨68753930875543103481558805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91671907834057471308745073 68753930875543103481558805)
            ·
              refine ⟨3222840509791082975698069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68753930875543103481558805 3222840509791082975698069)
              ·
                refine ⟨151070648896457014485847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3222840509791082975698069 151070648896457014485847)
                ·
                  rfl

theorem cell21_1985911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 6].length) (baseStart_1985911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1985911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1985911 prefixEnd_1985911 := by exact prefixLift 1985911
  have htrace : WordTrace (prefixWord ++ tailWord_1985911) baseStart_1985911 baseEnd_1985911 := by
    simpa [prefixWord, tailWord_1985911, baseEnd_1985911] using wordTrace_append hprefix tailTrace_1985911
  have hstable : (prefixWord ++ tailWord_1985911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985911).length < 2 ^ (prefixWord ++ tailWord_1985911).sum := by decide
  have hdescent : baseEnd_1985911 < baseStart_1985911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986004 : List Nat := [2, 4, 1, 2, 3, 1, 8]
def baseStart_1986004 : Nat := 118140960795 + 1986004 * 2 ^ 59
def prefixEnd_1986004 : Nat := 4983230072969 + 3 ^ 40 * 1986004 * 2
def baseEnd_1986004 : Nat := 50359241172935949823039

theorem tailTrace_1986004 : CollatzResearch.WordTrace tailWord_1986004 prefixEnd_1986004 50359241172935949823039 := by
  unfold tailWord_1986004
  simp only [CollatzResearch.WordTrace]
  refine ⟨36217758348527082662306533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48290344464702776883075377 36217758348527082662306533)
  ·
    refine ⟨6790829690348827999182475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36217758348527082662306533 6790829690348827999182475)
    ·
      refine ⟨10186244535523241998773713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6790829690348827999182475 10186244535523241998773713)
      ·
        refine ⟨7639683401642431499080285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10186244535523241998773713 7639683401642431499080285)
        ·
          refine ⟨2864881275615911812155107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7639683401642431499080285 2864881275615911812155107)
          ·
            refine ⟨4297321913423867718232661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864881275615911812155107 4297321913423867718232661)
            ·
              refine ⟨50359241172935949823039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4297321913423867718232661 50359241172935949823039)
              ·
                rfl

theorem cell21_1986004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 8].length) (baseStart_1986004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986004 prefixEnd_1986004 := by exact prefixLift 1986004
  have htrace : WordTrace (prefixWord ++ tailWord_1986004) baseStart_1986004 baseEnd_1986004 := by
    simpa [prefixWord, tailWord_1986004, baseEnd_1986004] using wordTrace_append hprefix tailTrace_1986004
  have hstable : (prefixWord ++ tailWord_1986004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986004).length < 2 ^ (prefixWord ++ tailWord_1986004).sum := by decide
  have hdescent : baseEnd_1986004 < baseStart_1986004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986080 : List Nat := [2, 1, 1, 6, 1, 2, 2, 6]
def baseStart_1986080 : Nat := 118140960795 + 1986080 * 2 ^ 59
def prefixEnd_1986080 : Nat := 4983230072969 + 3 ^ 40 * 1986080 * 2
def baseEnd_1986080 : Nat := 151083504930621435046843

theorem tailTrace_1986080 : CollatzResearch.WordTrace tailWord_1986080 prefixEnd_1986080 151083504930621435046843 := by
  unfold tailWord_1986080
  simp only [CollatzResearch.WordTrace]
  refine ⟨36219144322389415152189847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48292192429852553536253129 36219144322389415152189847)
  ·
    refine ⟨54328716483584122728284771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36219144322389415152189847 54328716483584122728284771)
    ·
      refine ⟨81493074725376184092427157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54328716483584122728284771 81493074725376184092427157)
      ·
        refine ⟨3819987877752008629332523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81493074725376184092427157 3819987877752008629332523)
        ·
          refine ⟨5729981816628012943998785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819987877752008629332523 5729981816628012943998785)
          ·
            refine ⟨4297486362471009707999089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5729981816628012943998785 4297486362471009707999089)
            ·
              refine ⟨3223114771853257280999317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4297486362471009707999089 3223114771853257280999317)
              ·
                refine ⟨151083504930621435046843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3223114771853257280999317 151083504930621435046843)
                ·
                  rfl

theorem cell21_1986080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_1986080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986080 prefixEnd_1986080 := by exact prefixLift 1986080
  have htrace : WordTrace (prefixWord ++ tailWord_1986080) baseStart_1986080 baseEnd_1986080 := by
    simpa [prefixWord, tailWord_1986080, baseEnd_1986080] using wordTrace_append hprefix tailTrace_1986080
  have hstable : (prefixWord ++ tailWord_1986080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986080).length < 2 ^ (prefixWord ++ tailWord_1986080).sum := by decide
  have hdescent : baseEnd_1986080 < baseStart_1986080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986083 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 4]
def baseStart_1986083 : Nat := 118140960795 + 1986083 * 2 ^ 59
def prefixEnd_1986083 : Nat := 4983230072969 + 3 ^ 40 * 1986083 * 2
def baseEnd_1986083 : Nat := 453251199432736966590523

theorem tailTrace_1986083 : CollatzResearch.WordTrace tailWord_1986083 prefixEnd_1986083 453251199432736966590523 := by
  unfold tailWord_1986083
  simp only [CollatzResearch.WordTrace]
  refine ⟨72438398063767961816738903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48292265375845307877825935 72438398063767961816738903)
  ·
    refine ⟨108657597095651942725108355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72438398063767961816738903 108657597095651942725108355)
    ·
      refine ⟨162986395643477914087662533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108657597095651942725108355 162986395643477914087662533)
      ·
        refine ⟨30559949183152108891436725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162986395643477914087662533 30559949183152108891436725)
        ·
          refine ⟨2864995235920510208572193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30559949183152108891436725 2864995235920510208572193)
          ·
            refine ⟨2148746426940382656429145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864995235920510208572193 2148746426940382656429145)
            ·
              refine ⟨1611559820205286992321859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148746426940382656429145 1611559820205286992321859)
              ·
                refine ⟨2417339730307930488482789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611559820205286992321859 2417339730307930488482789)
                ·
                  refine ⟨453251199432736966590523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2417339730307930488482789 453251199432736966590523)
                  ·
                    rfl

theorem cell21_1986083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 4].length) (baseStart_1986083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986083 prefixEnd_1986083 := by exact prefixLift 1986083
  have htrace : WordTrace (prefixWord ++ tailWord_1986083) baseStart_1986083 baseEnd_1986083 := by
    simpa [prefixWord, tailWord_1986083, baseEnd_1986083] using wordTrace_append hprefix tailTrace_1986083
  have hstable : (prefixWord ++ tailWord_1986083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986083).length < 2 ^ (prefixWord ++ tailWord_1986083).sum := by decide
  have hdescent : baseEnd_1986083 < baseStart_1986083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986153 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 7]
def baseStart_1986153 : Nat := 118140960795 + 1986153 * 2 ^ 59
def prefixEnd_1986153 : Nat := 4983230072969 + 3 ^ 40 * 1986153 * 2
def baseEnd_1986153 : Nat := 453267174386432400423713

theorem tailTrace_1986153 : CollatzResearch.WordTrace tailWord_1986153 prefixEnd_1986153 453267174386432400423713 := by
  unfold tailWord_1986153
  simp only [CollatzResearch.WordTrace]
  refine ⟨72440951173514363771787113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48293967449009575847858075 72440951173514363771787113)
  ·
    refine ⟨54330713380135772828840335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72440951173514363771787113 54330713380135772828840335)
    ·
      refine ⟨81496070070203659243260503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54330713380135772828840335 81496070070203659243260503)
      ·
        refine ⟨122244105105305488864890755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81496070070203659243260503 122244105105305488864890755)
        ·
          refine ⟨183366157657958233297336133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122244105105305488864890755 183366157657958233297336133)
          ·
            refine ⟨34381154560867168743250525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183366157657958233297336133 34381154560867168743250525)
            ·
              refine ⟨12892932960325188278718947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34381154560867168743250525 12892932960325188278718947)
              ·
                refine ⟨19339399440487782418078421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12892932960325188278718947 19339399440487782418078421)
                ·
                  refine ⟨453267174386432400423713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19339399440487782418078421 453267174386432400423713)
                  ·
                    rfl

theorem cell21_1986153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_1986153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986153 prefixEnd_1986153 := by exact prefixLift 1986153
  have htrace : WordTrace (prefixWord ++ tailWord_1986153) baseStart_1986153 baseEnd_1986153 := by
    simpa [prefixWord, tailWord_1986153, baseEnd_1986153] using wordTrace_append hprefix tailTrace_1986153
  have hstable : (prefixWord ++ tailWord_1986153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986153).length < 2 ^ (prefixWord ++ tailWord_1986153).sum := by decide
  have hdescent : baseEnd_1986153 < baseStart_1986153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986252 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 4]
def baseStart_1986252 : Nat := 118140960795 + 1986252 * 2 ^ 59
def prefixEnd_1986252 : Nat := 4983230072969 + 3 ^ 40 * 1986252 * 2
def baseEnd_1986252 : Nat := 453289767535230228273511

theorem tailTrace_1986252 : CollatzResearch.WordTrace tailWord_1986252 prefixEnd_1986252 453289767535230228273511 := by
  unfold tailWord_1986252
  simp only [CollatzResearch.WordTrace]
  refine ⟨36222281000077851839820505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48296374666770469119760673 36222281000077851839820505)
  ·
    refine ⟨27166710750058388879865379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36222281000077851839820505 27166710750058388879865379)
    ·
      refine ⟨40750066125087583319798069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27166710750058388879865379 40750066125087583319798069)
      ·
        refine ⟨3820318699226960936231069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40750066125087583319798069 3820318699226960936231069)
        ·
          refine ⟨1432619512210110351086651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3820318699226960936231069 1432619512210110351086651)
          ·
            refine ⟨2148929268315165526629977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432619512210110351086651 2148929268315165526629977)
            ·
              refine ⟨1611696951236374144972483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148929268315165526629977 1611696951236374144972483)
              ·
                refine ⟨2417545426854561217458725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611696951236374144972483 2417545426854561217458725)
                ·
                  refine ⟨453289767535230228273511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2417545426854561217458725 453289767535230228273511)
                  ·
                    rfl

theorem cell21_1986252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_1986252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986252 prefixEnd_1986252 := by exact prefixLift 1986252
  have htrace : WordTrace (prefixWord ++ tailWord_1986252) baseStart_1986252 baseEnd_1986252 := by
    simpa [prefixWord, tailWord_1986252, baseEnd_1986252] using wordTrace_append hprefix tailTrace_1986252
  have hstable : (prefixWord ++ tailWord_1986252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986252).length < 2 ^ (prefixWord ++ tailWord_1986252).sum := by decide
  have hdescent : baseEnd_1986252 < baseStart_1986252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986294 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1986294 : Nat := 118140960795 + 1986294 * 2 ^ 59
def prefixEnd_1986294 : Nat := 4983230072969 + 3 ^ 40 * 1986294 * 2
def baseEnd_1986294 : Nat := 453299352507447488573425

theorem tailTrace_1986294 : CollatzResearch.WordTrace tailWord_1986294 prefixEnd_1986294 453299352507447488573425 := by
  unfold tailWord_1986294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4527880866625221553291871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48297395910669029901779957 4527880866625221553291871)
  ·
    refine ⟨6791821299937832329937807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4527880866625221553291871 6791821299937832329937807)
    ·
      refine ⟨10187731949906748494906711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6791821299937832329937807 10187731949906748494906711)
      ·
        refine ⟨15281597924860122742360067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10187731949906748494906711 15281597924860122742360067)
        ·
          refine ⟨22922396887290184113540101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15281597924860122742360067 22922396887290184113540101)
          ·
            refine ⟨4297949416366909521288769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22922396887290184113540101 4297949416366909521288769)
            ·
              refine ⟨3223462062275182140966577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4297949416366909521288769 3223462062275182140966577)
              ·
                refine ⟨2417596546706386605724933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223462062275182140966577 2417596546706386605724933)
                ·
                  refine ⟨453299352507447488573425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2417596546706386605724933 453299352507447488573425)
                  ·
                    rfl

theorem cell21_1986294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1986294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986294 prefixEnd_1986294 := by exact prefixLift 1986294
  have htrace : WordTrace (prefixWord ++ tailWord_1986294) baseStart_1986294 baseEnd_1986294 := by
    simpa [prefixWord, tailWord_1986294, baseEnd_1986294] using wordTrace_append hprefix tailTrace_1986294
  have hstable : (prefixWord ++ tailWord_1986294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986294).length < 2 ^ (prefixWord ++ tailWord_1986294).sum := by decide
  have hdescent : baseEnd_1986294 < baseStart_1986294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986308 : List Nat := [2, 3, 2, 2, 1, 4, 1, 6]
def baseStart_1986308 : Nat := 118140960795 + 1986308 * 2 ^ 59
def prefixEnd_1986308 : Nat := 4983230072969 + 3 ^ 40 * 1986308 * 2
def baseEnd_1986308 : Nat := 151100849166062191780021

theorem tailTrace_1986308 : CollatzResearch.WordTrace tailWord_1986308 prefixEnd_1986308 151100849166062191780021 := by
  unfold tailWord_1986308
  simp only [CollatzResearch.WordTrace]
  refine ⟨36223302243976412621839789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48297736325301883495786385 36223302243976412621839789)
  ·
    refine ⟨13583738341491154733189921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36223302243976412621839789 13583738341491154733189921)
    ·
      refine ⟨10187803756118366049892441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13583738341491154733189921 10187803756118366049892441)
      ·
        refine ⟨7640852817088774537419331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10187803756118366049892441 7640852817088774537419331)
        ·
          refine ⟨11461279225633161806128997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7640852817088774537419331 11461279225633161806128997)
          ·
            refine ⟨2148989854806217838649187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11461279225633161806128997 2148989854806217838649187)
            ·
              refine ⟨3223484782209326757973781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148989854806217838649187 3223484782209326757973781)
              ·
                refine ⟨151100849166062191780021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3223484782209326757973781 151100849166062191780021)
                ·
                  rfl

theorem cell21_1986308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_1986308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986308 prefixEnd_1986308 := by exact prefixLift 1986308
  have htrace : WordTrace (prefixWord ++ tailWord_1986308) baseStart_1986308 baseEnd_1986308 := by
    simpa [prefixWord, tailWord_1986308, baseEnd_1986308] using wordTrace_append hprefix tailTrace_1986308
  have hstable : (prefixWord ++ tailWord_1986308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986308).length < 2 ^ (prefixWord ++ tailWord_1986308).sum := by decide
  have hdescent : baseEnd_1986308 < baseStart_1986308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986336 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_1986336 : Nat := 118140960795 + 1986336 * 2 ^ 59
def prefixEnd_1986336 : Nat := 4983230072969 + 3 ^ 40 * 1986336 * 2
def baseEnd_1986336 : Nat := 453308937479664748873339

theorem tailTrace_1986336 : CollatzResearch.WordTrace tailWord_1986336 prefixEnd_1986336 453308937479664748873339 := by
  unfold tailWord_1986336
  simp only [CollatzResearch.WordTrace]
  refine ⟨36223812865925693012849431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48298417154567590683799241 36223812865925693012849431)
  ·
    refine ⟨54335719298888539519274147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36223812865925693012849431 54335719298888539519274147)
    ·
      refine ⟨81503578948332809278911221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54335719298888539519274147 81503578948332809278911221)
      ·
        refine ⟨7640960526406200869897927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81503578948332809278911221 7640960526406200869897927)
        ·
          refine ⟨11461440789609301304846891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7640960526406200869897927 11461440789609301304846891)
          ·
            refine ⟨17192161184413951957270337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11461440789609301304846891 17192161184413951957270337)
            ·
              refine ⟨12894120888310463967952753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17192161184413951957270337 12894120888310463967952753)
              ·
                refine ⟨9670590666232847975964565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12894120888310463967952753 9670590666232847975964565)
                ·
                  refine ⟨453308937479664748873339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9670590666232847975964565 453308937479664748873339)
                  ·
                    rfl

theorem cell21_1986336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_1986336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986336 prefixEnd_1986336 := by exact prefixLift 1986336
  have htrace : WordTrace (prefixWord ++ tailWord_1986336) baseStart_1986336 baseEnd_1986336 := by
    simpa [prefixWord, tailWord_1986336, baseEnd_1986336] using wordTrace_append hprefix tailTrace_1986336
  have hstable : (prefixWord ++ tailWord_1986336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986336).length < 2 ^ (prefixWord ++ tailWord_1986336).sum := by decide
  have hdescent : baseEnd_1986336 < baseStart_1986336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986353 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 4]
def baseStart_1986353 : Nat := 118140960795 + 1986353 * 2 ^ 59
def prefixEnd_1986353 : Nat := 4983230072969 + 3 ^ 40 * 1986353 * 2
def baseEnd_1986353 : Nat := 453312817111276497089971

theorem tailTrace_1986353 : CollatzResearch.WordTrace tailWord_1986353 prefixEnd_1986353 453312817111276497089971 := by
  unfold tailWord_1986353
  simp only [CollatzResearch.WordTrace]
  refine ⟨72448245772789797929067713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48298830515193198619378475 72448245772789797929067713)
  ·
    refine ⟨54336184329592348446800785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72448245772789797929067713 54336184329592348446800785)
    ·
      refine ⟨40752138247194261335100589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54336184329592348446800785 40752138247194261335100589)
      ·
        refine ⟨15282051842697848000662721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40752138247194261335100589 15282051842697848000662721)
        ·
          refine ⟨11461538882023386000497041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15282051842697848000662721 11461538882023386000497041)
          ·
            refine ⟨8596154161517539500372781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11461538882023386000497041 8596154161517539500372781)
            ·
              refine ⟨3223557810569077312639793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8596154161517539500372781 3223557810569077312639793)
              ·
                refine ⟨2417668357926807984479845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223557810569077312639793 2417668357926807984479845)
                ·
                  refine ⟨453312817111276497089971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2417668357926807984479845 453312817111276497089971)
                  ·
                    rfl

theorem cell21_1986353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_1986353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986353 prefixEnd_1986353 := by exact prefixLift 1986353
  have htrace : WordTrace (prefixWord ++ tailWord_1986353) baseStart_1986353 baseEnd_1986353 := by
    simpa [prefixWord, tailWord_1986353, baseEnd_1986353] using wordTrace_append hprefix tailTrace_1986353
  have hstable : (prefixWord ++ tailWord_1986353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986353).length < 2 ^ (prefixWord ++ tailWord_1986353).sum := by decide
  have hdescent : baseEnd_1986353 < baseStart_1986353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986356 : List Nat := [2, 5, 1, 1, 2, 1, 2, 4, 3]
def baseStart_1986356 : Nat := 118140960795 + 1986356 * 2 ^ 59
def prefixEnd_1986356 : Nat := 4983230072969 + 3 ^ 40 * 1986356 * 2
def baseEnd_1986356 : Nat := 453313501752149158539965

theorem tailTrace_1986356 : CollatzResearch.WordTrace tailWord_1986356 prefixEnd_1986356 453313501752149158539965 := by
  unfold tailWord_1986356
  simp only [CollatzResearch.WordTrace]
  refine ⟨36224177595889464720713461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48298903461185952960951281 36224177595889464720713461)
  ·
    refine ⟨3396016649614637317566887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36224177595889464720713461 3396016649614637317566887)
    ·
      refine ⟨5094024974421955976350331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3396016649614637317566887 5094024974421955976350331)
      ·
        refine ⟨7641037461632933964525497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5094024974421955976350331 7641037461632933964525497)
        ·
          refine ⟨5730778096224700473394123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7641037461632933964525497 5730778096224700473394123)
          ·
            refine ⟨8596167144337050710091185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5730778096224700473394123 8596167144337050710091185)
            ·
              refine ⟨6447125358252788032568389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8596167144337050710091185 6447125358252788032568389)
              ·
                refine ⟨1208836004672397756106573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6447125358252788032568389 1208836004672397756106573)
                ·
                  refine ⟨453313501752149158539965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208836004672397756106573 453313501752149158539965)
                  ·
                    rfl

theorem cell21_1986356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_1986356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986356 prefixEnd_1986356 := by exact prefixLift 1986356
  have htrace : WordTrace (prefixWord ++ tailWord_1986356) baseStart_1986356 baseEnd_1986356 := by
    simpa [prefixWord, tailWord_1986356, baseEnd_1986356] using wordTrace_append hprefix tailTrace_1986356
  have hstable : (prefixWord ++ tailWord_1986356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986356).length < 2 ^ (prefixWord ++ tailWord_1986356).sum := by decide
  have hdescent : baseEnd_1986356 < baseStart_1986356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986412 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_1986412 : Nat := 118140960795 + 1986412 * 2 ^ 59
def prefixEnd_1986412 : Nat := 4983230072969 + 3 ^ 40 * 1986412 * 2
def baseEnd_1986412 : Nat := 453326281715105505606517

theorem tailTrace_1986412 : CollatzResearch.WordTrace tailWord_1986412 prefixEnd_1986412 453326281715105505606517 := by
  unfold tailWord_1986412
  simp only [CollatzResearch.WordTrace]
  refine ⟨36225198839788025502732745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48300265119717367336976993 36225198839788025502732745)
  ·
    refine ⟨27168899129841019127049559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36225198839788025502732745 27168899129841019127049559)
    ·
      refine ⟨40753348694761528690574339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27168899129841019127049559 40753348694761528690574339)
      ·
        refine ⟨61130023042142293035861509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40753348694761528690574339 61130023042142293035861509)
        ·
          refine ⟨11461879320401679944224033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61130023042142293035861509 11461879320401679944224033)
          ·
            refine ⟨8596409490301259958168025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11461879320401679944224033 8596409490301259958168025)
            ·
              refine ⟨6447307117725944968626019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8596409490301259958168025 6447307117725944968626019)
              ·
                refine ⟨9670960676588917452939029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6447307117725944968626019 9670960676588917452939029)
                ·
                  refine ⟨453326281715105505606517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9670960676588917452939029 453326281715105505606517)
                  ·
                    rfl

theorem cell21_1986412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_1986412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986412 prefixEnd_1986412 := by exact prefixLift 1986412
  have htrace : WordTrace (prefixWord ++ tailWord_1986412) baseStart_1986412 baseEnd_1986412 := by
    simpa [prefixWord, tailWord_1986412, baseEnd_1986412] using wordTrace_append hprefix tailTrace_1986412
  have hstable : (prefixWord ++ tailWord_1986412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986412).length < 2 ^ (prefixWord ++ tailWord_1986412).sum := by decide
  have hdescent : baseEnd_1986412 < baseStart_1986412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986426 : List Nat := [3, 1, 1, 1, 1, 1, 5, 8]
def baseStart_1986426 : Nat := 118140960795 + 1986426 * 2 ^ 59
def prefixEnd_1986426 : Nat := 4983230072969 + 3 ^ 40 * 1986426 * 2
def baseEnd_1986426 : Nat := 151109825568614864124385

theorem tailTrace_1986426 : CollatzResearch.WordTrace tailWord_1986426 prefixEnd_1986426 151109825568614864124385 := by
  unfold tailWord_1986426
  simp only [CollatzResearch.WordTrace]
  refine ⟨18112727075381332849118783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48300605534350220930983421 18112727075381332849118783)
  ·
    refine ⟨27169090613071999273678175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18112727075381332849118783 27169090613071999273678175)
    ·
      refine ⟨40753635919607998910517263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27169090613071999273678175 40753635919607998910517263)
      ·
        refine ⟨61130453879411998365775895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40753635919607998910517263 61130453879411998365775895)
        ·
          refine ⟨91695680819117997548663843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61130453879411998365775895 91695680819117997548663843)
          ·
            refine ⟨137543521228676996322995765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91695680819117997548663843 137543521228676996322995765)
            ·
              refine ⟨12894705115188468405280853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137543521228676996322995765 12894705115188468405280853)
              ·
                refine ⟨151109825568614864124385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12894705115188468405280853 151109825568614864124385)
                ·
                  rfl

theorem cell21_1986426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_1986426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986426 prefixEnd_1986426 := by exact prefixLift 1986426
  have htrace : WordTrace (prefixWord ++ tailWord_1986426) baseStart_1986426 baseEnd_1986426 := by
    simpa [prefixWord, tailWord_1986426, baseEnd_1986426] using wordTrace_append hprefix tailTrace_1986426
  have hstable : (prefixWord ++ tailWord_1986426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986426).length < 2 ^ (prefixWord ++ tailWord_1986426).sum := by decide
  have hdescent : baseEnd_1986426 < baseStart_1986426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986466 : List Nat := [3, 3, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1986466 : Nat := 118140960795 + 1986466 * 2 ^ 59
def prefixEnd_1986466 : Nat := 4983230072969 + 3 ^ 40 * 1986466 * 2
def baseEnd_1986466 : Nat := 453338605250813411706407

theorem tailTrace_1986466 : CollatzResearch.WordTrace tailWord_1986466 prefixEnd_1986466 453338605250813411706407 := by
  unfold tailWord_1986466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18113091805345104556982813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48301578147586945485287501 18113091805345104556982813)
  ·
    refine ⟨6792409427004414208868555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18113091805345104556982813 6792409427004414208868555)
    ·
      refine ⟨10188614140506621313302833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6792409427004414208868555 10188614140506621313302833)
      ·
        refine ⟨7641460605379965984977125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10188614140506621313302833 7641460605379965984977125)
        ·
          refine ⟨1432773863508743622183211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7641460605379965984977125 1432773863508743622183211)
          ·
            refine ⟨2149160795263115433274817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432773863508743622183211 2149160795263115433274817)
            ·
              refine ⟨1611870596447336574956113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2149160795263115433274817 1611870596447336574956113)
              ·
                refine ⟨1208902947335502431217085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611870596447336574956113 1208902947335502431217085)
                ·
                  refine ⟨453338605250813411706407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208902947335502431217085 453338605250813411706407)
                  ·
                    rfl

theorem cell21_1986466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1986466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986466 prefixEnd_1986466 := by exact prefixLift 1986466
  have htrace : WordTrace (prefixWord ++ tailWord_1986466) baseStart_1986466 baseEnd_1986466 := by
    simpa [prefixWord, tailWord_1986466, baseEnd_1986466] using wordTrace_append hprefix tailTrace_1986466
  have hstable : (prefixWord ++ tailWord_1986466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986466).length < 2 ^ (prefixWord ++ tailWord_1986466).sum := by decide
  have hdescent : baseEnd_1986466 < baseStart_1986466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986488 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 4]
def baseStart_1986488 : Nat := 118140960795 + 1986488 * 2 ^ 59
def prefixEnd_1986488 : Nat := 4983230072969 + 3 ^ 40 * 1986488 * 2
def baseEnd_1986488 : Nat := 453343625950546262339695

theorem tailTrace_1986488 : CollatzResearch.WordTrace tailWord_1986488 prefixEnd_1986488 453343625950546262339695 := by
  unfold tailWord_1986488
  simp only [CollatzResearch.WordTrace]
  refine ⟨36226584813650357992616059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48302113084867143990154745 36226584813650357992616059)
  ·
    refine ⟨54339877220475536988924089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36226584813650357992616059 54339877220475536988924089)
    ·
      refine ⟨40754907915356652741693067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54339877220475536988924089 40754907915356652741693067)
      ·
        refine ⟨61132361873034979112539601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40754907915356652741693067 61132361873034979112539601)
        ·
          refine ⟨45849271404776234334404701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61132361873034979112539601 45849271404776234334404701)
          ·
            refine ⟨17193476776791087875401763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45849271404776234334404701 17193476776791087875401763)
            ·
              refine ⟨25790215165186631813102645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17193476776791087875401763 25790215165186631813102645)
              ·
                refine ⟨2417832671736246732478373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25790215165186631813102645 2417832671736246732478373)
                ·
                  refine ⟨453343625950546262339695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2417832671736246732478373 453343625950546262339695)
                  ·
                    rfl

theorem cell21_1986488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_1986488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986488 prefixEnd_1986488 := by exact prefixLift 1986488
  have htrace : WordTrace (prefixWord ++ tailWord_1986488) baseStart_1986488 baseEnd_1986488 := by
    simpa [prefixWord, tailWord_1986488, baseEnd_1986488] using wordTrace_append hprefix tailTrace_1986488
  have hstable : (prefixWord ++ tailWord_1986488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986488).length < 2 ^ (prefixWord ++ tailWord_1986488).sum := by decide
  have hdescent : baseEnd_1986488 < baseStart_1986488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986522 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_1986522 : Nat := 118140960795 + 1986522 * 2 ^ 59
def prefixEnd_1986522 : Nat := 4983230072969 + 3 ^ 40 * 1986522 * 2
def baseEnd_1986522 : Nat := 453351385213769758772959

theorem tailTrace_1986522 : CollatzResearch.WordTrace tailWord_1986522 prefixEnd_1986522 453351385213769758772959 := by
  unfold tailWord_1986522
  simp only [CollatzResearch.WordTrace]
  refine ⟨18113602427294384947992455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48302939806118359861313213 18113602427294384947992455)
  ·
    refine ⟨27170403640941577421988683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18113602427294384947992455 27170403640941577421988683)
    ·
      refine ⟨40755605461412366132983025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27170403640941577421988683 40755605461412366132983025)
      ·
        refine ⟨30566704096059274599737269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40755605461412366132983025 30566704096059274599737269)
        ·
          refine ⟨2865628509005556993725369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30566704096059274599737269 2865628509005556993725369)
          ·
            refine ⟨2149221381754167745294027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2865628509005556993725369 2149221381754167745294027)
            ·
              refine ⟨3223832072631251617941041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149221381754167745294027 3223832072631251617941041)
              ·
                refine ⟨2417874054473438713455781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223832072631251617941041 2417874054473438713455781)
                ·
                  refine ⟨453351385213769758772959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2417874054473438713455781 453351385213769758772959)
                  ·
                    rfl

theorem cell21_1986522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_1986522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986522 prefixEnd_1986522 := by exact prefixLift 1986522
  have htrace : WordTrace (prefixWord ++ tailWord_1986522) baseStart_1986522 baseEnd_1986522 := by
    simpa [prefixWord, tailWord_1986522, baseEnd_1986522] using wordTrace_append hprefix tailTrace_1986522
  have hstable : (prefixWord ++ tailWord_1986522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986522).length < 2 ^ (prefixWord ++ tailWord_1986522).sum := by decide
  have hdescent : baseEnd_1986522 < baseStart_1986522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986567 : List Nat := [1, 1, 4, 3, 1, 2, 3, 3, 3]
def baseStart_1986567 : Nat := 118140960795 + 1986567 * 2 ^ 59
def prefixEnd_1986567 : Nat := 4983230072969 + 3 ^ 40 * 1986567 * 2
def baseEnd_1986567 : Nat := 453361654826859680522867

theorem tailTrace_1986567 : CollatzResearch.WordTrace tailWord_1986567 prefixEnd_1986567 453361654826859680522867 := by
  unfold tailWord_1986567
  simp only [CollatzResearch.WordTrace]
  refine ⟨72456050994014512477357955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48304033996009674984905303 72456050994014512477357955)
  ·
    refine ⟨108684076491021768716036933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72456050994014512477357955 108684076491021768716036933)
    ·
      refine ⟨20378264342066581634256925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108684076491021768716036933 20378264342066581634256925)
      ·
        refine ⟨7641849128274968112846347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20378264342066581634256925 7641849128274968112846347)
        ·
          refine ⟨11462773692412452169269521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7641849128274968112846347 11462773692412452169269521)
          ·
            refine ⟨8597080269309339126952141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11462773692412452169269521 8597080269309339126952141)
            ·
              refine ⟨3223905100991002172607053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8597080269309339126952141 3223905100991002172607053)
              ·
                refine ⟨1208964412871625814727645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3223905100991002172607053 1208964412871625814727645)
                ·
                  refine ⟨453361654826859680522867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208964412871625814727645 453361654826859680522867)
                  ·
                    rfl

theorem cell21_1986567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 3].length) (baseStart_1986567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986567 prefixEnd_1986567 := by exact prefixLift 1986567
  have htrace : WordTrace (prefixWord ++ tailWord_1986567) baseStart_1986567 baseEnd_1986567 := by
    simpa [prefixWord, tailWord_1986567, baseEnd_1986567] using wordTrace_append hprefix tailTrace_1986567
  have hstable : (prefixWord ++ tailWord_1986567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986567).length < 2 ^ (prefixWord ++ tailWord_1986567).sum := by decide
  have hdescent : baseEnd_1986567 < baseStart_1986567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986623 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 8]
def baseStart_1986623 : Nat := 118140960795 + 1986623 * 2 ^ 59
def prefixEnd_1986623 : Nat := 4983230072969 + 3 ^ 40 * 1986623 * 2
def baseEnd_1986623 : Nat := 453374434789816027589419

theorem tailTrace_1986623 : CollatzResearch.WordTrace tailWord_1986623 prefixEnd_1986623 453374434789816027589419 := by
  unfold tailWord_1986623
  simp only [CollatzResearch.WordTrace]
  refine ⟨72458093481811634041396523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48305395654541089360931015 72458093481811634041396523)
  ·
    refine ⟨108687140222717451062094785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72458093481811634041396523 108687140222717451062094785)
    ·
      refine ⟨81515355167038088296571089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108687140222717451062094785 81515355167038088296571089)
      ·
        refine ⟨61136516375278566222428317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81515355167038088296571089 61136516375278566222428317)
        ·
          refine ⟨22926193640729462333410619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61136516375278566222428317 22926193640729462333410619)
          ·
            refine ⟨34389290461094193500115929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22926193640729462333410619 34389290461094193500115929)
            ·
              refine ⟨25791967845820645125086947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34389290461094193500115929 25791967845820645125086947)
              ·
                refine ⟨38687951768730967687630421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25791967845820645125086947 38687951768730967687630421)
                ·
                  refine ⟨453374434789816027589419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38687951768730967687630421 453374434789816027589419)
                  ·
                    rfl

theorem cell21_1986623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_1986623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986623 prefixEnd_1986623 := by exact prefixLift 1986623
  have htrace : WordTrace (prefixWord ++ tailWord_1986623) baseStart_1986623 baseEnd_1986623 := by
    simpa [prefixWord, tailWord_1986623, baseEnd_1986623] using wordTrace_append hprefix tailTrace_1986623
  have hstable : (prefixWord ++ tailWord_1986623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986623).length < 2 ^ (prefixWord ++ tailWord_1986623).sum := by decide
  have hdescent : baseEnd_1986623 < baseStart_1986623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986671 : List Nat := [1, 1, 2, 1, 3, 5, 3, 5]
def baseStart_1986671 : Nat := 118140960795 + 1986671 * 2 ^ 59
def prefixEnd_1986671 : Nat := 4983230072969 + 3 ^ 40 * 1986671 * 2
def baseEnd_1986671 : Nat := 151128463014592870263107

theorem tailTrace_1986671 : CollatzResearch.WordTrace tailWord_1986671 prefixEnd_1986671 151128463014592870263107 := by
  unfold tailWord_1986671
  simp only [CollatzResearch.WordTrace]
  refine ⟨72459844185637738239143867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48306562790425158826095911 72459844185637738239143867)
  ·
    refine ⟨108689766278456607358715801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72459844185637738239143867 108689766278456607358715801)
    ·
      refine ⟨81517324708842455519036851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108689766278456607358715801 81517324708842455519036851)
      ·
        refine ⟨122275987063263683278555277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81517324708842455519036851 122275987063263683278555277)
        ·
          refine ⟨45853495148723881229458229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122275987063263683278555277 45853495148723881229458229)
          ·
            refine ⟨4298765170192863865261709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45853495148723881229458229 4298765170192863865261709)
            ·
              refine ⟨1612036938822323949473141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4298765170192863865261709 1612036938822323949473141)
              ·
                refine ⟨151128463014592870263107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1612036938822323949473141 151128463014592870263107)
                ·
                  rfl

theorem cell21_1986671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 5].length) (baseStart_1986671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986671 prefixEnd_1986671 := by exact prefixLift 1986671
  have htrace : WordTrace (prefixWord ++ tailWord_1986671) baseStart_1986671 baseEnd_1986671 := by
    simpa [prefixWord, tailWord_1986671, baseEnd_1986671] using wordTrace_append hprefix tailTrace_1986671
  have hstable : (prefixWord ++ tailWord_1986671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986671).length < 2 ^ (prefixWord ++ tailWord_1986671).sum := by decide
  have hdescent : baseEnd_1986671 < baseStart_1986671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986753 : List Nat := [1, 2, 6, 1, 2, 1, 3, 2, 3]
def baseStart_1986753 : Nat := 118140960795 + 1986753 * 2 ^ 59
def prefixEnd_1986753 : Nat := 4983230072969 + 3 ^ 40 * 1986753 * 2
def baseEnd_1986753 : Nat := 453404102560964690422487

theorem tailTrace_1986753 : CollatzResearch.WordTrace tailWord_1986753 prefixEnd_1986753 453404102560964690422487 := by
  unfold tailWord_1986753
  simp only [CollatzResearch.WordTrace]
  refine ⟨72462834971340666243628913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48308556647560444162419275 72462834971340666243628913)
  ·
    refine ⟨54347126228505499682721685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72462834971340666243628913 54347126228505499682721685)
    ·
      refine ⟨2547521541961195297627579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54347126228505499682721685 2547521541961195297627579)
      ·
        refine ⟨3821282312941792946441369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547521541961195297627579 3821282312941792946441369)
        ·
          refine ⟨2865961734706344709831027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3821282312941792946441369 2865961734706344709831027)
          ·
            refine ⟨4298942602059517064746541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865961734706344709831027 4298942602059517064746541)
            ·
              refine ⟨1612103475772318899279953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4298942602059517064746541 1612103475772318899279953)
              ·
                refine ⟨1209077606829239174459965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612103475772318899279953 1209077606829239174459965)
                ·
                  refine ⟨453404102560964690422487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209077606829239174459965 453404102560964690422487)
                  ·
                    rfl

theorem cell21_1986753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 3].length) (baseStart_1986753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986753 prefixEnd_1986753 := by exact prefixLift 1986753
  have htrace : WordTrace (prefixWord ++ tailWord_1986753) baseStart_1986753 baseEnd_1986753 := by
    simpa [prefixWord, tailWord_1986753, baseEnd_1986753] using wordTrace_append hprefix tailTrace_1986753
  have hstable : (prefixWord ++ tailWord_1986753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986753).length < 2 ^ (prefixWord ++ tailWord_1986753).sum := by decide
  have hdescent : baseEnd_1986753 < baseStart_1986753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986764 : List Nat := [2, 2, 1, 6, 1, 1, 2, 6]
def baseStart_1986764 : Nat := 118140960795 + 1986764 * 2 ^ 59
def prefixEnd_1986764 : Nat := 4983230072969 + 3 ^ 40 * 1986764 * 2
def baseEnd_1986764 : Nat := 151135537636943705246377

theorem tailTrace_1986764 : CollatzResearch.WordTrace tailWord_1986764 prefixEnd_1986764 151135537636943705246377 := by
  unfold tailWord_1986764
  simp only [CollatzResearch.WordTrace]
  refine ⟨36231618087150407561139673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48308824116200543414852897 36231618087150407561139673)
  ·
    refine ⟨27173713565362805670854755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36231618087150407561139673 27173713565362805670854755)
    ·
      refine ⟨40760570348044208506282133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27173713565362805670854755 40760570348044208506282133)
      ·
        refine ⟨1910651735064572273731975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40760570348044208506282133 1910651735064572273731975)
        ·
          refine ⟨2865977602596858410597963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910651735064572273731975 2865977602596858410597963)
          ·
            refine ⟨4298966403895287615896945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865977602596858410597963 4298966403895287615896945)
            ·
              refine ⟨3224224802921465711922709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4298966403895287615896945 3224224802921465711922709)
              ·
                refine ⟨151135537636943705246377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3224224802921465711922709 151135537636943705246377)
                ·
                  rfl

theorem cell21_1986764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_1986764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986764 prefixEnd_1986764 := by exact prefixLift 1986764
  have htrace : WordTrace (prefixWord ++ tailWord_1986764) baseStart_1986764 baseEnd_1986764 := by
    simpa [prefixWord, tailWord_1986764, baseEnd_1986764] using wordTrace_append hprefix tailTrace_1986764
  have hstable : (prefixWord ++ tailWord_1986764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986764).length < 2 ^ (prefixWord ++ tailWord_1986764).sum := by decide
  have hdescent : baseEnd_1986764 < baseStart_1986764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986812 : List Nat := [2, 2, 2, 1, 4, 3, 2, 2, 3]
def baseStart_1986812 : Nat := 118140960795 + 1986812 * 2 ^ 59
def prefixEnd_1986812 : Nat := 4983230072969 + 3 ^ 40 * 1986812 * 2
def baseEnd_1986812 : Nat := 453417567164793698939033

theorem tailTrace_1986812 : CollatzResearch.WordTrace tailWord_1986812 prefixEnd_1986812 453417567164793698939033 := by
  unfold tailWord_1986812
  simp only [CollatzResearch.WordTrace]
  refine ⟨36232493439063459660013345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48309991252084612880017793 36232493439063459660013345)
  ·
    refine ⟨27174370079297594745010009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36232493439063459660013345 27174370079297594745010009)
    ·
      refine ⟨20380777559473196058757507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27174370079297594745010009 20380777559473196058757507)
      ·
        refine ⟨30571166339209794088136261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20380777559473196058757507 30571166339209794088136261)
        ·
          refine ⟨5732093688601836391525549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30571166339209794088136261 5732093688601836391525549)
          ·
            refine ⟨2149535133225688646822081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5732093688601836391525549 2149535133225688646822081)
            ·
              refine ⟨1612151349919266485116561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2149535133225688646822081 1612151349919266485116561)
              ·
                refine ⟨1209113512439449863837421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612151349919266485116561 1209113512439449863837421)
                ·
                  refine ⟨453417567164793698939033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209113512439449863837421 453417567164793698939033)
                  ·
                    rfl

theorem cell21_1986812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_1986812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986812 prefixEnd_1986812 := by exact prefixLift 1986812
  have htrace : WordTrace (prefixWord ++ tailWord_1986812) baseStart_1986812 baseEnd_1986812 := by
    simpa [prefixWord, tailWord_1986812, baseEnd_1986812] using wordTrace_append hprefix tailTrace_1986812
  have hstable : (prefixWord ++ tailWord_1986812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986812).length < 2 ^ (prefixWord ++ tailWord_1986812).sum := by decide
  have hdescent : baseEnd_1986812 < baseStart_1986812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986851 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 6]
def baseStart_1986851 : Nat := 118140960795 + 1986851 * 2 ^ 59
def prefixEnd_1986851 : Nat := 4983230072969 + 3 ^ 40 * 1986851 * 2
def baseEnd_1986851 : Nat := 453426467496138297788953

theorem tailTrace_1986851 : CollatzResearch.WordTrace tailWord_1986851 prefixEnd_1986851 453426467496138297788953 := by
  unfold tailWord_1986851
  simp only [CollatzResearch.WordTrace]
  refine ⟨72466409324985628980696407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48310939549990419320464271 72466409324985628980696407)
  ·
    refine ⟨108699613987478443471044611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72466409324985628980696407 108699613987478443471044611)
    ·
      refine ⟨163049420981217665206566917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108699613987478443471044611 163049420981217665206566917)
      ·
        refine ⟨30571766433978312226231297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163049420981217665206566917 30571766433978312226231297)
        ·
          refine ⟨22928824825483734169673473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30571766433978312226231297 22928824825483734169673473)
          ·
            refine ⟨17196618619112800627255105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22928824825483734169673473 17196618619112800627255105)
            ·
              refine ⟨12897463964334600470441329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17196618619112800627255105 12897463964334600470441329)
              ·
                refine ⟨9673097973250950352830997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12897463964334600470441329 9673097973250950352830997)
                ·
                  refine ⟨453426467496138297788953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9673097973250950352830997 453426467496138297788953)
                  ·
                    rfl

theorem cell21_1986851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_1986851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986851 prefixEnd_1986851 := by exact prefixLift 1986851
  have htrace : WordTrace (prefixWord ++ tailWord_1986851) baseStart_1986851 baseEnd_1986851 := by
    simpa [prefixWord, tailWord_1986851, baseEnd_1986851] using wordTrace_append hprefix tailTrace_1986851
  have hstable : (prefixWord ++ tailWord_1986851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986851).length < 2 ^ (prefixWord ++ tailWord_1986851).sum := by decide
  have hdescent : baseEnd_1986851 < baseStart_1986851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986930 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1986930 : Nat := 118140960795 + 1986930 * 2 ^ 59
def prefixEnd_1986930 : Nat := 4983230072969 + 3 ^ 40 * 1986930 * 2
def baseEnd_1986930 : Nat := 453444496372451715972125

theorem tailTrace_1986930 : CollatzResearch.WordTrace tailWord_1986930 prefixEnd_1986930 453444496372451715972125 := by
  unfold tailWord_1986930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18117322672924856368205561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48312860461132950315214829 18117322672924856368205561)
  ·
    refine ⟨13587992004693642276154171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18117322672924856368205561 13587992004693642276154171)
    ·
      refine ⟨20381988007040463414231257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13587992004693642276154171 20381988007040463414231257)
      ·
        refine ⟨15286491005280347560673443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20381988007040463414231257 15286491005280347560673443)
        ·
          refine ⟨22929736507920521341010165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15286491005280347560673443 22929736507920521341010165)
          ·
            refine ⟨2149662797617548875719703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22929736507920521341010165 2149662797617548875719703)
            ·
              refine ⟨3224494196426323313579555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149662797617548875719703 3224494196426323313579555)
              ·
                refine ⟨4836741294639484970369333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224494196426323313579555 4836741294639484970369333)
                ·
                  refine ⟨453444496372451715972125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4836741294639484970369333 453444496372451715972125)
                  ·
                    rfl

theorem cell21_1986930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1986930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1986930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1986930 prefixEnd_1986930 := by exact prefixLift 1986930
  have htrace : WordTrace (prefixWord ++ tailWord_1986930) baseStart_1986930 baseEnd_1986930 := by
    simpa [prefixWord, tailWord_1986930, baseEnd_1986930] using wordTrace_append hprefix tailTrace_1986930
  have hstable : (prefixWord ++ tailWord_1986930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986930).length < 2 ^ (prefixWord ++ tailWord_1986930).sum := by decide
  have hdescent : baseEnd_1986930 < baseStart_1986930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987017 : List Nat := [1, 2, 1, 1, 2, 1, 4, 9]
def baseStart_1987017 : Nat := 118140960795 + 1987017 * 2 ^ 59
def prefixEnd_1987017 : Nat := 4983230072969 + 3 ^ 40 * 1987017 * 2
def baseEnd_1987017 : Nat := 151154783652586299340649

theorem tailTrace_1987017 : CollatzResearch.WordTrace tailWord_1987017 prefixEnd_1987017 151154783652586299340649 := by
  unfold tailWord_1987017
  simp only [CollatzResearch.WordTrace]
  refine ⟨72472463842384239331239305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48314975894922826220826203 72472463842384239331239305)
  ·
    refine ⟨54354347881788179498429479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72472463842384239331239305 54354347881788179498429479)
    ·
      refine ⟨81531521822682269247644219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54354347881788179498429479 81531521822682269247644219)
      ·
        refine ⟨122297282734023403871466329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81531521822682269247644219 122297282734023403871466329)
        ·
          refine ⟨91722962050517552903599747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122297282734023403871466329 91722962050517552903599747)
          ·
            refine ⟨137584443075776329355399621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91722962050517552903599747 137584443075776329355399621)
            ·
              refine ⟨25797083076708061754137429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137584443075776329355399621 25797083076708061754137429)
              ·
                refine ⟨151154783652586299340649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25797083076708061754137429 151154783652586299340649)
                ·
                  rfl

theorem cell21_1987017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 9].length) (baseStart_1987017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987017 prefixEnd_1987017 := by exact prefixLift 1987017
  have htrace : WordTrace (prefixWord ++ tailWord_1987017) baseStart_1987017 baseEnd_1987017 := by
    simpa [prefixWord, tailWord_1987017, baseEnd_1987017] using wordTrace_append hprefix tailTrace_1987017
  have hstable : (prefixWord ++ tailWord_1987017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987017).length < 2 ^ (prefixWord ++ tailWord_1987017).sum := by decide
  have hdescent : baseEnd_1987017 < baseStart_1987017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987282 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_1987282 : Nat := 118140960795 + 1987282 * 2 ^ 59
def prefixEnd_1987282 : Nat := 4983230072969 + 3 ^ 40 * 1987282 * 2
def baseEnd_1987282 : Nat := 453524827568177326104739

theorem tailTrace_1987282 : CollatzResearch.WordTrace tailWord_1987282 prefixEnd_1987282 453524827568177326104739 := by
  unfold tailWord_1987282
  simp only [CollatzResearch.WordTrace]
  refine ⟨18120532296606047397409025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48321419457616126393090733 18120532296606047397409025)
  ·
    refine ⟨13590399222454535548056769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18120532296606047397409025 13590399222454535548056769)
    ·
      refine ⟨10192799416840901661042577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13590399222454535548056769 10192799416840901661042577)
      ·
        refine ⟨7644599562630676245781933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10192799416840901661042577 7644599562630676245781933)
        ·
          refine ⟨2866724835986503592168225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7644599562630676245781933 2866724835986503592168225)
          ·
            refine ⟨2150043626989877694126169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2866724835986503592168225 2150043626989877694126169)
            ·
              refine ⟨1612532720242408270594627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150043626989877694126169 1612532720242408270594627)
              ·
                refine ⟨2418799080363612405891941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612532720242408270594627 2418799080363612405891941)
                ·
                  refine ⟨453524827568177326104739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2418799080363612405891941 453524827568177326104739)
                  ·
                    rfl

theorem cell21_1987282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_1987282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987282 prefixEnd_1987282 := by exact prefixLift 1987282
  have htrace : WordTrace (prefixWord ++ tailWord_1987282) baseStart_1987282 baseEnd_1987282 := by
    simpa [prefixWord, tailWord_1987282, baseEnd_1987282] using wordTrace_append hprefix tailTrace_1987282
  have hstable : (prefixWord ++ tailWord_1987282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987282).length < 2 ^ (prefixWord ++ tailWord_1987282).sum := by decide
  have hdescent : baseEnd_1987282 < baseStart_1987282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987324 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 4]
def baseStart_1987324 : Nat := 118140960795 + 1987324 * 2 ^ 59
def prefixEnd_1987324 : Nat := 4983230072969 + 3 ^ 40 * 1987324 * 2
def baseEnd_1987324 : Nat := 453534412540394586404653

theorem tailTrace_1987324 : CollatzResearch.WordTrace tailWord_1987324 prefixEnd_1987324 453534412540394586404653 := by
  unfold tailWord_1987324
  simp only [CollatzResearch.WordTrace]
  refine ⟨36241830526136015381332513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48322440701514687175110017 36241830526136015381332513)
  ·
    refine ⟨27181372894602011535999385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36241830526136015381332513 27181372894602011535999385)
    ·
      refine ⟨20386029670951508651999539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27181372894602011535999385 20386029670951508651999539)
      ·
        refine ⟨30579044506427262977999309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20386029670951508651999539 30579044506427262977999309)
        ·
          refine ⟨11467141689910223616749741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30579044506427262977999309 11467141689910223616749741)
          ·
            refine ⟨4300178133716333856281153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11467141689910223616749741 4300178133716333856281153)
            ·
              refine ⟨3225133600287250392210865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4300178133716333856281153 3225133600287250392210865)
              ·
                refine ⟨2418850200215437794158149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225133600287250392210865 2418850200215437794158149)
                ·
                  refine ⟨453534412540394586404653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2418850200215437794158149 453534412540394586404653)
                  ·
                    rfl

theorem cell21_1987324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_1987324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987324 prefixEnd_1987324 := by exact prefixLift 1987324
  have htrace : WordTrace (prefixWord ++ tailWord_1987324) baseStart_1987324 baseEnd_1987324 := by
    simpa [prefixWord, tailWord_1987324, baseEnd_1987324] using wordTrace_append hprefix tailTrace_1987324
  have hstable : (prefixWord ++ tailWord_1987324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987324).length < 2 ^ (prefixWord ++ tailWord_1987324).sum := by decide
  have hdescent : baseEnd_1987324 < baseStart_1987324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987400 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 4]
def baseStart_1987400 : Nat := 118140960795 + 1987400 * 2 ^ 59
def prefixEnd_1987400 : Nat := 4983230072969 + 3 ^ 40 * 1987400 * 2
def baseEnd_1987400 : Nat := 453551756775835343137831

theorem tailTrace_1987400 : CollatzResearch.WordTrace tailWord_1987400 prefixEnd_1987400 453551756775835343137831 := by
  unfold tailWord_1987400
  simp only [CollatzResearch.WordTrace]
  refine ⟨36243216499998347871215827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48324288666664463828287769 36243216499998347871215827)
  ·
    refine ⟨54364824749997521806823741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36243216499998347871215827 54364824749997521806823741)
    ·
      refine ⟨20386809281249070677558903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54364824749997521806823741 20386809281249070677558903)
      ·
        refine ⟨30580213921873606016338355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20386809281249070677558903 30580213921873606016338355)
        ·
          refine ⟨45870320882810409024507533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30580213921873606016338355 45870320882810409024507533)
          ·
            refine ⟨17201370331053903384190325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45870320882810409024507533 17201370331053903384190325)
            ·
              refine ⟨1612628468536303442267843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17201370331053903384190325 1612628468536303442267843)
              ·
                refine ⟨2418942702804455163401765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612628468536303442267843 2418942702804455163401765)
                ·
                  refine ⟨453551756775835343137831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2418942702804455163401765 453551756775835343137831)
                  ·
                    rfl

theorem cell21_1987400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_1987400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987400 prefixEnd_1987400 := by exact prefixLift 1987400
  have htrace : WordTrace (prefixWord ++ tailWord_1987400) baseStart_1987400 baseEnd_1987400 := by
    simpa [prefixWord, tailWord_1987400, baseEnd_1987400] using wordTrace_append hprefix tailTrace_1987400
  have hstable : (prefixWord ++ tailWord_1987400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987400).length < 2 ^ (prefixWord ++ tailWord_1987400).sum := by decide
  have hdescent : baseEnd_1987400 < baseStart_1987400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987445 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 5]
def baseStart_1987445 : Nat := 118140960795 + 1987445 * 2 ^ 59
def prefixEnd_1987445 : Nat := 4983230072969 + 3 ^ 40 * 1987445 * 2
def baseEnd_1987445 : Nat := 453562026388925264887739

theorem tailTrace_1987445 : CollatzResearch.WordTrace tailWord_1987445 prefixEnd_1987445 453562026388925264887739 := by
  unfold tailWord_1987445
  simp only [CollatzResearch.WordTrace]
  refine ⟨72488074284833668427819789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48325382856555778951879859 72488074284833668427819789)
  ·
    refine ⟨27183027856812625660432421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72488074284833668427819789 27183027856812625660432421)
    ·
      refine ⟨5096817723152367311331079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27183027856812625660432421 5096817723152367311331079)
      ·
        refine ⟨7645226584728550966996619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5096817723152367311331079 7645226584728550966996619)
        ·
          refine ⟨11467839877092826450494929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7645226584728550966996619 11467839877092826450494929)
          ·
            refine ⟨8600879907819619837871197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11467839877092826450494929 8600879907819619837871197)
            ·
              refine ⟨3225329965432357439201699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8600879907819619837871197 3225329965432357439201699)
              ·
                refine ⟨4837994948148536158802549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3225329965432357439201699 4837994948148536158802549)
                ·
                  refine ⟨453562026388925264887739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4837994948148536158802549 453562026388925264887739)
                  ·
                    rfl

theorem cell21_1987445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_1987445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987445 prefixEnd_1987445 := by exact prefixLift 1987445
  have htrace : WordTrace (prefixWord ++ tailWord_1987445) baseStart_1987445 baseEnd_1987445 := by
    simpa [prefixWord, tailWord_1987445, baseEnd_1987445] using wordTrace_append hprefix tailTrace_1987445
  have hstable : (prefixWord ++ tailWord_1987445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987445).length < 2 ^ (prefixWord ++ tailWord_1987445).sum := by decide
  have hdescent : baseEnd_1987445 < baseStart_1987445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
