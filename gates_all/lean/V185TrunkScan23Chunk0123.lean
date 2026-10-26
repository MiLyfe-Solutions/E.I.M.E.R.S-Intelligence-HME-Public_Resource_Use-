import V185TrunkScan23Chunk0122

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_728097 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_728097 : Nat := 118140960795 + 728097 * 2 ^ 59
def prefixEnd_728097 : Nat := 4983230072969 + 3 ^ 40 * 728097 * 2
def baseEnd_728097 : Nat := 373863724096743050839049

theorem tailTrace_728097 : CollatzResearch.WordTrace tailWord_728097 prefixEnd_728097 373863724096743050839049 := by
  unfold tailWord_728097
  simp only [CollatzResearch.WordTrace]
  refine ⟨26555879243236392912774545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17703919495490928608516363 26555879243236392912774545)
  ·
    refine ⟨19916909432427294684580909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26555879243236392912774545 19916909432427294684580909)
    ·
      refine ⟨7468841037160235506717841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19916909432427294684580909 7468841037160235506717841)
      ·
        refine ⟨5601630777870176630038381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7468841037160235506717841 5601630777870176630038381)
        ·
          refine ⟨2100611541701316236264393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5601630777870176630038381 2100611541701316236264393)
          ·
            refine ⟨1575458656275987177198295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2100611541701316236264393 1575458656275987177198295)
            ·
              refine ⟨2363187984413980765797443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575458656275987177198295 2363187984413980765797443)
              ·
                refine ⟨3544781976620971148696165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363187984413980765797443 3544781976620971148696165)
                ·
                  refine ⟨664646620616432090380531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3544781976620971148696165 664646620616432090380531)
                  ·
                    refine ⟨996969930924648135570797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 664646620616432090380531 996969930924648135570797)
                    ·
                      refine ⟨373863724096743050839049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 996969930924648135570797 373863724096743050839049)
                      ·
                        rfl

theorem cell23_728097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_728097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728097 prefixEnd_728097 := by exact prefixLift 728097
  have htrace : WordTrace (prefixWord ++ tailWord_728097) baseStart_728097 baseEnd_728097 := by
    simpa [prefixWord, tailWord_728097, baseEnd_728097] using wordTrace_append hprefix tailTrace_728097
  have hstable : (prefixWord ++ tailWord_728097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728097).length < 2 ^ (prefixWord ++ tailWord_728097).sum := by decide
  have hdescent : baseEnd_728097 < baseStart_728097 := by decide
  rcases family_descends (prefixWord ++ tailWord_728097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728113 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 2, 6]
def baseStart_728113 : Nat := 118140960795 + 728113 * 2 ^ 59
def prefixEnd_728113 : Nat := 4983230072969 + 3 ^ 40 * 728113 * 2
def baseEnd_728113 : Nat := 124623979929071662746325

theorem tailTrace_728113 : CollatzResearch.WordTrace tailWord_728113 prefixEnd_728113 124623979929071662746325 := by
  unfold tailWord_728113
  simp only [CollatzResearch.WordTrace]
  refine ⟨26556462811178427645356993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17704308540785618430237995 26556462811178427645356993)
  ·
    refine ⟨19917347108383820734017745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26556462811178427645356993 19917347108383820734017745)
    ·
      refine ⟨14938010331287865550513309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19917347108383820734017745 14938010331287865550513309)
      ·
        refine ⟨5601753874232949581442491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14938010331287865550513309 5601753874232949581442491)
        ·
          refine ⟨8402630811349424372163737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5601753874232949581442491 8402630811349424372163737)
          ·
            refine ⟨6301973108512068279122803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8402630811349424372163737 6301973108512068279122803)
            ·
              refine ⟨9452959662768102418684205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6301973108512068279122803 9452959662768102418684205)
              ·
                refine ⟨3544859873538038407006577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9452959662768102418684205 3544859873538038407006577)
                ·
                  refine ⟨2658644905153528805254933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3544859873538038407006577 2658644905153528805254933)
                  ·
                    refine ⟨124623979929071662746325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2658644905153528805254933 124623979929071662746325)
                    ·
                      rfl

theorem cell23_728113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_728113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728113 prefixEnd_728113 := by exact prefixLift 728113
  have htrace : WordTrace (prefixWord ++ tailWord_728113) baseStart_728113 baseEnd_728113 := by
    simpa [prefixWord, tailWord_728113, baseEnd_728113] using wordTrace_append hprefix tailTrace_728113
  have hstable : (prefixWord ++ tailWord_728113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728113).length < 2 ^ (prefixWord ++ tailWord_728113).sum := by decide
  have hdescent : baseEnd_728113 < baseStart_728113 := by decide
  rcases family_descends (prefixWord ++ tailWord_728113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728114 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3]
def baseStart_728114 : Nat := 118140960795 + 728114 * 2 ^ 59
def prefixEnd_728114 : Nat := 4983230072969 + 3 ^ 40 * 728114 * 2
def baseEnd_728114 : Nat := 373872453267869484326471

theorem tailTrace_728114 : CollatzResearch.WordTrace tailWord_728114 prefixEnd_728114 373872453267869484326471 := by
  unfold tailWord_728114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6639124821043701204035849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17704332856116536544095597 6639124821043701204035849)
  ·
    refine ⟨4979343615782775903026887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6639124821043701204035849 4979343615782775903026887)
    ·
      refine ⟨7469015423674163854540331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4979343615782775903026887 7469015423674163854540331)
      ·
        refine ⟨11203523135511245781810497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7469015423674163854540331 11203523135511245781810497)
        ·
          refine ⟨8402642351633434336357873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11203523135511245781810497 8402642351633434336357873)
          ·
            refine ⟨6301981763725075752268405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8402642351633434336357873 6301981763725075752268405)
            ·
              refine ⟨590810790349225851775163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6301981763725075752268405 590810790349225851775163)
              ·
                refine ⟨886216185523838777662745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590810790349225851775163 886216185523838777662745)
                ·
                  refine ⟨664662139142879083247059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 886216185523838777662745 664662139142879083247059)
                  ·
                    refine ⟨996993208714318624870589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 664662139142879083247059 996993208714318624870589)
                    ·
                      refine ⟨373872453267869484326471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 996993208714318624870589 373872453267869484326471)
                      ·
                        rfl

theorem cell23_728114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_728114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728114 prefixEnd_728114 := by exact prefixLift 728114
  have htrace : WordTrace (prefixWord ++ tailWord_728114) baseStart_728114 baseEnd_728114 := by
    simpa [prefixWord, tailWord_728114, baseEnd_728114] using wordTrace_append hprefix tailTrace_728114
  have hstable : (prefixWord ++ tailWord_728114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728114).length < 2 ^ (prefixWord ++ tailWord_728114).sum := by decide
  have hdescent : baseEnd_728114 < baseStart_728114 := by decide
  rcases family_descends (prefixWord ++ tailWord_728114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728124 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 1, 3, 2]
def baseStart_728124 : Nat := 118140960795 + 728124 * 2 ^ 59
def prefixEnd_728124 : Nat := 4983230072969 + 3 ^ 40 * 728124 * 2
def baseEnd_728124 : Nat := 373877588074414445201425

theorem tailTrace_728124 : CollatzResearch.WordTrace tailWord_728124 prefixEnd_728124 373877588074414445201425 := by
  unfold tailWord_728124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13278432007069288262003713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17704576009425717682671617 13278432007069288262003713)
  ·
    refine ⟨9958824005301966196502785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13278432007069288262003713 9958824005301966196502785)
    ·
      refine ⟨7469118003976474647377089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9958824005301966196502785 7469118003976474647377089)
      ·
        refine ⟨5601838502982355985532817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7469118003976474647377089 5601838502982355985532817)
        ·
          refine ⟨4201378877236766989149613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5601838502982355985532817 4201378877236766989149613)
          ·
            refine ⟨1575517078963787620931105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4201378877236766989149613 1575517078963787620931105)
            ·
              refine ⟨1181637809222840715698329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575517078963787620931105 1181637809222840715698329)
              ·
                refine ⟨886228356917130536773747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1181637809222840715698329 886228356917130536773747)
                ·
                  refine ⟨1329342535375695805160621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886228356917130536773747 1329342535375695805160621)
                  ·
                    refine ⟨498503450765885926935233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329342535375695805160621 498503450765885926935233)
                    ·
                      refine ⟨373877588074414445201425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498503450765885926935233 373877588074414445201425)
                      ·
                        rfl

theorem cell23_728124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_728124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728124 prefixEnd_728124 := by exact prefixLift 728124
  have htrace : WordTrace (prefixWord ++ tailWord_728124) baseStart_728124 baseEnd_728124 := by
    simpa [prefixWord, tailWord_728124, baseEnd_728124] using wordTrace_append hprefix tailTrace_728124
  have hstable : (prefixWord ++ tailWord_728124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728124).length < 2 ^ (prefixWord ++ tailWord_728124).sum := by decide
  have hdescent : baseEnd_728124 < baseStart_728124 := by decide
  rcases family_descends (prefixWord ++ tailWord_728124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728133 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_728133 : Nat := 118140960795 + 728133 * 2 ^ 59
def prefixEnd_728133 : Nat := 4983230072969 + 3 ^ 40 * 728133 * 2
def baseEnd_728133 : Nat := 373882209400304909988883

theorem tailTrace_728133 : CollatzResearch.WordTrace tailWord_728133 prefixEnd_728133 373882209400304909988883 := by
  unfold tailWord_728133
  simp only [CollatzResearch.WordTrace]
  refine ⟨26557192271105971061085053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17704794847403980707390035 26557192271105971061085053)
  ·
    refine ⟨9958947101664739147906895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26557192271105971061085053 9958947101664739147906895)
    ·
      refine ⟨14938420652497108721860343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9958947101664739147906895 14938420652497108721860343)
      ·
        refine ⟨22407630978745663082790515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14938420652497108721860343 22407630978745663082790515)
        ·
          refine ⟨33611446468118494624185773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22407630978745663082790515 33611446468118494624185773)
          ·
            refine ⟨12604292425544435484069665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33611446468118494624185773 12604292425544435484069665)
            ·
              refine ⟨9453219319158326613052249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12604292425544435484069665 9453219319158326613052249)
              ·
                refine ⟨7089914489368744959789187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9453219319158326613052249 7089914489368744959789187)
                ·
                  refine ⟨10634871734053117439683781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7089914489368744959789187 10634871734053117439683781)
                  ·
                    refine ⟨1994038450134959519940709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10634871734053117439683781 1994038450134959519940709)
                    ·
                      refine ⟨373882209400304909988883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1994038450134959519940709 373882209400304909988883)
                      ·
                        rfl

theorem cell23_728133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_728133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728133 prefixEnd_728133 := by exact prefixLift 728133
  have htrace : WordTrace (prefixWord ++ tailWord_728133) baseStart_728133 baseEnd_728133 := by
    simpa [prefixWord, tailWord_728133, baseEnd_728133] using wordTrace_append hprefix tailTrace_728133
  have hstable : (prefixWord ++ tailWord_728133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728133).length < 2 ^ (prefixWord ++ tailWord_728133).sum := by decide
  have hdescent : baseEnd_728133 < baseStart_728133 := by decide
  rcases family_descends (prefixWord ++ tailWord_728133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728183 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_728183 : Nat := 118140960795 + 728183 * 2 ^ 59
def prefixEnd_728183 : Nat := 4983230072969 + 3 ^ 40 * 728183 * 2
def baseEnd_728183 : Nat := 373907883433029714363653

theorem tailTrace_728183 : CollatzResearch.WordTrace tailWord_728183 prefixEnd_728183 373907883433029714363653 := by
  unfold tailWord_728183
  simp only [CollatzResearch.WordTrace]
  refine ⟨26559015920924829600405203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17706010613949886400270135 26559015920924829600405203)
  ·
    refine ⟨39838523881387244400607805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26559015920924829600405203 39838523881387244400607805)
    ·
      refine ⟨14939446455520216650227927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39838523881387244400607805 14939446455520216650227927)
      ·
        refine ⟨22409169683280324975341891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14939446455520216650227927 22409169683280324975341891)
        ·
          refine ⟨33613754524920487463012837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22409169683280324975341891 33613754524920487463012837)
          ·
            refine ⟨6302578973422591399314907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33613754524920487463012837 6302578973422591399314907)
            ·
              refine ⟨9453868460133887098972361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6302578973422591399314907 9453868460133887098972361)
              ·
                refine ⟨7090401345100415324229271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9453868460133887098972361 7090401345100415324229271)
                ·
                  refine ⟨10635602017650622986343907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7090401345100415324229271 10635602017650622986343907)
                  ·
                    refine ⟨15953403026475934479515861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10635602017650622986343907 15953403026475934479515861)
                    ·
                      refine ⟨373907883433029714363653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15953403026475934479515861 373907883433029714363653)
                      ·
                        rfl

theorem cell23_728183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_728183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728183 prefixEnd_728183 := by exact prefixLift 728183
  have htrace : WordTrace (prefixWord ++ tailWord_728183) baseStart_728183 baseEnd_728183 := by
    simpa [prefixWord, tailWord_728183, baseEnd_728183] using wordTrace_append hprefix tailTrace_728183
  have hstable : (prefixWord ++ tailWord_728183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728183).length < 2 ^ (prefixWord ++ tailWord_728183).sum := by decide
  have hdescent : baseEnd_728183 < baseStart_728183 := by decide
  rcases family_descends (prefixWord ++ tailWord_728183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728257 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_728257 : Nat := 118140960795 + 728257 * 2 ^ 59
def prefixEnd_728257 : Nat := 4983230072969 + 3 ^ 40 * 728257 * 2
def baseEnd_728257 : Nat := 373945881001462424838313

theorem tailTrace_728257 : CollatzResearch.WordTrace tailWord_728257 prefixEnd_728257 373945881001462424838313 := by
  unfold tailWord_728257
  simp only [CollatzResearch.WordTrace]
  refine ⟨26561714922656740238599025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17707809948437826825732683 26561714922656740238599025)
  ·
    refine ⟨19921286191992555178949269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26561714922656740238599025 19921286191992555178949269)
    ·
      refine ⟨933810290249651024013247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19921286191992555178949269 933810290249651024013247)
      ·
        refine ⟨1400715435374476536019871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933810290249651024013247 1400715435374476536019871)
        ·
          refine ⟨2101073153061714804029807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400715435374476536019871 2101073153061714804029807)
          ·
            refine ⟨3151609729592572206044711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101073153061714804029807 3151609729592572206044711)
            ·
              refine ⟨4727414594388858309067067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151609729592572206044711 4727414594388858309067067)
              ·
                refine ⟨7091121891583287463600601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4727414594388858309067067 7091121891583287463600601)
                ·
                  refine ⟨5318341418687465597700451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7091121891583287463600601 5318341418687465597700451)
                  ·
                    refine ⟨7977512128031198396550677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5318341418687465597700451 7977512128031198396550677)
                    ·
                      refine ⟨373945881001462424838313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7977512128031198396550677 373945881001462424838313)
                      ·
                        rfl

theorem cell23_728257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_728257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728257 prefixEnd_728257 := by exact prefixLift 728257
  have htrace : WordTrace (prefixWord ++ tailWord_728257) baseStart_728257 baseEnd_728257 := by
    simpa [prefixWord, tailWord_728257, baseEnd_728257] using wordTrace_append hprefix tailTrace_728257
  have hstable : (prefixWord ++ tailWord_728257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728257).length < 2 ^ (prefixWord ++ tailWord_728257).sum := by decide
  have hdescent : baseEnd_728257 < baseStart_728257 := by decide
  rcases family_descends (prefixWord ++ tailWord_728257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728287 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 1, 5, 2]
def baseStart_728287 : Nat := 118140960795 + 728287 * 2 ^ 59
def prefixEnd_728287 : Nat := 4983230072969 + 3 ^ 40 * 728287 * 2
def baseEnd_728287 : Nat := 373961285421097307463175

theorem tailTrace_728287 : CollatzResearch.WordTrace tailWord_728287 prefixEnd_728287 373961285421097307463175 := by
  unfold tailWord_728287
  simp only [CollatzResearch.WordTrace]
  refine ⟨26562809112548055362191115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17708539408365370241460743 26562809112548055362191115)
  ·
    refine ⟨39844213668822083043286673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26562809112548055362191115 39844213668822083043286673)
    ·
      refine ⟨29883160251616562282465005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39844213668822083043286673 29883160251616562282465005)
      ·
        refine ⟨11206185094356210855924377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29883160251616562282465005 11206185094356210855924377)
        ·
          refine ⟨8404638820767158141943283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11206185094356210855924377 8404638820767158141943283)
          ·
            refine ⟨12606958231150737212914925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8404638820767158141943283 12606958231150737212914925)
            ·
              refine ⟨4727609336681526454843097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12606958231150737212914925 4727609336681526454843097)
              ·
                refine ⟨3545707002511144841132323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4727609336681526454843097 3545707002511144841132323)
                ·
                  refine ⟨5318560503766717261698485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545707002511144841132323 5318560503766717261698485)
                  ·
                    refine ⟨498615047228129743284233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5318560503766717261698485 498615047228129743284233)
                    ·
                      refine ⟨373961285421097307463175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498615047228129743284233 373961285421097307463175)
                      ·
                        rfl

theorem cell23_728287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_728287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728287 prefixEnd_728287 := by exact prefixLift 728287
  have htrace : WordTrace (prefixWord ++ tailWord_728287) baseStart_728287 baseEnd_728287 := by
    simpa [prefixWord, tailWord_728287, baseEnd_728287] using wordTrace_append hprefix tailTrace_728287
  have hstable : (prefixWord ++ tailWord_728287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728287).length < 2 ^ (prefixWord ++ tailWord_728287).sum := by decide
  have hdescent : baseEnd_728287 < baseStart_728287 := by decide
  rcases family_descends (prefixWord ++ tailWord_728287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728328 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 3, 1, 3]
def baseStart_728328 : Nat := 118140960795 + 728328 * 2 ^ 59
def prefixEnd_728328 : Nat := 4983230072969 + 3 ^ 40 * 728328 * 2
def baseEnd_728328 : Nat := 373982338127931647050487

theorem tailTrace_728328 : CollatzResearch.WordTrace tailWord_728328 prefixEnd_728328 373982338127931647050487 := by
  unfold tailWord_728328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13282152252699759682216819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17709536336933012909622425 13282152252699759682216819)
  ·
    refine ⟨19923228379049639523325229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13282152252699759682216819 19923228379049639523325229)
    ·
      refine ⟨7471210642143614821246961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19923228379049639523325229 7471210642143614821246961)
      ·
        refine ⟨5603407981607711115935221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7471210642143614821246961 5603407981607711115935221)
        ·
          refine ⟨525319498275722917118927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5603407981607711115935221 525319498275722917118927)
          ·
            refine ⟨787979247413584375678391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525319498275722917118927 787979247413584375678391)
            ·
              refine ⟨1181968871120376563517587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787979247413584375678391 1181968871120376563517587)
              ·
                refine ⟨1772953306680564845276381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181968871120376563517587 1772953306680564845276381)
                ·
                  refine ⟨664857490005211816978643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1772953306680564845276381 664857490005211816978643)
                  ·
                    refine ⟨997286235007817725467965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 664857490005211816978643 997286235007817725467965)
                    ·
                      refine ⟨373982338127931647050487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 997286235007817725467965 373982338127931647050487)
                      ·
                        rfl

theorem cell23_728328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_728328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728328 prefixEnd_728328 := by exact prefixLift 728328
  have htrace : WordTrace (prefixWord ++ tailWord_728328) baseStart_728328 baseEnd_728328 := by
    simpa [prefixWord, tailWord_728328, baseEnd_728328] using wordTrace_append hprefix tailTrace_728328
  have hstable : (prefixWord ++ tailWord_728328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728328).length < 2 ^ (prefixWord ++ tailWord_728328).sum := by decide
  have hdescent : baseEnd_728328 < baseStart_728328 := by decide
  rcases family_descends (prefixWord ++ tailWord_728328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728337 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 3]
def baseStart_728337 : Nat := 118140960795 + 728337 * 2 ^ 59
def prefixEnd_728337 : Nat := 4983230072969 + 3 ^ 40 * 728337 * 2
def baseEnd_728337 : Nat := 373986959453822111837945

theorem tailTrace_728337 : CollatzResearch.WordTrace tailWord_728337 prefixEnd_728337 373986959453822111837945 := by
  unfold tailWord_728337
  simp only [CollatzResearch.WordTrace]
  refine ⟨26564632762366913901511265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17709755174911275934340843 26564632762366913901511265)
  ·
    refine ⟨19923474571775185426133449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26564632762366913901511265 19923474571775185426133449)
    ·
      refine ⟨14942605928831389069600087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19923474571775185426133449 14942605928831389069600087)
      ·
        refine ⟨22413908893247083604400131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14942605928831389069600087 22413908893247083604400131)
        ·
          refine ⟨33620863339870625406600197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22413908893247083604400131 33620863339870625406600197)
          ·
            refine ⟨6303911876225742263737537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33620863339870625406600197 6303911876225742263737537)
            ·
              refine ⟨4727933907169306697803153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6303911876225742263737537 4727933907169306697803153)
              ·
                refine ⟨3545950430376980023352365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4727933907169306697803153 3545950430376980023352365)
                ·
                  refine ⟨1329731411391367508757137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3545950430376980023352365 1329731411391367508757137)
                  ·
                    refine ⟨997298558543525631567853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1329731411391367508757137 997298558543525631567853)
                    ·
                      refine ⟨373986959453822111837945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 997298558543525631567853 373986959453822111837945)
                      ·
                        rfl

theorem cell23_728337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_728337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728337 prefixEnd_728337 := by exact prefixLift 728337
  have htrace : WordTrace (prefixWord ++ tailWord_728337) baseStart_728337 baseEnd_728337 := by
    simpa [prefixWord, tailWord_728337, baseEnd_728337] using wordTrace_append hprefix tailTrace_728337
  have hstable : (prefixWord ++ tailWord_728337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728337).length < 2 ^ (prefixWord ++ tailWord_728337).sum := by decide
  have hdescent : baseEnd_728337 < baseStart_728337 := by decide
  rcases family_descends (prefixWord ++ tailWord_728337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728344 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 2, 4]
def baseStart_728344 : Nat := 118140960795 + 728344 * 2 ^ 59
def prefixEnd_728344 : Nat := 4983230072969 + 3 ^ 40 * 728344 * 2
def baseEnd_728344 : Nat := 124663517939467861483471

theorem tailTrace_728344 : CollatzResearch.WordTrace tailWord_728344 prefixEnd_728344 124663517939467861483471 := by
  unfold tailWord_728344
  simp only [CollatzResearch.WordTrace]
  refine ⟨13282444036670777048508043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17709925382227702731344057 13282444036670777048508043)
  ·
    refine ⟨19923666055006165572762065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13282444036670777048508043 19923666055006165572762065)
    ·
      refine ⟨14942749541254624179571549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19923666055006165572762065 14942749541254624179571549)
      ·
        refine ⟨5603531077970484067339331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14942749541254624179571549 5603531077970484067339331)
        ·
          refine ⟨8405296616955726101008997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5603531077970484067339331 8405296616955726101008997)
          ·
            refine ⟨1575993115679198643939187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8405296616955726101008997 1575993115679198643939187)
            ·
              refine ⟨2363989673518797965908781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575993115679198643939187 2363989673518797965908781)
              ·
                refine ⟨886496127569549237215793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2363989673518797965908781 886496127569549237215793)
                ·
                  refine ⟨664872095677161927911845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 886496127569549237215793 664872095677161927911845)
                  ·
                    refine ⟨124663517939467861483471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 664872095677161927911845 124663517939467861483471)
                    ·
                      rfl

theorem cell23_728344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_728344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728344 prefixEnd_728344 := by exact prefixLift 728344
  have htrace : WordTrace (prefixWord ++ tailWord_728344) baseStart_728344 baseEnd_728344 := by
    simpa [prefixWord, tailWord_728344, baseEnd_728344] using wordTrace_append hprefix tailTrace_728344
  have hstable : (prefixWord ++ tailWord_728344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728344).length < 2 ^ (prefixWord ++ tailWord_728344).sum := by decide
  have hdescent : baseEnd_728344 < baseStart_728344 := by decide
  rcases family_descends (prefixWord ++ tailWord_728344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728351 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 4]
def baseStart_728351 : Nat := 118140960795 + 728351 * 2 ^ 59
def prefixEnd_728351 : Nat := 4983230072969 + 3 ^ 40 * 728351 * 2
def baseEnd_728351 : Nat := 373994148182985057062881

theorem tailTrace_728351 : CollatzResearch.WordTrace tailWord_728351 prefixEnd_728351 373994148182985057062881 := by
  unfold tailWord_728351
  simp only [CollatzResearch.WordTrace]
  refine ⟨26565143384316194292520907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17710095589544129528347271 26565143384316194292520907)
  ·
    refine ⟨39847715076474291438781361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26565143384316194292520907 39847715076474291438781361)
    ·
      refine ⟨29885786307355718579086021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39847715076474291438781361 29885786307355718579086021)
      ·
        refine ⟨5603584932629197233578629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29885786307355718579086021 5603584932629197233578629)
        ·
          refine ⟨1050672174867974481295993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5603584932629197233578629 1050672174867974481295993)
          ·
            refine ⟨788004131150980860971995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050672174867974481295993 788004131150980860971995)
            ·
              refine ⟨1182006196726471291457993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788004131150980860971995 1182006196726471291457993)
              ·
                refine ⟨886504647544853468593495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1182006196726471291457993 886504647544853468593495)
                ·
                  refine ⟨1329756971317280202890243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886504647544853468593495 1329756971317280202890243)
                  ·
                    refine ⟨1994635456975920304335365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1329756971317280202890243 1994635456975920304335365)
                    ·
                      refine ⟨373994148182985057062881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1994635456975920304335365 373994148182985057062881)
                      ·
                        rfl

theorem cell23_728351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_728351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728351 prefixEnd_728351 := by exact prefixLift 728351
  have htrace : WordTrace (prefixWord ++ tailWord_728351) baseStart_728351 baseEnd_728351 := by
    simpa [prefixWord, tailWord_728351, baseEnd_728351] using wordTrace_append hprefix tailTrace_728351
  have hstable : (prefixWord ++ tailWord_728351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728351).length < 2 ^ (prefixWord ++ tailWord_728351).sum := by decide
  have hdescent : baseEnd_728351 < baseStart_728351 := by decide
  rcases family_descends (prefixWord ++ tailWord_728351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728371 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 1, 2, 3]
def baseStart_728371 : Nat := 118140960795 + 728371 * 2 ^ 59
def prefixEnd_728371 : Nat := 4983230072969 + 3 ^ 40 * 728371 * 2
def baseEnd_728371 : Nat := 374004417796074978812789

theorem tailTrace_728371 : CollatzResearch.WordTrace tailWord_728371 prefixEnd_728371 374004417796074978812789 := by
  unfold tailWord_728371
  simp only [CollatzResearch.WordTrace]
  refine ⟨26565872844243737708248967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17710581896162491805499311 26565872844243737708248967)
  ·
    refine ⟨39848809266365606562373451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26565872844243737708248967 39848809266365606562373451)
    ·
      refine ⟨59773213899548409843560177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39848809266365606562373451 59773213899548409843560177)
      ·
        refine ⟨44829910424661307382670133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59773213899548409843560177 44829910424661307382670133)
        ·
          refine ⟨4202804102311997567125325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44829910424661307382670133 4202804102311997567125325)
          ·
            refine ⟨1576051538366999087671997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4202804102311997567125325 1576051538366999087671997)
            ·
              refine ⟨591019326887624657876999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1576051538366999087671997 591019326887624657876999)
              ·
                refine ⟨886528990331436986815499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591019326887624657876999 886528990331436986815499)
                ·
                  refine ⟨1329793485497155480223249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886528990331436986815499 1329793485497155480223249)
                  ·
                    refine ⟨997345114122866610167437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1329793485497155480223249 997345114122866610167437)
                    ·
                      refine ⟨374004417796074978812789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 997345114122866610167437 374004417796074978812789)
                      ·
                        rfl

theorem cell23_728371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 2, 3].length) (baseStart_728371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728371 prefixEnd_728371 := by exact prefixLift 728371
  have htrace : WordTrace (prefixWord ++ tailWord_728371) baseStart_728371 baseEnd_728371 := by
    simpa [prefixWord, tailWord_728371, baseEnd_728371] using wordTrace_append hprefix tailTrace_728371
  have hstable : (prefixWord ++ tailWord_728371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728371).length < 2 ^ (prefixWord ++ tailWord_728371).sum := by decide
  have hdescent : baseEnd_728371 < baseStart_728371 := by decide
  rcases family_descends (prefixWord ++ tailWord_728371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728374 : List Nat := [5, 1, 2, 3, 1, 11]
def baseStart_728374 : Nat := 118140960795 + 728374 * 2 ^ 59
def prefixEnd_728374 : Nat := 4983230072969 + 3 ^ 40 * 728374 * 2
def baseEnd_728374 : Nat := 1539119169703862004425

theorem tailTrace_728374 : CollatzResearch.WordTrace tailWord_728374 prefixEnd_728374 1539119169703862004425 := by
  unfold tailWord_728374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660373891452054326288011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17710654842155246147072117 1660373891452054326288011)
  ·
    refine ⟨2490560837178081489432017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1660373891452054326288011 2490560837178081489432017)
    ·
      refine ⟨1867920627883561117074013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2490560837178081489432017 1867920627883561117074013)
      ·
        refine ⟨700470235456335418902755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1867920627883561117074013 700470235456335418902755)
        ·
          refine ⟨1050705353184503128354133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700470235456335418902755 1050705353184503128354133)
          ·
            refine ⟨1539119169703862004425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1050705353184503128354133 1539119169703862004425)
            ·
              rfl

theorem cell23_728374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 11].length) (baseStart_728374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728374 prefixEnd_728374 := by exact prefixLift 728374
  have htrace : WordTrace (prefixWord ++ tailWord_728374) baseStart_728374 baseEnd_728374 := by
    simpa [prefixWord, tailWord_728374, baseEnd_728374] using wordTrace_append hprefix tailTrace_728374
  have hstable : (prefixWord ++ tailWord_728374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728374).length < 2 ^ (prefixWord ++ tailWord_728374).sum := by decide
  have hdescent : baseEnd_728374 < baseStart_728374 := by decide
  rcases family_descends (prefixWord ++ tailWord_728374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728385 : List Nat := [1, 2, 5, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_728385 : Nat := 118140960795 + 728385 * 2 ^ 59
def prefixEnd_728385 : Nat := 4983230072969 + 3 ^ 40 * 728385 * 2
def baseEnd_728385 : Nat := 374011606525237924037725

theorem tailTrace_728385 : CollatzResearch.WordTrace tailWord_728385 prefixEnd_728385 374011606525237924037725 := by
  unfold tailWord_728385
  simp only [CollatzResearch.WordTrace]
  refine ⟨26566383466193018099258609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17710922310795345399505739 26566383466193018099258609)
  ·
    refine ⟨19924787599644763574443957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26566383466193018099258609 19924787599644763574443957)
    ·
      refine ⟨1867948837466696585104121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19924787599644763574443957 1867948837466696585104121)
      ·
        refine ⟨1400961628100022438828091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1867948837466696585104121 1400961628100022438828091)
        ·
          refine ⟨2101442442150033658242137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400961628100022438828091 2101442442150033658242137)
          ·
            refine ⟨1576081831612525243681603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2101442442150033658242137 1576081831612525243681603)
            ·
              refine ⟨2364122747418787865522405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1576081831612525243681603 2364122747418787865522405)
              ·
                refine ⟨443273015141022724785451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2364122747418787865522405 443273015141022724785451)
                ·
                  refine ⟨664909522711534087178177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443273015141022724785451 664909522711534087178177)
                  ·
                    refine ⟨498682142033650565383633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 664909522711534087178177 498682142033650565383633)
                    ·
                      refine ⟨374011606525237924037725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498682142033650565383633 374011606525237924037725)
                      ·
                        rfl

theorem cell23_728385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_728385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728385 prefixEnd_728385 := by exact prefixLift 728385
  have htrace : WordTrace (prefixWord ++ tailWord_728385) baseStart_728385 baseEnd_728385 := by
    simpa [prefixWord, tailWord_728385, baseEnd_728385] using wordTrace_append hprefix tailTrace_728385
  have hstable : (prefixWord ++ tailWord_728385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728385).length < 2 ^ (prefixWord ++ tailWord_728385).sum := by decide
  have hdescent : baseEnd_728385 < baseStart_728385 := by decide
  rcases family_descends (prefixWord ++ tailWord_728385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728428 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 1, 3, 2]
def baseStart_728428 : Nat := 118140960795 + 728428 * 2 ^ 59
def prefixEnd_728428 : Nat := 4983230072969 + 3 ^ 40 * 728428 * 2
def baseEnd_728428 : Nat := 374033686193381255800027

theorem tailTrace_728428 : CollatzResearch.WordTrace tailWord_728428 prefixEnd_728428 374033686193381255800027 := by
  unfold tailWord_728428
  simp only [CollatzResearch.WordTrace]
  refine ⟨13283975902518618221536969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17711967870024824295382625 13283975902518618221536969)
  ·
    refine ⟨9962981926888963666152727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13283975902518618221536969 9962981926888963666152727)
    ·
      refine ⟨14944472890333445499229091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9962981926888963666152727 14944472890333445499229091)
      ·
        refine ⟨22416709335500168248843637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14944472890333445499229091 22416709335500168248843637)
        ·
          refine ⟨2101566500203140773329091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22416709335500168248843637 2101566500203140773329091)
          ·
            refine ⟨3152349750304711159993637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101566500203140773329091 3152349750304711159993637)
            ·
              refine ⟨591065578182133342498807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3152349750304711159993637 591065578182133342498807)
              ·
                refine ⟨886598367273200013748211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591065578182133342498807 886598367273200013748211)
                ·
                  refine ⟨1329897550909800020622317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886598367273200013748211 1329897550909800020622317)
                  ·
                    refine ⟨498711581591175007733369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329897550909800020622317 498711581591175007733369)
                    ·
                      refine ⟨374033686193381255800027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498711581591175007733369 374033686193381255800027)
                      ·
                        rfl

theorem cell23_728428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 3, 2].length) (baseStart_728428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728428 prefixEnd_728428 := by exact prefixLift 728428
  have htrace : WordTrace (prefixWord ++ tailWord_728428) baseStart_728428 baseEnd_728428 := by
    simpa [prefixWord, tailWord_728428, baseEnd_728428] using wordTrace_append hprefix tailTrace_728428
  have hstable : (prefixWord ++ tailWord_728428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728428).length < 2 ^ (prefixWord ++ tailWord_728428).sum := by decide
  have hdescent : baseEnd_728428 < baseStart_728428 := by decide
  rcases family_descends (prefixWord ++ tailWord_728428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728484 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 1, 7, 2]
def baseStart_728484 : Nat := 118140960795 + 728484 * 2 ^ 59
def prefixEnd_728484 : Nat := 4983230072969 + 3 ^ 40 * 728484 * 2
def baseEnd_728484 : Nat := 374062441110033036699769

theorem tailTrace_728484 : CollatzResearch.WordTrace tailWord_728484 prefixEnd_728484 374062441110033036699769 := by
  unfold tailWord_728484
  simp only [CollatzResearch.WordTrace]
  refine ⟨13284997146417179003556253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17713329528556238671408337 13284997146417179003556253)
  ·
    refine ⟨4981873929906442126333595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13284997146417179003556253 4981873929906442126333595)
    ·
      refine ⟨7472810894859663189500393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4981873929906442126333595 7472810894859663189500393)
      ·
        refine ⟨5604608171144747392125295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7472810894859663189500393 5604608171144747392125295)
        ·
          refine ⟨8406912256717121088187943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5604608171144747392125295 8406912256717121088187943)
          ·
            refine ⟨12610368385075681632281915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8406912256717121088187943 12610368385075681632281915)
            ·
              refine ⟨18915552577613522448422873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12610368385075681632281915 18915552577613522448422873)
              ·
                refine ⟨14186664433210141836317155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18915552577613522448422873 14186664433210141836317155)
                ·
                  refine ⟨21279996649815212754475733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14186664433210141836317155 21279996649815212754475733)
                  ·
                    refine ⟨498749921480044048933025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21279996649815212754475733 498749921480044048933025)
                    ·
                      refine ⟨374062441110033036699769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498749921480044048933025 374062441110033036699769)
                      ·
                        rfl

theorem cell23_728484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_728484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728484 prefixEnd_728484 := by exact prefixLift 728484
  have htrace : WordTrace (prefixWord ++ tailWord_728484) baseStart_728484 baseEnd_728484 := by
    simpa [prefixWord, tailWord_728484, baseEnd_728484] using wordTrace_append hprefix tailTrace_728484
  have hstable : (prefixWord ++ tailWord_728484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728484).length < 2 ^ (prefixWord ++ tailWord_728484).sum := by decide
  have hdescent : baseEnd_728484 < baseStart_728484 := by decide
  rcases family_descends (prefixWord ++ tailWord_728484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728527 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 4]
def baseStart_728527 : Nat := 118140960795 + 728527 * 2 ^ 59
def prefixEnd_728527 : Nat := 4983230072969 + 3 ^ 40 * 728527 * 2
def baseEnd_728527 : Nat := 374084520778176368462071

theorem tailTrace_728527 : CollatzResearch.WordTrace tailWord_728527 prefixEnd_728527 374084520778176368462071 := by
  unfold tailWord_728527
  simp only [CollatzResearch.WordTrace]
  refine ⟨26571562631678576350927835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17714375087785717567285223 26571562631678576350927835)
  ·
    refine ⟨39857343947517864526391753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26571562631678576350927835 39857343947517864526391753)
    ·
      refine ⟨29893007960638398394793815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39857343947517864526391753 29893007960638398394793815)
      ·
        refine ⟨44839511940957597592190723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29893007960638398394793815 44839511940957597592190723)
        ·
          refine ⟨67259267911436396388286085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44839511940957597592190723 67259267911436396388286085)
          ·
            refine ⟨12611112733394324322803641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67259267911436396388286085 12611112733394324322803641)
            ·
              refine ⟨9458334550045743242102731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12611112733394324322803641 9458334550045743242102731)
              ·
                refine ⟨14187501825068614863154097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9458334550045743242102731 14187501825068614863154097)
                ·
                  refine ⟨10640626368801461147365573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14187501825068614863154097 10640626368801461147365573)
                  ·
                    refine ⟨1995117444150273965131045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10640626368801461147365573 1995117444150273965131045)
                    ·
                      refine ⟨374084520778176368462071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1995117444150273965131045 374084520778176368462071)
                      ·
                        rfl

theorem cell23_728527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_728527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728527 prefixEnd_728527 := by exact prefixLift 728527
  have htrace : WordTrace (prefixWord ++ tailWord_728527) baseStart_728527 baseEnd_728527 := by
    simpa [prefixWord, tailWord_728527, baseEnd_728527] using wordTrace_append hprefix tailTrace_728527
  have hstable : (prefixWord ++ tailWord_728527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728527).length < 2 ^ (prefixWord ++ tailWord_728527).sum := by decide
  have hdescent : baseEnd_728527 < baseStart_728527 := by decide
  rcases family_descends (prefixWord ++ tailWord_728527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728551 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_728551 : Nat := 118140960795 + 728551 * 2 ^ 59
def prefixEnd_728551 : Nat := 4983230072969 + 3 ^ 40 * 728551 * 2
def baseEnd_728551 : Nat := 374096844313884274561961

theorem tailTrace_728551 : CollatzResearch.WordTrace tailWord_728551 prefixEnd_728551 374096844313884274561961 := by
  unfold tailWord_728551
  simp only [CollatzResearch.WordTrace]
  refine ⟨26572437983591628449801507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17714958655727752299867671 26572437983591628449801507)
  ·
    refine ⟨39858656975387442674702261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26572437983591628449801507 39858656975387442674702261)
    ·
      refine ⟨3736749091442572750753337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39858656975387442674702261 3736749091442572750753337)
      ·
        refine ⟨2802561818581929563065003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3736749091442572750753337 2802561818581929563065003)
        ·
          refine ⟨4203842727872894344597505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802561818581929563065003 4203842727872894344597505)
          ·
            refine ⟨3152882045904670758448129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4203842727872894344597505 3152882045904670758448129)
            ·
              refine ⟨2364661534428503068836097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3152882045904670758448129 2364661534428503068836097)
              ·
                refine ⟨1773496150821377301627073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2364661534428503068836097 1773496150821377301627073)
                ·
                  refine ⟨1330122113116032976220305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1773496150821377301627073 1330122113116032976220305)
                  ·
                    refine ⟨997591584837024732165229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1330122113116032976220305 997591584837024732165229)
                    ·
                      refine ⟨374096844313884274561961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 997591584837024732165229 374096844313884274561961)
                      ·
                        rfl

theorem cell23_728551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_728551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728551 prefixEnd_728551 := by exact prefixLift 728551
  have htrace : WordTrace (prefixWord ++ tailWord_728551) baseStart_728551 baseEnd_728551 := by
    simpa [prefixWord, tailWord_728551, baseEnd_728551] using wordTrace_append hprefix tailTrace_728551
  have hstable : (prefixWord ++ tailWord_728551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728551).length < 2 ^ (prefixWord ++ tailWord_728551).sum := by decide
  have hdescent : baseEnd_728551 < baseStart_728551 := by decide
  rcases family_descends (prefixWord ++ tailWord_728551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728558 : List Nat := [4, 1, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_728558 : Nat := 118140960795 + 728558 * 2 ^ 59
def prefixEnd_728558 : Nat := 4983230072969 + 3 ^ 40 * 728558 * 2
def baseEnd_728558 : Nat := 124700146226155249058143

theorem tailTrace_728558 : CollatzResearch.WordTrace tailWord_728558 prefixEnd_728558 124700146226155249058143 := by
  unfold tailWord_728558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3321586661820783580663291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17715128863044179096870885 3321586661820783580663291)
  ·
    refine ⟨4982379992731175370994937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3321586661820783580663291 4982379992731175370994937)
    ·
      refine ⟨3736784994548381528246203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4982379992731175370994937 3736784994548381528246203)
      ·
        refine ⟨5605177491822572292369305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3736784994548381528246203 5605177491822572292369305)
        ·
          refine ⟨4203883118866929219276979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5605177491822572292369305 4203883118866929219276979)
          ·
            refine ⟨6305824678300393828915469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203883118866929219276979 6305824678300393828915469)
            ·
              refine ⟨2364684254362647685843301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6305824678300393828915469 2364684254362647685843301)
              ·
                refine ⟨443378297692996441095619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2364684254362647685843301 443378297692996441095619)
                ·
                  refine ⟨665067446539494661643429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443378297692996441095619 665067446539494661643429)
                  ·
                    refine ⟨124700146226155249058143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 665067446539494661643429 124700146226155249058143)
                    ·
                      rfl

theorem cell23_728558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_728558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728558 prefixEnd_728558 := by exact prefixLift 728558
  have htrace : WordTrace (prefixWord ++ tailWord_728558) baseStart_728558 baseEnd_728558 := by
    simpa [prefixWord, tailWord_728558, baseEnd_728558] using wordTrace_append hprefix tailTrace_728558
  have hstable : (prefixWord ++ tailWord_728558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728558).length < 2 ^ (prefixWord ++ tailWord_728558).sum := by decide
  have hdescent : baseEnd_728558 < baseStart_728558 := by decide
  rcases family_descends (prefixWord ++ tailWord_728558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728584 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 3, 5]
def baseStart_728584 : Nat := 118140960795 + 728584 * 2 ^ 59
def prefixEnd_728584 : Nat := 4983230072969 + 3 ^ 40 * 728584 * 2
def baseEnd_728584 : Nat := 124704596391827548483103

theorem tailTrace_728584 : CollatzResearch.WordTrace tailWord_728584 prefixEnd_728584 124704596391827548483103 := by
  unfold tailWord_728584
  simp only [CollatzResearch.WordTrace]
  refine ⟨13286820796236037542876403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17715761061648050057168537 13286820796236037542876403)
  ·
    refine ⟨19930231194354056314314605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13286820796236037542876403 19930231194354056314314605)
    ·
      refine ⟨7473836697882771117867977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19930231194354056314314605 7473836697882771117867977)
      ·
        refine ⟨5605377523412078338400983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7473836697882771117867977 5605377523412078338400983)
        ·
          refine ⟨8408066285118117507601475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5605377523412078338400983 8408066285118117507601475)
          ·
            refine ⟨12612099427677176261402213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8408066285118117507601475 12612099427677176261402213)
            ·
              refine ⟨2364768642689470549012915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12612099427677176261402213 2364768642689470549012915)
              ·
                refine ⟨3547152964034205823519373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364768642689470549012915 3547152964034205823519373)
                ·
                  refine ⟨1330182361512827183819765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3547152964034205823519373 1330182361512827183819765)
                  ·
                    refine ⟨124704596391827548483103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1330182361512827183819765 124704596391827548483103)
                    ·
                      rfl

theorem cell23_728584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_728584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728584 prefixEnd_728584 := by exact prefixLift 728584
  have htrace : WordTrace (prefixWord ++ tailWord_728584) baseStart_728584 baseEnd_728584 := by
    simpa [prefixWord, tailWord_728584, baseEnd_728584] using wordTrace_append hprefix tailTrace_728584
  have hstable : (prefixWord ++ tailWord_728584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728584).length < 2 ^ (prefixWord ++ tailWord_728584).sum := by decide
  have hdescent : baseEnd_728584 < baseStart_728584 := by decide
  rcases family_descends (prefixWord ++ tailWord_728584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728631 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 1, 6]
def baseStart_728631 : Nat := 118140960795 + 728631 * 2 ^ 59
def prefixEnd_728631 : Nat := 4983230072969 + 3 ^ 40 * 728631 * 2
def baseEnd_728631 : Nat := 124712640922081320520531

theorem tailTrace_728631 : CollatzResearch.WordTrace tailWord_728631 prefixEnd_728631 124712640922081320520531 := by
  unfold tailWord_728631
  simp only [CollatzResearch.WordTrace]
  refine ⟨26575355823301802112713747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17716903882201201408475831 26575355823301802112713747)
  ·
    refine ⟨39863033734952703169070621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26575355823301802112713747 39863033734952703169070621)
    ·
      refine ⟨14948637650607263688401483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39863033734952703169070621 14948637650607263688401483)
      ·
        refine ⟨22422956475910895532602225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14948637650607263688401483 22422956475910895532602225)
        ·
          refine ⟨16817217356933171649451669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22422956475910895532602225 16817217356933171649451669)
          ·
            refine ⟨788307063606242421068047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16817217356933171649451669 788307063606242421068047)
            ·
              refine ⟨1182460595409363631602071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788307063606242421068047 1182460595409363631602071)
              ·
                refine ⟨1773690893114045447403107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182460595409363631602071 1773690893114045447403107)
                ·
                  refine ⟨2660536339671068171104661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773690893114045447403107 2660536339671068171104661)
                  ·
                    refine ⟨124712640922081320520531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2660536339671068171104661 124712640922081320520531)
                    ·
                      rfl

theorem cell23_728631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_728631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728631 prefixEnd_728631 := by exact prefixLift 728631
  have htrace : WordTrace (prefixWord ++ tailWord_728631) baseStart_728631 baseEnd_728631 := by
    simpa [prefixWord, tailWord_728631, baseEnd_728631] using wordTrace_append hprefix tailTrace_728631
  have hstable : (prefixWord ++ tailWord_728631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728631).length < 2 ^ (prefixWord ++ tailWord_728631).sum := by decide
  have hdescent : baseEnd_728631 < baseStart_728631 := by decide
  rcases family_descends (prefixWord ++ tailWord_728631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728634 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_728634 : Nat := 118140960795 + 728634 * 2 ^ 59
def prefixEnd_728634 : Nat := 4983230072969 + 3 ^ 40 * 728634 * 2
def baseEnd_728634 : Nat := 374139463208207449824079

theorem tailTrace_728634 : CollatzResearch.WordTrace tailWord_728634 prefixEnd_728634 374139463208207449824079 := by
  unfold tailWord_728634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6643866310572733406268239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17716976828193955750048637 6643866310572733406268239)
  ·
    refine ⟨9965799465859100109402359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6643866310572733406268239 9965799465859100109402359)
    ·
      refine ⟨14948699198788650164103539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9965799465859100109402359 14948699198788650164103539)
      ·
        refine ⟨22423048798182975246155309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14948699198788650164103539 22423048798182975246155309)
        ·
          refine ⟨8408643299318615717308241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22423048798182975246155309 8408643299318615717308241)
          ·
            refine ⟨6306482474488961787981181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8408643299318615717308241 6306482474488961787981181)
            ·
              refine ⟨2364930927933360670492943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6306482474488961787981181 2364930927933360670492943)
              ·
                refine ⟨3547396391900041005739415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364930927933360670492943 3547396391900041005739415)
                ·
                  refine ⟨5321094587850061508609123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3547396391900041005739415 5321094587850061508609123)
                  ·
                    refine ⟨7981641881775092262913685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5321094587850061508609123 7981641881775092262913685)
                    ·
                      refine ⟨374139463208207449824079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7981641881775092262913685 374139463208207449824079)
                      ·
                        rfl

theorem cell23_728634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_728634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728634 prefixEnd_728634 := by exact prefixLift 728634
  have htrace : WordTrace (prefixWord ++ tailWord_728634) baseStart_728634 baseEnd_728634 := by
    simpa [prefixWord, tailWord_728634, baseEnd_728634] using wordTrace_append hprefix tailTrace_728634
  have hstable : (prefixWord ++ tailWord_728634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728634).length < 2 ^ (prefixWord ++ tailWord_728634).sum := by decide
  have hdescent : baseEnd_728634 < baseStart_728634 := by decide
  rcases family_descends (prefixWord ++ tailWord_728634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728658 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_728658 : Nat := 118140960795 + 728658 * 2 ^ 59
def prefixEnd_728658 : Nat := 4983230072969 + 3 ^ 40 * 728658 * 2
def baseEnd_728658 : Nat := 374151786743915355923969

theorem tailTrace_728658 : CollatzResearch.WordTrace tailWord_728658 prefixEnd_728658 374151786743915355923969 := by
  unfold tailWord_728658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6644085148550996430986657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17717560396135990482631085 6644085148550996430986657)
  ·
    refine ⟨4983063861413247323239993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6644085148550996430986657 4983063861413247323239993)
    ·
      refine ⟨3737297896059935492429995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4983063861413247323239993 3737297896059935492429995)
      ·
        refine ⟨5605946844089903238644993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3737297896059935492429995 5605946844089903238644993)
        ·
          refine ⟨4204460133067427428983745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5605946844089903238644993 4204460133067427428983745)
          ·
            refine ⟨3153345099800570571737809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4204460133067427428983745 3153345099800570571737809)
            ·
              refine ⟨2365008824850427928803357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3153345099800570571737809 2365008824850427928803357)
              ·
                refine ⟨886878309318910473301259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2365008824850427928803357 886878309318910473301259)
                ·
                  refine ⟨1330317463978365709951889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886878309318910473301259 1330317463978365709951889)
                  ·
                    refine ⟨997738097983774282463917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1330317463978365709951889 997738097983774282463917)
                    ·
                      refine ⟨374151786743915355923969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 997738097983774282463917 374151786743915355923969)
                      ·
                        rfl

theorem cell23_728658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_728658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728658 prefixEnd_728658 := by exact prefixLift 728658
  have htrace : WordTrace (prefixWord ++ tailWord_728658) baseStart_728658 baseEnd_728658 := by
    simpa [prefixWord, tailWord_728658, baseEnd_728658] using wordTrace_append hprefix tailTrace_728658
  have hstable : (prefixWord ++ tailWord_728658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728658).length < 2 ^ (prefixWord ++ tailWord_728658).sum := by decide
  have hdescent : baseEnd_728658 < baseStart_728658 := by decide
  rcases family_descends (prefixWord ++ tailWord_728658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728698 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2]
def baseStart_728698 : Nat := 118140960795 + 728698 * 2 ^ 59
def prefixEnd_728698 : Nat := 4983230072969 + 3 ^ 40 * 728698 * 2
def baseEnd_728698 : Nat := 374172325970095199423785

theorem tailTrace_728698 : CollatzResearch.WordTrace tailWord_728698 prefixEnd_728698 374172325970095199423785 := by
  unfold tailWord_728698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6644449878514768138850687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17718533009372715036935165 6644449878514768138850687)
  ·
    refine ⟨9966674817772152208276031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6644449878514768138850687 9966674817772152208276031)
    ·
      refine ⟨14950012226658228312414047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9966674817772152208276031 14950012226658228312414047)
      ·
        refine ⟨22425018339987342468621071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14950012226658228312414047 22425018339987342468621071)
        ·
          refine ⟨33637527509981013702931607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22425018339987342468621071 33637527509981013702931607)
          ·
            refine ⟨50456291264971520554397411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33637527509981013702931607 50456291264971520554397411)
            ·
              refine ⟨75684436897457280831596117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50456291264971520554397411 75684436897457280831596117)
              ·
                refine ⟨886926994892077509745267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 75684436897457280831596117 886926994892077509745267)
                ·
                  refine ⟨1330390492338116264617901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886926994892077509745267 1330390492338116264617901)
                  ·
                    refine ⟨498896434626793599231713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1330390492338116264617901 498896434626793599231713)
                    ·
                      refine ⟨374172325970095199423785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498896434626793599231713 374172325970095199423785)
                      ·
                        rfl

theorem cell23_728698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2].length) (baseStart_728698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728698 prefixEnd_728698 := by exact prefixLift 728698
  have htrace : WordTrace (prefixWord ++ tailWord_728698) baseStart_728698 baseEnd_728698 := by
    simpa [prefixWord, tailWord_728698, baseEnd_728698] using wordTrace_append hprefix tailTrace_728698
  have hstable : (prefixWord ++ tailWord_728698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728698).length < 2 ^ (prefixWord ++ tailWord_728698).sum := by decide
  have hdescent : baseEnd_728698 < baseStart_728698 := by decide
  rcases family_descends (prefixWord ++ tailWord_728698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728715 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 1, 3, 2]
def baseStart_728715 : Nat := 118140960795 + 728715 * 2 ^ 59
def prefixEnd_728715 : Nat := 4983230072969 + 3 ^ 40 * 728715 * 2
def baseEnd_728715 : Nat := 374181055141221632911207

theorem tailTrace_728715 : CollatzResearch.WordTrace tailWord_728715 prefixEnd_728715 374181055141221632911207 := by
  unfold tailWord_728715
  simp only [CollatzResearch.WordTrace]
  refine ⟨26578419554997484458771599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17718946369998322972514399 26578419554997484458771599)
  ·
    refine ⟨39867629332496226688157399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26578419554997484458771599 39867629332496226688157399)
    ·
      refine ⟨59801443998744340032236099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39867629332496226688157399 59801443998744340032236099)
      ·
        refine ⟨89702165998116510048354149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59801443998744340032236099 89702165998116510048354149)
        ·
          refine ⟨16819156124646845634066403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89702165998116510048354149 16819156124646845634066403)
          ·
            refine ⟨25228734186970268451099605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16819156124646845634066403 25228734186970268451099605)
            ·
              refine ⟨591298457507115666822647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25228734186970268451099605 591298457507115666822647)
              ·
                refine ⟨886947686260673500233971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591298457507115666822647 886947686260673500233971)
                ·
                  refine ⟨1330421529391010250350957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886947686260673500233971 1330421529391010250350957)
                  ·
                    refine ⟨498908073521628843881609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1330421529391010250350957 498908073521628843881609)
                    ·
                      refine ⟨374181055141221632911207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498908073521628843881609 374181055141221632911207)
                      ·
                        rfl

theorem cell23_728715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 3, 2].length) (baseStart_728715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728715 prefixEnd_728715 := by exact prefixLift 728715
  have htrace : WordTrace (prefixWord ++ tailWord_728715) baseStart_728715 baseEnd_728715 := by
    simpa [prefixWord, tailWord_728715, baseEnd_728715] using wordTrace_append hprefix tailTrace_728715
  have hstable : (prefixWord ++ tailWord_728715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728715).length < 2 ^ (prefixWord ++ tailWord_728715).sum := by decide
  have hdescent : baseEnd_728715 < baseStart_728715 := by decide
  rcases family_descends (prefixWord ++ tailWord_728715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728722 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_728722 : Nat := 118140960795 + 728722 * 2 ^ 59
def prefixEnd_728722 : Nat := 4983230072969 + 3 ^ 40 * 728722 * 2
def baseEnd_728722 : Nat := 374184649505803105523675

theorem tailTrace_728722 : CollatzResearch.WordTrace tailWord_728722 prefixEnd_728722 374184649505803105523675 := by
  unfold tailWord_728722
  simp only [CollatzResearch.WordTrace]
  refine ⟨6644668716493031163569105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17719116577314749769517613 6644668716493031163569105)
  ·
    refine ⟨4983501537369773372676829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6644668716493031163569105 4983501537369773372676829)
    ·
      refine ⟨1868813076513665014753811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4983501537369773372676829 1868813076513665014753811)
      ·
        refine ⟨2803219614770497522130717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868813076513665014753811 2803219614770497522130717)
        ·
          refine ⟨1051207355538936570799019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2803219614770497522130717 1051207355538936570799019)
          ·
            refine ⟨1576811033308404856198529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051207355538936570799019 1576811033308404856198529)
            ·
              refine ⟨1182608274981303642148897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1576811033308404856198529 1182608274981303642148897)
              ·
                refine ⟨886956206235977731611673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1182608274981303642148897 886956206235977731611673)
                ·
                  refine ⟨665217154676983298708755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 886956206235977731611673 665217154676983298708755)
                  ·
                    refine ⟨997825732015474948063133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 665217154676983298708755 997825732015474948063133)
                    ·
                      refine ⟨374184649505803105523675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 997825732015474948063133 374184649505803105523675)
                      ·
                        rfl

theorem cell23_728722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_728722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728722 prefixEnd_728722 := by exact prefixLift 728722
  have htrace : WordTrace (prefixWord ++ tailWord_728722) baseStart_728722 baseEnd_728722 := by
    simpa [prefixWord, tailWord_728722, baseEnd_728722] using wordTrace_append hprefix tailTrace_728722
  have hstable : (prefixWord ++ tailWord_728722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728722).length < 2 ^ (prefixWord ++ tailWord_728722).sum := by decide
  have hdescent : baseEnd_728722 < baseStart_728722 := by decide
  rcases family_descends (prefixWord ++ tailWord_728722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728768 : List Nat := [2, 1, 1, 2, 4, 1, 4, 3, 5]
def baseStart_728768 : Nat := 118140960795 + 728768 * 2 ^ 59
def prefixEnd_728768 : Nat := 4983230072969 + 3 ^ 40 * 728768 * 2
def baseEnd_728768 : Nat := 41578696623989991727607

theorem tailTrace_728768 : CollatzResearch.WordTrace tailWord_728768 prefixEnd_728768 41578696623989991727607 := by
  unfold tailWord_728768
  simp only [CollatzResearch.WordTrace]
  refine ⟨13290176311902737255225479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17720235082536983006967305 13290176311902737255225479)
  ·
    refine ⟨19935264467854105882838219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13290176311902737255225479 19935264467854105882838219)
    ·
      refine ⟨29902896701781158824257329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19935264467854105882838219 29902896701781158824257329)
      ·
        refine ⟨22427172526335869118192997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29902896701781158824257329 22427172526335869118192997)
        ·
          refine ⟨4205094848687975459661187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22427172526335869118192997 4205094848687975459661187)
          ·
            refine ⟨6307642273031963189491781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205094848687975459661187 6307642273031963189491781)
            ·
              refine ⟨1182682926193493098029709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6307642273031963189491781 1182682926193493098029709)
              ·
                refine ⟨443506097322559911761141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1182682926193493098029709 443506097322559911761141)
                ·
                  refine ⟨41578696623989991727607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 443506097322559911761141 41578696623989991727607)
                  ·
                    rfl

theorem cell23_728768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 5].length) (baseStart_728768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728768 prefixEnd_728768 := by exact prefixLift 728768
  have htrace : WordTrace (prefixWord ++ tailWord_728768) baseStart_728768 baseEnd_728768 := by
    simpa [prefixWord, tailWord_728768, baseEnd_728768] using wordTrace_append hprefix tailTrace_728768
  have hstable : (prefixWord ++ tailWord_728768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728768).length < 2 ^ (prefixWord ++ tailWord_728768).sum := by decide
  have hdescent : baseEnd_728768 < baseStart_728768 := by decide
  rcases family_descends (prefixWord ++ tailWord_728768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728796 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_728796 : Nat := 118140960795 + 728796 * 2 ^ 59
def prefixEnd_728796 : Nat := 4983230072969 + 3 ^ 40 * 728796 * 2
def baseEnd_728796 : Nat := 374222647074235815998335

theorem tailTrace_728796 : CollatzResearch.WordTrace tailWord_728796 prefixEnd_728796 374222647074235815998335 := by
  unfold tailWord_728796
  simp only [CollatzResearch.WordTrace]
  refine ⟨13290686933852017646235121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17720915911802690194980161 13290686933852017646235121)
  ·
    refine ⟨9968015200389013234676341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13290686933852017646235121 9968015200389013234676341)
    ·
      refine ⟨934501425036469990750907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9968015200389013234676341 934501425036469990750907)
      ·
        refine ⟨1401752137554704986126361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934501425036469990750907 1401752137554704986126361)
        ·
          refine ⟨1051314103166028739594771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1401752137554704986126361 1051314103166028739594771)
          ·
            refine ⟨1576971154749043109392157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051314103166028739594771 1576971154749043109392157)
            ·
              refine ⟨591364183030891166022059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1576971154749043109392157 591364183030891166022059)
              ·
                refine ⟨887046274546336749033089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591364183030891166022059 887046274546336749033089)
                ·
                  refine ⟨665284705909752561774817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 887046274546336749033089 665284705909752561774817)
                  ·
                    refine ⟨498963529432314421331113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 665284705909752561774817 498963529432314421331113)
                    ·
                      refine ⟨374222647074235815998335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 498963529432314421331113 374222647074235815998335)
                      ·
                        rfl

theorem cell23_728796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_728796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728796 prefixEnd_728796 := by exact prefixLift 728796
  have htrace : WordTrace (prefixWord ++ tailWord_728796) baseStart_728796 baseEnd_728796 := by
    simpa [prefixWord, tailWord_728796, baseEnd_728796] using wordTrace_append hprefix tailTrace_728796
  have hstable : (prefixWord ++ tailWord_728796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728796).length < 2 ^ (prefixWord ++ tailWord_728796).sum := by decide
  have hdescent : baseEnd_728796 < baseStart_728796 := by decide
  rcases family_descends (prefixWord ++ tailWord_728796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728818 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_728818 : Nat := 118140960795 + 728818 * 2 ^ 59
def prefixEnd_728818 : Nat := 4983230072969 + 3 ^ 40 * 728818 * 2
def baseEnd_728818 : Nat := 374233943648634729923233

theorem tailTrace_728818 : CollatzResearch.WordTrace tailWord_728818 prefixEnd_728818 374233943648634729923233 := by
  unfold tailWord_728818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6645544068406083262442777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17721450849082888699847405 6645544068406083262442777)
  ·
    refine ⟨4984158051304562446832083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6645544068406083262442777 4984158051304562446832083)
    ·
      refine ⟨7476237076956843670248125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4984158051304562446832083 7476237076956843670248125)
      ·
        refine ⟨2803588903858816376343047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7476237076956843670248125 2803588903858816376343047)
        ·
          refine ⟨4205383355788224564514571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2803588903858816376343047 4205383355788224564514571)
          ·
            refine ⟨6308075033682336846771857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205383355788224564514571 6308075033682336846771857)
            ·
              refine ⟨4731056275261752635078893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6308075033682336846771857 4731056275261752635078893)
              ·
                refine ⟨1774146103223157238154585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4731056275261752635078893 1774146103223157238154585)
                ·
                  refine ⟨1330609577417367928615939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1774146103223157238154585 1330609577417367928615939)
                  ·
                    refine ⟨1995914366126051892923909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1330609577417367928615939 1995914366126051892923909)
                    ·
                      refine ⟨374233943648634729923233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1995914366126051892923909 374233943648634729923233)
                      ·
                        rfl

theorem cell23_728818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_728818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728818 prefixEnd_728818 := by exact prefixLift 728818
  have htrace : WordTrace (prefixWord ++ tailWord_728818) baseStart_728818 baseEnd_728818 := by
    simpa [prefixWord, tailWord_728818, baseEnd_728818] using wordTrace_append hprefix tailTrace_728818
  have hstable : (prefixWord ++ tailWord_728818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728818).length < 2 ^ (prefixWord ++ tailWord_728818).sum := by decide
  have hdescent : baseEnd_728818 < baseStart_728818 := by decide
  rcases family_descends (prefixWord ++ tailWord_728818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728841 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 6]
def baseStart_728841 : Nat := 118140960795 + 728841 * 2 ^ 59
def prefixEnd_728841 : Nat := 4983230072969 + 3 ^ 40 * 728841 * 2
def baseEnd_728841 : Nat := 41582861522632015548403

theorem tailTrace_728841 : CollatzResearch.WordTrace tailWord_728841 prefixEnd_728841 41582861522632015548403 := by
  unfold tailWord_728841
  simp only [CollatzResearch.WordTrace]
  refine ⟨26583015152541007977858377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17722010101694005318572251 26583015152541007977858377)
  ·
    refine ⟨19937261364405755983393783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26583015152541007977858377 19937261364405755983393783)
    ·
      refine ⟨29905892046608633975090675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19937261364405755983393783 29905892046608633975090675)
      ·
        refine ⟨44858838069912950962636013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29905892046608633975090675 44858838069912950962636013)
        ·
          refine ⟨16822064276217356610988505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44858838069912950962636013 16822064276217356610988505)
          ·
            refine ⟨12616548207163017458241379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16822064276217356610988505 12616548207163017458241379)
            ·
              refine ⟨18924822310744526187362069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12616548207163017458241379 18924822310744526187362069)
              ·
                refine ⟨887101045816149665032597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18924822310744526187362069 887101045816149665032597)
                ·
                  refine ⟨41582861522632015548403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 887101045816149665032597 41582861522632015548403)
                  ·
                    rfl

theorem cell23_728841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 6].length) (baseStart_728841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728841 prefixEnd_728841 := by exact prefixLift 728841
  have htrace : WordTrace (prefixWord ++ tailWord_728841) baseStart_728841 baseEnd_728841 := by
    simpa [prefixWord, tailWord_728841, baseEnd_728841] using wordTrace_append hprefix tailTrace_728841
  have hstable : (prefixWord ++ tailWord_728841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728841).length < 2 ^ (prefixWord ++ tailWord_728841).sum := by decide
  have hdescent : baseEnd_728841 < baseStart_728841 := by decide
  rcases family_descends (prefixWord ++ tailWord_728841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728851 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 3]
def baseStart_728851 : Nat := 118140960795 + 728851 * 2 ^ 59
def prefixEnd_728851 : Nat := 4983230072969 + 3 ^ 40 * 728851 * 2
def baseEnd_728851 : Nat := 374250888510233100810581

theorem tailTrace_728851 : CollatzResearch.WordTrace tailWord_728851 prefixEnd_728851 374250888510233100810581 := by
  unfold tailWord_728851
  simp only [CollatzResearch.WordTrace]
  refine ⟨26583379882504779685722407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17722253255003186457148271 26583379882504779685722407)
  ·
    refine ⟨39875069823757169528583611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26583379882504779685722407 39875069823757169528583611)
    ·
      refine ⟨59812604735635754292875417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39875069823757169528583611 59812604735635754292875417)
      ·
        refine ⟨44859453551726815719656563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59812604735635754292875417 44859453551726815719656563)
        ·
          refine ⟨67289180327590223579484845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44859453551726815719656563 67289180327590223579484845)
          ·
            refine ⟨25233442622846333842306817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67289180327590223579484845 25233442622846333842306817)
            ·
              refine ⟨18925081967134750381730113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25233442622846333842306817 18925081967134750381730113)
              ·
                refine ⟨14193811475351062786297585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18925081967134750381730113 14193811475351062786297585)
                ·
                  refine ⟨10645358606513297089723189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14193811475351062786297585 10645358606513297089723189)
                  ·
                    refine ⟨998002369360621602161549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10645358606513297089723189 998002369360621602161549)
                    ·
                      refine ⟨374250888510233100810581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 998002369360621602161549 374250888510233100810581)
                      ·
                        rfl

theorem cell23_728851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 3].length) (baseStart_728851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728851 prefixEnd_728851 := by exact prefixLift 728851
  have htrace : WordTrace (prefixWord ++ tailWord_728851) baseStart_728851 baseEnd_728851 := by
    simpa [prefixWord, tailWord_728851, baseEnd_728851] using wordTrace_append hprefix tailTrace_728851
  have hstable : (prefixWord ++ tailWord_728851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728851).length < 2 ^ (prefixWord ++ tailWord_728851).sum := by decide
  have hdescent : baseEnd_728851 < baseStart_728851 := by decide
  rcases family_descends (prefixWord ++ tailWord_728851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728858 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 6]
def baseStart_728858 : Nat := 118140960795 + 728858 * 2 ^ 59
def prefixEnd_728858 : Nat := 4983230072969 + 3 ^ 40 * 728858 * 2
def baseEnd_728858 : Nat := 41583831430534952602561

theorem tailTrace_728858 : CollatzResearch.WordTrace tailWord_728858 prefixEnd_728858 41583831430534952602561 := by
  unfold tailWord_728858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6645908798369854970306807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17722423462319613254151485 6645908798369854970306807)
  ·
    refine ⟨9968863197554782455460211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6645908798369854970306807 9968863197554782455460211)
    ·
      refine ⟨14953294796332173683190317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9968863197554782455460211 14953294796332173683190317)
      ·
        refine ⟨5607485548624565131196369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14953294796332173683190317 5607485548624565131196369)
        ·
          refine ⟨4205614161468423848397277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5607485548624565131196369 4205614161468423848397277)
          ·
            refine ⟨1577105310550658943148979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4205614161468423848397277 1577105310550658943148979)
            ·
              refine ⟨2365657965825988414723469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577105310550658943148979 2365657965825988414723469)
              ·
                refine ⟨887121737184745655521301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2365657965825988414723469 887121737184745655521301)
                ·
                  refine ⟨41583831430534952602561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 887121737184745655521301 41583831430534952602561)
                  ·
                    rfl

theorem cell23_728858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_728858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728858 prefixEnd_728858 := by exact prefixLift 728858
  have htrace : WordTrace (prefixWord ++ tailWord_728858) baseStart_728858 baseEnd_728858 := by
    simpa [prefixWord, tailWord_728858, baseEnd_728858] using wordTrace_append hprefix tailTrace_728858
  have hstable : (prefixWord ++ tailWord_728858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728858).length < 2 ^ (prefixWord ++ tailWord_728858).sum := by decide
  have hdescent : baseEnd_728858 < baseStart_728858 := by decide
  rcases family_descends (prefixWord ++ tailWord_728858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728901 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_728901 : Nat := 118140960795 + 728901 * 2 ^ 59
def prefixEnd_728901 : Nat := 4983230072969 + 3 ^ 40 * 728901 * 2
def baseEnd_728901 : Nat := 124758854180985968395117

theorem tailTrace_728901 : CollatzResearch.WordTrace tailWord_728901 prefixEnd_728901 124758854180985968395117 := by
  unfold tailWord_728901
  simp only [CollatzResearch.WordTrace]
  refine ⟨26585203532323638225042557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17723469021549092150028371 26585203532323638225042557)
  ·
    refine ⟨9969451324621364334390959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26585203532323638225042557 9969451324621364334390959)
    ·
      refine ⟨14954176986932046501586439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9969451324621364334390959 14954176986932046501586439)
      ·
        refine ⟨22431265480398069752379659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14954176986932046501586439 22431265480398069752379659)
        ·
          refine ⟨33646898220597104628569489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22431265480398069752379659 33646898220597104628569489)
          ·
            refine ⟨25235173665447828471427117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33646898220597104628569489 25235173665447828471427117)
            ·
              refine ⟨9463190124542935676785169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25235173665447828471427117 9463190124542935676785169)
              ·
                refine ⟨7097392593407201757588877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9463190124542935676785169 7097392593407201757588877)
                ·
                  refine ⟨2661522222527700659095829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7097392593407201757588877 2661522222527700659095829)
                  ·
                    refine ⟨124758854180985968395117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2661522222527700659095829 124758854180985968395117)
                    ·
                      rfl

theorem cell23_728901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_728901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728901 prefixEnd_728901 := by exact prefixLift 728901
  have htrace : WordTrace (prefixWord ++ tailWord_728901) baseStart_728901 baseEnd_728901 := by
    simpa [prefixWord, tailWord_728901, baseEnd_728901] using wordTrace_append hprefix tailTrace_728901
  have hstable : (prefixWord ++ tailWord_728901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728901).length < 2 ^ (prefixWord ++ tailWord_728901).sum := by decide
  have hdescent : baseEnd_728901 < baseStart_728901 := by decide
  rcases family_descends (prefixWord ++ tailWord_728901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728942 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_728942 : Nat := 118140960795 + 728942 * 2 ^ 59
def prefixEnd_728942 : Nat := 4983230072969 + 3 ^ 40 * 728942 * 2
def baseEnd_728942 : Nat := 374297615249792244772663

theorem tailTrace_728942 : CollatzResearch.WordTrace tailWord_728942 prefixEnd_728942 374297615249792244772663 := by
  unfold tailWord_728942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323337365646887778410635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17724465950116734818190053 3323337365646887778410635)
  ·
    refine ⟨4985006048470331667615953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3323337365646887778410635 4985006048470331667615953)
    ·
      refine ⟨3738754536352748750711965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4985006048470331667615953 3738754536352748750711965)
      ·
        refine ⟨1402032951132280781516987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3738754536352748750711965 1402032951132280781516987)
        ·
          refine ⟨2103049426698421172275481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402032951132280781516987 2103049426698421172275481)
          ·
            refine ⟨1577287070023815879206611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2103049426698421172275481 1577287070023815879206611)
            ·
              refine ⟨2365930605035723818809917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577287070023815879206611 2365930605035723818809917)
              ·
                refine ⟨887223976888396432053719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2365930605035723818809917 887223976888396432053719)
                ·
                  refine ⟨1330835965332594648080579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887223976888396432053719 1330835965332594648080579)
                  ·
                    refine ⟨1996253947998891972120869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1330835965332594648080579 1996253947998891972120869)
                    ·
                      refine ⟨374297615249792244772663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1996253947998891972120869 374297615249792244772663)
                      ·
                        rfl

theorem cell23_728942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_728942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728942 prefixEnd_728942 := by exact prefixLift 728942
  have htrace : WordTrace (prefixWord ++ tailWord_728942) baseStart_728942 baseEnd_728942 := by
    simpa [prefixWord, tailWord_728942, baseEnd_728942] using wordTrace_append hprefix tailTrace_728942
  have hstable : (prefixWord ++ tailWord_728942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728942).length < 2 ^ (prefixWord ++ tailWord_728942).sum := by decide
  have hdescent : baseEnd_728942 < baseStart_728942 := by decide
  rcases family_descends (prefixWord ++ tailWord_728942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728945 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 1, 2, 3]
def baseStart_728945 : Nat := 118140960795 + 728945 * 2 ^ 59
def prefixEnd_728945 : Nat := 4983230072969 + 3 ^ 40 * 728945 * 2
def baseEnd_728945 : Nat := 374299155691755733035149

theorem tailTrace_728945 : CollatzResearch.WordTrace tailWord_728945 prefixEnd_728945 374299155691755733035149 := by
  unfold tailWord_728945
  simp only [CollatzResearch.WordTrace]
  refine ⟨26586808344164233739644289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17724538896109489159762859 26586808344164233739644289)
  ·
    refine ⟨19940106258123175304733217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26586808344164233739644289 19940106258123175304733217)
    ·
      refine ⟨14955079693592381478549913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19940106258123175304733217 14955079693592381478549913)
      ·
        refine ⟨11216309770194286108912435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14955079693592381478549913 11216309770194286108912435)
        ·
          refine ⟨16824464655291429163368653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11216309770194286108912435 16824464655291429163368653)
          ·
            refine ⟨6309174245734285936263245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16824464655291429163368653 6309174245734285936263245)
            ·
              refine ⟨2365940342150357226098717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6309174245734285936263245 2365940342150357226098717)
              ·
                refine ⟨887227628306383959787019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2365940342150357226098717 887227628306383959787019)
                ·
                  refine ⟨1330841442459575939680529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887227628306383959787019 1330841442459575939680529)
                  ·
                    refine ⟨998131081844681954760397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1330841442459575939680529 998131081844681954760397)
                    ·
                      refine ⟨374299155691755733035149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 998131081844681954760397 374299155691755733035149)
                      ·
                        rfl

theorem cell23_728945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_728945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728945 prefixEnd_728945 := by exact prefixLift 728945
  have htrace : WordTrace (prefixWord ++ tailWord_728945) baseStart_728945 baseEnd_728945 := by
    simpa [prefixWord, tailWord_728945, baseEnd_728945] using wordTrace_append hprefix tailTrace_728945
  have hstable : (prefixWord ++ tailWord_728945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728945).length < 2 ^ (prefixWord ++ tailWord_728945).sum := by decide
  have hdescent : baseEnd_728945 < baseStart_728945 := by decide
  rcases family_descends (prefixWord ++ tailWord_728945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728951 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_728951 : Nat := 118140960795 + 728951 * 2 ^ 59
def prefixEnd_728951 : Nat := 4983230072969 + 3 ^ 40 * 728951 * 2
def baseEnd_728951 : Nat := 374302236575682709560121

theorem tailTrace_728951 : CollatzResearch.WordTrace tailWord_728951 prefixEnd_728951 374302236575682709560121 := by
  unfold tailWord_728951
  simp only [CollatzResearch.WordTrace]
  refine ⟨26587027182142496764362707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17724684788094997842908471 26587027182142496764362707)
  ·
    refine ⟨39880540773213745146544061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26587027182142496764362707 39880540773213745146544061)
    ·
      refine ⟨14955202789955154429954023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39880540773213745146544061 14955202789955154429954023)
      ·
        refine ⟨22432804184932731644931035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14955202789955154429954023 22432804184932731644931035)
        ·
          refine ⟨33649206277399097467396553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22432804184932731644931035 33649206277399097467396553)
          ·
            refine ⟨25236904708049323100547415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33649206277399097467396553 25236904708049323100547415)
            ·
              refine ⟨37855357062073984650821123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25236904708049323100547415 37855357062073984650821123)
              ·
                refine ⟨56783035593110976976231685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37855357062073984650821123 56783035593110976976231685)
                ·
                  refine ⟨10646819173708308183043441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56783035593110976976231685 10646819173708308183043441)
                  ·
                    refine ⟨7985114380281231137282581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10646819173708308183043441 7985114380281231137282581)
                    ·
                      refine ⟨374302236575682709560121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7985114380281231137282581 374302236575682709560121)
                      ·
                        rfl

theorem cell23_728951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_728951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728951 prefixEnd_728951 := by exact prefixLift 728951
  have htrace : WordTrace (prefixWord ++ tailWord_728951) baseStart_728951 baseEnd_728951 := by
    simpa [prefixWord, tailWord_728951, baseEnd_728951] using wordTrace_append hprefix tailTrace_728951
  have hstable : (prefixWord ++ tailWord_728951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728951).length < 2 ^ (prefixWord ++ tailWord_728951).sum := by decide
  have hdescent : baseEnd_728951 < baseStart_728951 := by decide
  rcases family_descends (prefixWord ++ tailWord_728951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728985 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 3, 3, 2]
def baseStart_728985 : Nat := 118140960795 + 728985 * 2 ^ 59
def prefixEnd_728985 : Nat := 4983230072969 + 3 ^ 40 * 728985 * 2
def baseEnd_728985 : Nat := 374319694917935576534965

theorem tailTrace_728985 : CollatzResearch.WordTrace tailWord_728985 prefixEnd_728985 374319694917935576534965 := by
  unfold tailWord_728985
  simp only [CollatzResearch.WordTrace]
  refine ⟨26588267264019320571100409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17725511509346213714066939 26588267264019320571100409)
  ·
    refine ⟨19941200448014490428325307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26588267264019320571100409 19941200448014490428325307)
    ·
      refine ⟨29911800672021735642487961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19941200448014490428325307 29911800672021735642487961)
      ·
        refine ⟨22433850504016301731865971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29911800672021735642487961 22433850504016301731865971)
        ·
          refine ⟨33650775756024452597798957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22433850504016301731865971 33650775756024452597798957)
          ·
            refine ⟨12619040908509169724174609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33650775756024452597798957 12619040908509169724174609)
            ·
              refine ⟨9464280681381877293130957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12619040908509169724174609 9464280681381877293130957)
              ·
                refine ⟨3549105255518203984924109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9464280681381877293130957 3549105255518203984924109)
                ·
                  refine ⟨1330914470819326494346541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3549105255518203984924109 1330914470819326494346541)
                  ·
                    refine ⟨499092926557247435379953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1330914470819326494346541 499092926557247435379953)
                    ·
                      refine ⟨374319694917935576534965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 499092926557247435379953 374319694917935576534965)
                      ·
                        rfl

theorem cell23_728985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 3, 2].length) (baseStart_728985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728985 prefixEnd_728985 := by exact prefixLift 728985
  have htrace : WordTrace (prefixWord ++ tailWord_728985) baseStart_728985 baseEnd_728985 := by
    simpa [prefixWord, tailWord_728985, baseEnd_728985] using wordTrace_append hprefix tailTrace_728985
  have hstable : (prefixWord ++ tailWord_728985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728985).length < 2 ^ (prefixWord ++ tailWord_728985).sum := by decide
  have hdescent : baseEnd_728985 < baseStart_728985 := by decide
  rcases family_descends (prefixWord ++ tailWord_728985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728993 : List Nat := [1, 2, 3, 4, 2, 2, 1, 3, 1, 2, 2]
def baseStart_728993 : Nat := 118140960795 + 728993 * 2 ^ 59
def prefixEnd_728993 : Nat := 4983230072969 + 3 ^ 40 * 728993 * 2
def baseEnd_728993 : Nat := 374323802763171545234929

theorem tailTrace_728993 : CollatzResearch.WordTrace tailWord_728993 prefixEnd_728993 374323802763171545234929 := by
  unfold tailWord_728993
  simp only [CollatzResearch.WordTrace]
  refine ⟨26588559047990337937391633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17725706031993558624927755 26588559047990337937391633)
  ·
    refine ⟨19941419285992753453043725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26588559047990337937391633 19941419285992753453043725)
    ·
      refine ⟨7478032232247282544891397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19941419285992753453043725 7478032232247282544891397)
      ·
        refine ⟨1402131043546365477167137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7478032232247282544891397 1402131043546365477167137)
        ·
          refine ⟨1051598282659774107875353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1402131043546365477167137 1051598282659774107875353)
          ·
            refine ⟨788698711994830580906515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051598282659774107875353 788698711994830580906515)
            ·
              refine ⟨1183048067992245871359773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788698711994830580906515 1183048067992245871359773)
              ·
                refine ⟨443643025497092201759915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1183048067992245871359773 443643025497092201759915)
                ·
                  refine ⟨665464538245638302639873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443643025497092201759915 665464538245638302639873)
                  ·
                    refine ⟨499098403684228726979905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 665464538245638302639873 499098403684228726979905)
                    ·
                      refine ⟨374323802763171545234929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 499098403684228726979905 374323802763171545234929)
                      ·
                        rfl

theorem cell23_728993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_728993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_728993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_728993 prefixEnd_728993 := by exact prefixLift 728993
  have htrace : WordTrace (prefixWord ++ tailWord_728993) baseStart_728993 baseEnd_728993 := by
    simpa [prefixWord, tailWord_728993, baseEnd_728993] using wordTrace_append hprefix tailTrace_728993
  have hstable : (prefixWord ++ tailWord_728993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728993).length < 2 ^ (prefixWord ++ tailWord_728993).sum := by decide
  have hdescent : baseEnd_728993 < baseStart_728993 := by decide
  rcases family_descends (prefixWord ++ tailWord_728993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729038 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_729038 : Nat := 118140960795 + 729038 * 2 ^ 59
def prefixEnd_729038 : Nat := 4983230072969 + 3 ^ 40 * 729038 * 2
def baseEnd_729038 : Nat := 41594101043624874352469

theorem tailTrace_729038 : CollatzResearch.WordTrace tailWord_729038 prefixEnd_729038 41594101043624874352469 := by
  unfold tailWord_729038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323775041603413827847471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17726800221884873748519845 3323775041603413827847471)
  ·
    refine ⟨4985662562405120741771207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3323775041603413827847471 4985662562405120741771207)
    ·
      refine ⟨7478493843607681112656811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4985662562405120741771207 7478493843607681112656811)
      ·
        refine ⟨11217740765411521668985217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7478493843607681112656811 11217740765411521668985217)
        ·
          refine ⟨8413305574058641251738913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11217740765411521668985217 8413305574058641251738913)
          ·
            refine ⟨6309979180543980938804185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8413305574058641251738913 6309979180543980938804185)
            ·
              refine ⟨4732484385407985704103139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6309979180543980938804185 4732484385407985704103139)
              ·
                refine ⟨7098726578111978556154709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732484385407985704103139 7098726578111978556154709)
                ·
                  refine ⟨41594101043624874352469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7098726578111978556154709 41594101043624874352469)
                  ·
                    rfl

theorem cell23_729038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_729038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729038 prefixEnd_729038 := by exact prefixLift 729038
  have htrace : WordTrace (prefixWord ++ tailWord_729038) baseStart_729038 baseEnd_729038 := by
    simpa [prefixWord, tailWord_729038, baseEnd_729038] using wordTrace_append hprefix tailTrace_729038
  have hstable : (prefixWord ++ tailWord_729038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729038).length < 2 ^ (prefixWord ++ tailWord_729038).sum := by decide
  have hdescent : baseEnd_729038 < baseStart_729038 := by decide
  rcases family_descends (prefixWord ++ tailWord_729038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729072 : List Nat := [2, 1, 1, 1, 3, 2, 6, 2, 5]
def baseStart_729072 : Nat := 118140960795 + 729072 * 2 ^ 59
def prefixEnd_729072 : Nat := 4983230072969 + 3 ^ 40 * 729072 * 2
def baseEnd_729072 : Nat := 41596040859430748460785

theorem tailTrace_729072 : CollatzResearch.WordTrace tailWord_729072 prefixEnd_729072 41596040859430748460785 := by
  unfold tailWord_729072
  simp only [CollatzResearch.WordTrace]
  refine ⟨13295720207352067214758735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17727626943136089619678313 13295720207352067214758735)
  ·
    refine ⟨19943580311028100822138103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13295720207352067214758735 19943580311028100822138103)
    ·
      refine ⟨29915370466542151233207155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19943580311028100822138103 29915370466542151233207155)
      ·
        refine ⟨44873055699813226849810733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29915370466542151233207155 44873055699813226849810733)
        ·
          refine ⟨16827395887429960068679025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44873055699813226849810733 16827395887429960068679025)
          ·
            refine ⟨12620546915572470051509269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16827395887429960068679025 12620546915572470051509269)
            ·
              refine ⟨591588136667459533664497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12620546915572470051509269 591588136667459533664497)
              ·
                refine ⟨443691102500594650248373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591588136667459533664497 443691102500594650248373)
                ·
                  refine ⟨41596040859430748460785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 443691102500594650248373 41596040859430748460785)
                  ·
                    rfl

theorem cell23_729072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 5].length) (baseStart_729072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729072 prefixEnd_729072 := by exact prefixLift 729072
  have htrace : WordTrace (prefixWord ++ tailWord_729072) baseStart_729072 baseEnd_729072 := by
    simpa [prefixWord, tailWord_729072, baseEnd_729072] using wordTrace_append hprefix tailTrace_729072
  have hstable : (prefixWord ++ tailWord_729072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729072).length < 2 ^ (prefixWord ++ tailWord_729072).sum := by decide
  have hdescent : baseEnd_729072 < baseStart_729072 := by decide
  rcases family_descends (prefixWord ++ tailWord_729072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729122 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_729122 : Nat := 118140960795 + 729122 * 2 ^ 59
def prefixEnd_729122 : Nat := 4983230072969 + 3 ^ 40 * 729122 * 2
def baseEnd_729122 : Nat := 374390041767601540521835

theorem tailTrace_729122 : CollatzResearch.WordTrace tailWord_729122 prefixEnd_729122 374390041767601540521835 := by
  unfold tailWord_729122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6648316016130748242209405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17728842709681995312558413 6648316016130748242209405)
  ·
    refine ⟨2493118506049030590828527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6648316016130748242209405 2493118506049030590828527)
    ·
      refine ⟨3739677759073545886242791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493118506049030590828527 3739677759073545886242791)
      ·
        refine ⟨5609516638610318829364187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3739677759073545886242791 5609516638610318829364187)
        ·
          refine ⟨8414274957915478244046281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5609516638610318829364187 8414274957915478244046281)
          ·
            refine ⟨6310706218436608683034711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8414274957915478244046281 6310706218436608683034711)
            ·
              refine ⟨9466059327654913024552067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310706218436608683034711 9466059327654913024552067)
              ·
                refine ⟨14199088991482369536828101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9466059327654913024552067 14199088991482369536828101)
                ·
                  refine ⟨2662329185902944288155269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14199088991482369536828101 2662329185902944288155269)
                  ·
                    refine ⟨499186722356802054029113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2662329185902944288155269 499186722356802054029113)
                    ·
                      refine ⟨374390041767601540521835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 499186722356802054029113 374390041767601540521835)
                      ·
                        rfl

theorem cell23_729122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_729122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729122 prefixEnd_729122 := by exact prefixLift 729122
  have htrace : WordTrace (prefixWord ++ tailWord_729122) baseStart_729122 baseEnd_729122 := by
    simpa [prefixWord, tailWord_729122, baseEnd_729122] using wordTrace_append hprefix tailTrace_729122
  have hstable : (prefixWord ++ tailWord_729122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729122).length < 2 ^ (prefixWord ++ tailWord_729122).sum := by decide
  have hdescent : baseEnd_729122 < baseStart_729122 := by decide
  rcases family_descends (prefixWord ++ tailWord_729122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729142 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_729142 : Nat := 118140960795 + 729142 * 2 ^ 59
def prefixEnd_729142 : Nat := 4983230072969 + 3 ^ 40 * 729142 * 2
def baseEnd_729142 : Nat := 374400311380691462271743

theorem tailTrace_729142 : CollatzResearch.WordTrace tailWord_729142 prefixEnd_729142 374400311380691462271743 := by
  unfold tailWord_729142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662124595278158524035355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17729329016300357589710453 1662124595278158524035355)
  ·
    refine ⟨2493186892917237786053033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1662124595278158524035355 2493186892917237786053033)
    ·
      refine ⟨1869890169687928339539775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2493186892917237786053033 1869890169687928339539775)
      ·
        refine ⟨2804835254531892509309663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1869890169687928339539775 2804835254531892509309663)
        ·
          refine ⟨4207252881797838763964495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2804835254531892509309663 4207252881797838763964495)
          ·
            refine ⟨6310879322696758145946743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4207252881797838763964495 6310879322696758145946743)
            ·
              refine ⟨9466318984045137218920115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310879322696758145946743 9466318984045137218920115)
              ·
                refine ⟨14199478476067705828380173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9466318984045137218920115 14199478476067705828380173)
                ·
                  refine ⟨5324804428525389685642565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14199478476067705828380173 5324804428525389685642565)
                  ·
                    refine ⟨998400830348510566057981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5324804428525389685642565 998400830348510566057981)
                    ·
                      refine ⟨374400311380691462271743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 998400830348510566057981 374400311380691462271743)
                      ·
                        rfl

theorem cell23_729142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_729142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729142 prefixEnd_729142 := by exact prefixLift 729142
  have htrace : WordTrace (prefixWord ++ tailWord_729142) baseStart_729142 baseEnd_729142 := by
    simpa [prefixWord, tailWord_729142, baseEnd_729142] using wordTrace_append hprefix tailTrace_729142
  have hstable : (prefixWord ++ tailWord_729142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729142).length < 2 ^ (prefixWord ++ tailWord_729142).sum := by decide
  have hdescent : baseEnd_729142 < baseStart_729142 := by decide
  rcases family_descends (prefixWord ++ tailWord_729142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729166 : List Nat := [4, 1, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_729166 : Nat := 118140960795 + 729166 * 2 ^ 59
def prefixEnd_729166 : Nat := 4983230072969 + 3 ^ 40 * 729166 * 2
def baseEnd_729166 : Nat := 124804211638799789457211

theorem tailTrace_729166 : CollatzResearch.WordTrace tailWord_729166 prefixEnd_729166 124804211638799789457211 := by
  unfold tailWord_729166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3324358609545448560429919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17729912584242392322292901 3324358609545448560429919)
  ·
    refine ⟨4986537914318172840644879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3324358609545448560429919 4986537914318172840644879)
    ·
      refine ⟨7479806871477259260967319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4986537914318172840644879 7479806871477259260967319)
      ·
        refine ⟨11219710307215888891450979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7479806871477259260967319 11219710307215888891450979)
        ·
          refine ⟨16829565460823833337176469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11219710307215888891450979 16829565460823833337176469)
          ·
            refine ⟨788885880976117187680147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16829565460823833337176469 788885880976117187680147)
            ·
              refine ⟨1183328821464175781520221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788885880976117187680147 1183328821464175781520221)
              ·
                refine ⟨443748308049065918070083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1183328821464175781520221 443748308049065918070083)
                ·
                  refine ⟨665622462073598877105125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443748308049065918070083 665622462073598877105125)
                  ·
                    refine ⟨124804211638799789457211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 665622462073598877105125 124804211638799789457211)
                    ·
                      rfl

theorem cell23_729166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_729166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729166 prefixEnd_729166 := by exact prefixLift 729166
  have htrace : WordTrace (prefixWord ++ tailWord_729166) baseStart_729166 baseEnd_729166 := by
    simpa [prefixWord, tailWord_729166, baseEnd_729166] using wordTrace_append hprefix tailTrace_729166
  have hstable : (prefixWord ++ tailWord_729166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729166).length < 2 ^ (prefixWord ++ tailWord_729166).sum := by decide
  have hdescent : baseEnd_729166 < baseStart_729166 := by decide
  rcases family_descends (prefixWord ++ tailWord_729166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729189 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 3, 1, 3]
def baseStart_729189 : Nat := 118140960795 + 729189 * 2 ^ 59
def prefixEnd_729189 : Nat := 4983230072969 + 3 ^ 40 * 729189 * 2
def baseEnd_729189 : Nat := 374424444971452778384027

theorem tailTrace_729189 : CollatzResearch.WordTrace tailWord_729189 prefixEnd_729189 374424444971452778384027 := by
  unfold tailWord_729189
  simp only [CollatzResearch.WordTrace]
  refine ⟨26595707755280263411526621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17730471836853508941017747 26595707755280263411526621)
  ·
    refine ⟨9973390408230098779322483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26595707755280263411526621 9973390408230098779322483)
    ·
      refine ⟨14960085612345148168983725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9973390408230098779322483 14960085612345148168983725)
      ·
        refine ⟨5610032104629430563368897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14960085612345148168983725 5610032104629430563368897)
        ·
          refine ⟨4207524078472072922526673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5610032104629430563368897 4207524078472072922526673)
          ·
            refine ⟨3155643058854054691895005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4207524078472072922526673 3155643058854054691895005)
            ·
              refine ⟨1183366147070270509460627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3155643058854054691895005 1183366147070270509460627)
              ·
                refine ⟨1775049220605405764190941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183366147070270509460627 1775049220605405764190941)
                ·
                  refine ⟨665643457727027161571603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1775049220605405764190941 665643457727027161571603)
                  ·
                    refine ⟨998465186590540742357405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 665643457727027161571603 998465186590540742357405)
                    ·
                      refine ⟨374424444971452778384027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 998465186590540742357405 374424444971452778384027)
                      ·
                        rfl

theorem cell23_729189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_729189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729189 prefixEnd_729189 := by exact prefixLift 729189
  have htrace : WordTrace (prefixWord ++ tailWord_729189) baseStart_729189 baseEnd_729189 := by
    simpa [prefixWord, tailWord_729189, baseEnd_729189] using wordTrace_append hprefix tailTrace_729189
  have hstable : (prefixWord ++ tailWord_729189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729189).length < 2 ^ (prefixWord ++ tailWord_729189).sum := by decide
  have hdescent : baseEnd_729189 < baseStart_729189 := by decide
  rcases family_descends (prefixWord ++ tailWord_729189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729209 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 1, 5]
def baseStart_729209 : Nat := 118140960795 + 729209 * 2 ^ 59
def prefixEnd_729209 : Nat := 4983230072969 + 3 ^ 40 * 729209 * 2
def baseEnd_729209 : Nat := 124811571528180900044645

theorem tailTrace_729209 : CollatzResearch.WordTrace tailWord_729209 prefixEnd_729209 124811571528180900044645 := by
  unfold tailWord_729209
  simp only [CollatzResearch.WordTrace]
  refine ⟨26596437215207806827254681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17730958143471871218169787 26596437215207806827254681)
  ·
    refine ⟨19947327911405855120441011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26596437215207806827254681 19947327911405855120441011)
    ·
      refine ⟨29920991867108782680661517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19947327911405855120441011 29920991867108782680661517)
      ·
        refine ⟨11220371950165793505248069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29920991867108782680661517 11220371950165793505248069)
        ·
          refine ⟨2103819740656086282234013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11220371950165793505248069 2103819740656086282234013)
          ·
            refine ⟨788932402746032355837755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2103819740656086282234013 788932402746032355837755)
            ·
              refine ⟨1183398604119048533756633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788932402746032355837755 1183398604119048533756633)
              ·
                refine ⟨887548953089286400317475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1183398604119048533756633 887548953089286400317475)
                ·
                  refine ⟨1331323429633929600476213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887548953089286400317475 1331323429633929600476213)
                  ·
                    refine ⟨124811571528180900044645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1331323429633929600476213 124811571528180900044645)
                    ·
                      rfl

theorem cell23_729209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 5].length) (baseStart_729209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729209 prefixEnd_729209 := by exact prefixLift 729209
  have htrace : WordTrace (prefixWord ++ tailWord_729209) baseStart_729209 baseEnd_729209 := by
    simpa [prefixWord, tailWord_729209, baseEnd_729209] using wordTrace_append hprefix tailTrace_729209
  have hstable : (prefixWord ++ tailWord_729209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729209).length < 2 ^ (prefixWord ++ tailWord_729209).sum := by decide
  have hdescent : baseEnd_729209 < baseStart_729209 := by decide
  rcases family_descends (prefixWord ++ tailWord_729209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729212 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_729212 : Nat := 118140960795 + 729212 * 2 ^ 59
def prefixEnd_729212 : Nat := 4983230072969 + 3 ^ 40 * 729212 * 2
def baseEnd_729212 : Nat := 374436255026506188396421

theorem tailTrace_729212 : CollatzResearch.WordTrace tailWord_729212 prefixEnd_729212 374436255026506188396421 := by
  unfold tailWord_729212
  simp only [CollatzResearch.WordTrace]
  refine ⟨13298273317098469169806945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17731031089464625559742593 13298273317098469169806945)
  ·
    refine ⟨9973704987823851877355209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13298273317098469169806945 9973704987823851877355209)
    ·
      refine ⟨7480278740867888908016407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9973704987823851877355209 7480278740867888908016407)
      ·
        refine ⟨11220418111301833362024611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7480278740867888908016407 11220418111301833362024611)
        ·
          refine ⟨16830627166952750043036917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11220418111301833362024611 16830627166952750043036917)
          ·
            refine ⟨1577871296901820316534711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16830627166952750043036917 1577871296901820316534711)
            ·
              refine ⟨2366806945352730474802067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577871296901820316534711 2366806945352730474802067)
              ·
                refine ⟨3550210418029095712203101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366806945352730474802067 3550210418029095712203101)
                ·
                  refine ⟨1331328906760910892076163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3550210418029095712203101 1331328906760910892076163)
                  ·
                    refine ⟨1996993360141366338114245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1331328906760910892076163 1996993360141366338114245)
                    ·
                      refine ⟨374436255026506188396421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1996993360141366338114245 374436255026506188396421)
                      ·
                        rfl

theorem cell23_729212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_729212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729212 prefixEnd_729212 := by exact prefixLift 729212
  have htrace : WordTrace (prefixWord ++ tailWord_729212) baseStart_729212 baseEnd_729212 := by
    simpa [prefixWord, tailWord_729212, baseEnd_729212] using wordTrace_append hprefix tailTrace_729212
  have hstable : (prefixWord ++ tailWord_729212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729212).length < 2 ^ (prefixWord ++ tailWord_729212).sum := by decide
  have hdescent : baseEnd_729212 < baseStart_729212 := by decide
  rcases family_descends (prefixWord ++ tailWord_729212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729240 : List Nat := [2, 1, 2, 4, 3, 2, 2, 2, 1, 1, 3]
def baseStart_729240 : Nat := 118140960795 + 729240 * 2 ^ 59
def prefixEnd_729240 : Nat := 4983230072969 + 3 ^ 40 * 729240 * 2
def baseEnd_729240 : Nat := 374450632484832078846293

theorem tailTrace_729240 : CollatzResearch.WordTrace tailWord_729240 prefixEnd_729240 374450632484832078846293 := by
  unfold tailWord_729240
  simp only [CollatzResearch.WordTrace]
  refine ⟨13298783939047749560816587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17731711918730332747755449 13298783939047749560816587)
  ·
    refine ⟨19948175908571624341224881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13298783939047749560816587 19948175908571624341224881)
    ·
      refine ⟨14961131931428718255918661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19948175908571624341224881 14961131931428718255918661)
      ·
        refine ⟨2805212237142884672984749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14961131931428718255918661 2805212237142884672984749)
        ·
          refine ⟨1051954588928581752369281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2805212237142884672984749 1051954588928581752369281)
          ·
            refine ⟨788965941696436314276961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051954588928581752369281 788965941696436314276961)
            ·
              refine ⟨591724456272327235707721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788965941696436314276961 591724456272327235707721)
              ·
                refine ⟨443793342204245426780791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591724456272327235707721 443793342204245426780791)
                ·
                  refine ⟨665690013306368140171187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443793342204245426780791 665690013306368140171187)
                  ·
                    refine ⟨998535019959552210256781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 665690013306368140171187 998535019959552210256781)
                    ·
                      refine ⟨374450632484832078846293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 998535019959552210256781 374450632484832078846293)
                      ·
                        rfl

theorem cell23_729240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_729240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729240 prefixEnd_729240 := by exact prefixLift 729240
  have htrace : WordTrace (prefixWord ++ tailWord_729240) baseStart_729240 baseEnd_729240 := by
    simpa [prefixWord, tailWord_729240, baseEnd_729240] using wordTrace_append hprefix tailTrace_729240
  have hstable : (prefixWord ++ tailWord_729240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729240).length < 2 ^ (prefixWord ++ tailWord_729240).sum := by decide
  have hdescent : baseEnd_729240 < baseStart_729240 := by decide
  rcases family_descends (prefixWord ++ tailWord_729240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729275 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 5]
def baseStart_729275 : Nat := 118140960795 + 729275 * 2 ^ 59
def prefixEnd_729275 : Nat := 4983230072969 + 3 ^ 40 * 729275 * 2
def baseEnd_729275 : Nat := 374468604307739441908631

theorem tailTrace_729275 : CollatzResearch.WordTrace tailWord_729275 prefixEnd_729275 374468604307739441908631 := by
  unfold tailWord_729275
  simp only [CollatzResearch.WordTrace]
  refine ⟨26598844432968700099157279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17732562955312466732771519 26598844432968700099157279)
  ·
    refine ⟨39898266649453050148735919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26598844432968700099157279 39898266649453050148735919)
    ·
      refine ⟨59847399974179575223103879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39898266649453050148735919 59847399974179575223103879)
      ·
        refine ⟨89771099961269362834655819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59847399974179575223103879 89771099961269362834655819)
        ·
          refine ⟨134656649941904044251983729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89771099961269362834655819 134656649941904044251983729)
          ·
            refine ⟨100992487456428033188987797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134656649941904044251983729 100992487456428033188987797)
            ·
              refine ⟨4734022849520064055733803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100992487456428033188987797 4734022849520064055733803)
              ·
                refine ⟨7101034274280096083600705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4734022849520064055733803 7101034274280096083600705)
                ·
                  refine ⟨5325775705710072062700529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7101034274280096083600705 5325775705710072062700529)
                  ·
                    refine ⟨3994331779282554047025397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5325775705710072062700529 3994331779282554047025397)
                    ·
                      refine ⟨374468604307739441908631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3994331779282554047025397 374468604307739441908631)
                      ·
                        rfl

theorem cell23_729275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_729275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729275 prefixEnd_729275 := by exact prefixLift 729275
  have htrace : WordTrace (prefixWord ++ tailWord_729275) baseStart_729275 baseEnd_729275 := by
    simpa [prefixWord, tailWord_729275, baseEnd_729275] using wordTrace_append hprefix tailTrace_729275
  have hstable : (prefixWord ++ tailWord_729275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729275).length < 2 ^ (prefixWord ++ tailWord_729275).sum := by decide
  have hdescent : baseEnd_729275 < baseStart_729275 := by decide
  rcases family_descends (prefixWord ++ tailWord_729275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729295 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 4, 6]
def baseStart_729295 : Nat := 118140960795 + 729295 * 2 ^ 59
def prefixEnd_729295 : Nat := 4983230072969 + 3 ^ 40 * 729295 * 2
def baseEnd_729295 : Nat := 124826291306943121219513

theorem tailTrace_729295 : CollatzResearch.WordTrace tailWord_729295 prefixEnd_729295 124826291306943121219513 := by
  unfold tailWord_729295
  simp only [CollatzResearch.WordTrace]
  refine ⟨26599573892896243514885339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17733049261930829009923559 26599573892896243514885339)
  ·
    refine ⟨39899360839344365272328009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26599573892896243514885339 39899360839344365272328009)
    ·
      refine ⟨29924520629508273954246007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39899360839344365272328009 29924520629508273954246007)
      ·
        refine ⟨44886780944262410931369011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29924520629508273954246007 44886780944262410931369011)
        ·
          refine ⟨67330171416393616397053517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44886780944262410931369011 67330171416393616397053517)
          ·
            refine ⟨25248814281147606148895069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67330171416393616397053517 25248814281147606148895069)
            ·
              refine ⟨9468305355430352305835651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25248814281147606148895069 9468305355430352305835651)
              ·
                refine ⟨14202458033145528458753477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9468305355430352305835651 14202458033145528458753477)
                ·
                  refine ⟨2662960881214786586016277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14202458033145528458753477 2662960881214786586016277)
                  ·
                    refine ⟨124826291306943121219513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2662960881214786586016277 124826291306943121219513)
                    ·
                      rfl

theorem cell23_729295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_729295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729295 prefixEnd_729295 := by exact prefixLift 729295
  have htrace : WordTrace (prefixWord ++ tailWord_729295) baseStart_729295 baseEnd_729295 := by
    simpa [prefixWord, tailWord_729295, baseEnd_729295] using wordTrace_append hprefix tailTrace_729295
  have hstable : (prefixWord ++ tailWord_729295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729295).length < 2 ^ (prefixWord ++ tailWord_729295).sum := by decide
  have hdescent : baseEnd_729295 < baseStart_729295 := by decide
  rcases family_descends (prefixWord ++ tailWord_729295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729322 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_729322 : Nat := 118140960795 + 729322 * 2 ^ 59
def prefixEnd_729322 : Nat := 4983230072969 + 3 ^ 40 * 729322 * 2
def baseEnd_729322 : Nat := 374492737898500758020915

theorem tailTrace_729322 : CollatzResearch.WordTrace tailWord_729322 prefixEnd_729322 374492737898500758020915 := by
  unfold tailWord_729322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6650139665949606781529555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17733705775865618084078813 6650139665949606781529555)
  ·
    refine ⟨9975209498924410172294333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6650139665949606781529555 9975209498924410172294333)
    ·
      refine ⟨3740703562096653814610375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9975209498924410172294333 3740703562096653814610375)
      ·
        refine ⟨5611055343144980721915563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740703562096653814610375 5611055343144980721915563)
        ·
          refine ⟨8416583014717471082873345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5611055343144980721915563 8416583014717471082873345)
          ·
            refine ⟨6312437261038103312155009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8416583014717471082873345 6312437261038103312155009)
            ·
              refine ⟨4734327945778577484116257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6312437261038103312155009 4734327945778577484116257)
              ·
                refine ⟨3550745959333933113087193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4734327945778577484116257 3550745959333933113087193)
                ·
                  refine ⟨2663059469500449834815395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3550745959333933113087193 2663059469500449834815395)
                  ·
                    refine ⟨3994589204250674752223093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2663059469500449834815395 3994589204250674752223093)
                    ·
                      refine ⟨374492737898500758020915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3994589204250674752223093 374492737898500758020915)
                      ·
                        rfl

theorem cell23_729322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_729322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729322 prefixEnd_729322 := by exact prefixLift 729322
  have htrace : WordTrace (prefixWord ++ tailWord_729322) baseStart_729322 baseEnd_729322 := by
    simpa [prefixWord, tailWord_729322, baseEnd_729322] using wordTrace_append hprefix tailTrace_729322
  have hstable : (prefixWord ++ tailWord_729322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729322).length < 2 ^ (prefixWord ++ tailWord_729322).sum := by decide
  have hdescent : baseEnd_729322 < baseStart_729322 := by decide
  rcases family_descends (prefixWord ++ tailWord_729322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729335 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_729335 : Nat := 118140960795 + 729335 * 2 ^ 59
def prefixEnd_729335 : Nat := 4983230072969 + 3 ^ 40 * 729335 * 2
def baseEnd_729335 : Nat := 374499413147009207158355

theorem tailTrace_729335 : CollatzResearch.WordTrace tailWord_729335 prefixEnd_729335 374499413147009207158355 := by
  unfold tailWord_729335
  simp only [CollatzResearch.WordTrace]
  refine ⟨26601032812751330346341459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17734021875167553564227639 26601032812751330346341459)
  ·
    refine ⟨39901549219126995519512189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26601032812751330346341459 39901549219126995519512189)
    ·
      refine ⟨14963080957172623319817071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39901549219126995519512189 14963080957172623319817071)
      ·
        refine ⟨22444621435758934979725607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14963080957172623319817071 22444621435758934979725607)
        ·
          refine ⟨33666932153638402469588411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22444621435758934979725607 33666932153638402469588411)
          ·
            refine ⟨50500398230457603704382617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33666932153638402469588411 50500398230457603704382617)
            ·
              refine ⟨37875298672843202778286963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50500398230457603704382617 37875298672843202778286963)
              ·
                refine ⟨56812948009264804167430445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37875298672843202778286963 56812948009264804167430445)
                ·
                  refine ⟨21304855503474301562786417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56812948009264804167430445 21304855503474301562786417)
                  ·
                    refine ⟨15978641627605726172089813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21304855503474301562786417 15978641627605726172089813)
                    ·
                      refine ⟨374499413147009207158355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15978641627605726172089813 374499413147009207158355)
                      ·
                        rfl

theorem cell23_729335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_729335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729335 prefixEnd_729335 := by exact prefixLift 729335
  have htrace : WordTrace (prefixWord ++ tailWord_729335) baseStart_729335 baseEnd_729335 := by
    simpa [prefixWord, tailWord_729335, baseEnd_729335] using wordTrace_append hprefix tailTrace_729335
  have hstable : (prefixWord ++ tailWord_729335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729335).length < 2 ^ (prefixWord ++ tailWord_729335).sum := by decide
  have hdescent : baseEnd_729335 < baseStart_729335 := by decide
  rcases family_descends (prefixWord ++ tailWord_729335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729372 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_729372 : Nat := 118140960795 + 729372 * 2 ^ 59
def prefixEnd_729372 : Nat := 4983230072969 + 3 ^ 40 * 729372 * 2
def baseEnd_729372 : Nat := 124839470643741854131895

theorem tailTrace_729372 : CollatzResearch.WordTrace tailWord_729372 prefixEnd_729372 124839470643741854131895 := by
  unfold tailWord_729372
  simp only [CollatzResearch.WordTrace]
  refine ⟨13301191156808642832719185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17734921542411523776958913 13301191156808642832719185)
  ·
    refine ⟨9975893367606482124539389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13301191156808642832719185 9975893367606482124539389)
    ·
      refine ⟨3740960012852430796702271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9975893367606482124539389 3740960012852430796702271)
      ·
        refine ⟨5611440019278646195053407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740960012852430796702271 5611440019278646195053407)
        ·
          refine ⟨8417160028917969292580111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5611440019278646195053407 8417160028917969292580111)
          ·
            refine ⟨12625740043376953938870167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8417160028917969292580111 12625740043376953938870167)
            ·
              refine ⟨18938610065065430908305251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12625740043376953938870167 18938610065065430908305251)
              ·
                refine ⟨28407915097598146362457877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18938610065065430908305251 28407915097598146362457877)
                ·
                  refine ⟨1331621020199913110740213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28407915097598146362457877 1331621020199913110740213)
                  ·
                    refine ⟨124839470643741854131895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1331621020199913110740213 124839470643741854131895)
                    ·
                      rfl

theorem cell23_729372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_729372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729372 prefixEnd_729372 := by exact prefixLift 729372
  have htrace : WordTrace (prefixWord ++ tailWord_729372) baseStart_729372 baseEnd_729372 := by
    simpa [prefixWord, tailWord_729372, baseEnd_729372] using wordTrace_append hprefix tailTrace_729372
  have hstable : (prefixWord ++ tailWord_729372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729372).length < 2 ^ (prefixWord ++ tailWord_729372).sum := by decide
  have hdescent : baseEnd_729372 < baseStart_729372 := by decide
  rcases family_descends (prefixWord ++ tailWord_729372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729422 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_729422 : Nat := 118140960795 + 729422 * 2 ^ 59
def prefixEnd_729422 : Nat := 4983230072969 + 3 ^ 40 * 729422 * 2
def baseEnd_729422 : Nat := 374544085963950366770455

theorem tailTrace_729422 : CollatzResearch.WordTrace tailWord_729422 prefixEnd_729422 374544085963950366770455 := by
  unfold tailWord_729422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3325525745429518025594815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17736137308957429469839013 3325525745429518025594815)
  ·
    refine ⟨4988288618144277038392223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3325525745429518025594815 4988288618144277038392223)
    ·
      refine ⟨7482432927216415557588335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4988288618144277038392223 7482432927216415557588335)
      ·
        refine ⟨11223649390824623336382503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7482432927216415557588335 11223649390824623336382503)
        ·
          refine ⟨16835474086236935004573755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11223649390824623336382503 16835474086236935004573755)
          ·
            refine ⟨25253211129355402506860633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16835474086236935004573755 25253211129355402506860633)
            ·
              refine ⟨18939908347016551880145475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25253211129355402506860633 18939908347016551880145475)
              ·
                refine ⟨28409862520524827820218213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18939908347016551880145475 28409862520524827820218213)
                ·
                  refine ⟨5326849222598405216290915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28409862520524827820218213 5326849222598405216290915)
                  ·
                    refine ⟨7990273833897607824436373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5326849222598405216290915 7990273833897607824436373)
                    ·
                      refine ⟨374544085963950366770455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7990273833897607824436373 374544085963950366770455)
                      ·
                        rfl

theorem cell23_729422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_729422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729422 prefixEnd_729422 := by exact prefixLift 729422
  have htrace : WordTrace (prefixWord ++ tailWord_729422) baseStart_729422 baseEnd_729422 := by
    simpa [prefixWord, tailWord_729422, baseEnd_729422] using wordTrace_append hprefix tailTrace_729422
  have hstable : (prefixWord ++ tailWord_729422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729422).length < 2 ^ (prefixWord ++ tailWord_729422).sum := by decide
  have hdescent : baseEnd_729422 < baseStart_729422 := by decide
  rcases family_descends (prefixWord ++ tailWord_729422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729453 : List Nat := [1, 5, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_729453 : Nat := 118140960795 + 729453 * 2 ^ 59
def prefixEnd_729453 : Nat := 4983230072969 + 3 ^ 40 * 729453 * 2
def baseEnd_729453 : Nat := 124853334621413248494271

theorem tailTrace_729453 : CollatzResearch.WordTrace tailWord_729453 prefixEnd_729453 124853334621413248494271 := by
  unfold tailWord_729453
  simp only [CollatzResearch.WordTrace]
  refine ⟨26605336626323836499137013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17736891084215890999424675 26605336626323836499137013)
  ·
    refine ⟨2494250308717859671794095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26605336626323836499137013 2494250308717859671794095)
    ·
      refine ⟨3741375463076789507691143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2494250308717859671794095 3741375463076789507691143)
      ·
        refine ⟨5612063194615184261536715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3741375463076789507691143 5612063194615184261536715)
        ·
          refine ⟨8418094791922776392305073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5612063194615184261536715 8418094791922776392305073)
          ·
            refine ⟨6313571093942082294228805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8418094791922776392305073 6313571093942082294228805)
            ·
              refine ⟨1183794580114140430167901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6313571093942082294228805 1183794580114140430167901)
              ·
                refine ⟨443922967542802661312963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1183794580114140430167901 443922967542802661312963)
                ·
                  refine ⟨665884451314203991969445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443922967542802661312963 665884451314203991969445)
                  ·
                    refine ⟨124853334621413248494271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 665884451314203991969445 124853334621413248494271)
                    ·
                      rfl

theorem cell23_729453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_729453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729453 prefixEnd_729453 := by exact prefixLift 729453
  have htrace : WordTrace (prefixWord ++ tailWord_729453) baseStart_729453 baseEnd_729453 := by
    simpa [prefixWord, tailWord_729453, baseEnd_729453] using wordTrace_append hprefix tailTrace_729453
  have hstable : (prefixWord ++ tailWord_729453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729453).length < 2 ^ (prefixWord ++ tailWord_729453).sum := by decide
  have hdescent : baseEnd_729453 < baseStart_729453 := by decide
  rcases family_descends (prefixWord ++ tailWord_729453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729496 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 1, 5]
def baseStart_729496 : Nat := 118140960795 + 729496 * 2 ^ 59
def prefixEnd_729496 : Nat := 4983230072969 + 3 ^ 40 * 729496 * 2
def baseEnd_729496 : Nat := 124860694510794359081705

theorem tailTrace_729496 : CollatzResearch.WordTrace tailWord_729496 prefixEnd_729496 124860694510794359081705 := by
  unfold tailWord_729496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13303452482584027421476171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17737936643445369895301561 13303452482584027421476171)
  ·
    refine ⟨19955178723876041132214257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13303452482584027421476171 19955178723876041132214257)
    ·
      refine ⟨14966384042907030849160693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19955178723876041132214257 14966384042907030849160693)
      ·
        refine ⟨1403098504022534142108815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14966384042907030849160693 1403098504022534142108815)
        ·
          refine ⟨2104647756033801213163223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403098504022534142108815 2104647756033801213163223)
          ·
            refine ⟨3156971634050701819744835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104647756033801213163223 3156971634050701819744835)
            ·
              refine ⟨4735457451076052729617253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3156971634050701819744835 4735457451076052729617253)
              ·
                refine ⟨887898272076759886803235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4735457451076052729617253 887898272076759886803235)
                ·
                  refine ⟨1331847408115139830204853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887898272076759886803235 1331847408115139830204853)
                  ·
                    refine ⟨124860694510794359081705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1331847408115139830204853 124860694510794359081705)
                    ·
                      rfl

theorem cell23_729496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_729496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729496 prefixEnd_729496 := by exact prefixLift 729496
  have htrace : WordTrace (prefixWord ++ tailWord_729496) baseStart_729496 baseEnd_729496 := by
    simpa [prefixWord, tailWord_729496, baseEnd_729496] using wordTrace_append hprefix tailTrace_729496
  have hstable : (prefixWord ++ tailWord_729496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729496).length < 2 ^ (prefixWord ++ tailWord_729496).sum := by decide
  have hdescent : baseEnd_729496 < baseStart_729496 := by decide
  rcases family_descends (prefixWord ++ tailWord_729496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729509 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 6, 4]
def baseStart_729509 : Nat := 118140960795 + 729509 * 2 ^ 59
def prefixEnd_729509 : Nat := 4983230072969 + 3 ^ 40 * 729509 * 2
def baseEnd_729509 : Nat := 124862919593630508794185

theorem tailTrace_729509 : CollatzResearch.WordTrace tailWord_729509 prefixEnd_729509 124862919593630508794185 := by
  unfold tailWord_729509
  simp only [CollatzResearch.WordTrace]
  refine ⟨26607379114120958063175581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17738252742747305375450387 26607379114120958063175581)
  ·
    refine ⟨9977767167795359273690843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26607379114120958063175581 9977767167795359273690843)
    ·
      refine ⟨14966650751693038910536265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9977767167795359273690843 14966650751693038910536265)
      ·
        refine ⟨11224988063769779182902199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14966650751693038910536265 11224988063769779182902199)
        ·
          refine ⟨16837482095654668774353299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11224988063769779182902199 16837482095654668774353299)
          ·
            refine ⟨25256223143482003161529949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16837482095654668774353299 25256223143482003161529949)
            ·
              refine ⟨9471083678805751185573731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25256223143482003161529949 9471083678805751185573731)
              ·
                refine ⟨14206625518208626778360597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9471083678805751185573731 14206625518208626778360597)
                ·
                  refine ⟨665935571166029380235653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14206625518208626778360597 665935571166029380235653)
                  ·
                    refine ⟨124862919593630508794185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 665935571166029380235653 124862919593630508794185)
                    ·
                      rfl

theorem cell23_729509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_729509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729509 prefixEnd_729509 := by exact prefixLift 729509
  have htrace : WordTrace (prefixWord ++ tailWord_729509) baseStart_729509 baseEnd_729509 := by
    simpa [prefixWord, tailWord_729509, baseEnd_729509] using wordTrace_append hprefix tailTrace_729509
  have hstable : (prefixWord ++ tailWord_729509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729509).length < 2 ^ (prefixWord ++ tailWord_729509).sum := by decide
  have hdescent : baseEnd_729509 < baseStart_729509 := by decide
  rcases family_descends (prefixWord ++ tailWord_729509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729519 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 3]
def baseStart_729519 : Nat := 118140960795 + 729519 * 2 ^ 59
def prefixEnd_729519 : Nat := 4983230072969 + 3 ^ 40 * 729519 * 2
def baseEnd_729519 : Nat := 374593893587436487257509

theorem tailTrace_729519 : CollatzResearch.WordTrace tailWord_729519 prefixEnd_729519 374593893587436487257509 := by
  unfold tailWord_729519
  simp only [CollatzResearch.WordTrace]
  refine ⟨26607743844084729771039611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17738495896056486514026407 26607743844084729771039611)
  ·
    refine ⟨39911615766127094656559417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26607743844084729771039611 39911615766127094656559417)
    ·
      refine ⟨29933711824595320992419563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39911615766127094656559417 29933711824595320992419563)
      ·
        refine ⟨44900567736892981488629345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29933711824595320992419563 44900567736892981488629345)
        ·
          refine ⟨33675425802669736116472009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44900567736892981488629345 33675425802669736116472009)
          ·
            refine ⟨25256569352002302087354007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33675425802669736116472009 25256569352002302087354007)
            ·
              refine ⟨37884854028003453131031011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25256569352002302087354007 37884854028003453131031011)
              ·
                refine ⟨56827281042005179696546517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37884854028003453131031011 56827281042005179696546517)
                ·
                  refine ⟨1331889399421996399137809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 56827281042005179696546517 1331889399421996399137809)
                  ·
                    refine ⟨998917049566497299353357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1331889399421996399137809 998917049566497299353357)
                    ·
                      refine ⟨374593893587436487257509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 998917049566497299353357 374593893587436487257509)
                      ·
                        rfl

theorem cell23_729519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 3].length) (baseStart_729519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729519 prefixEnd_729519 := by exact prefixLift 729519
  have htrace : WordTrace (prefixWord ++ tailWord_729519) baseStart_729519 baseEnd_729519 := by
    simpa [prefixWord, tailWord_729519, baseEnd_729519] using wordTrace_append hprefix tailTrace_729519
  have hstable : (prefixWord ++ tailWord_729519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729519).length < 2 ^ (prefixWord ++ tailWord_729519).sum := by decide
  have hdescent : baseEnd_729519 < baseStart_729519 := by decide
  rcases family_descends (prefixWord ++ tailWord_729519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729529 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 6]
def baseStart_729529 : Nat := 118140960795 + 729529 * 2 ^ 59
def prefixEnd_729529 : Nat := 4983230072969 + 3 ^ 40 * 729529 * 2
def baseEnd_729529 : Nat := 374599028393981448132463

theorem tailTrace_729529 : CollatzResearch.WordTrace tailWord_729529 prefixEnd_729529 374599028393981448132463 := by
  unfold tailWord_729529
  simp only [CollatzResearch.WordTrace]
  refine ⟨26608108574048501478903641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17738739049365667652602427 26608108574048501478903641)
  ·
    refine ⟨19956081430536376109177731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26608108574048501478903641 19956081430536376109177731)
    ·
      refine ⟨29934122145804564163766597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19956081430536376109177731 29934122145804564163766597)
      ·
        refine ⟨5612647902338355780706237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29934122145804564163766597 5612647902338355780706237)
        ·
          refine ⟨2104742963376883417764839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5612647902338355780706237 2104742963376883417764839)
          ·
            refine ⟨3157114445065325126647259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104742963376883417764839 3157114445065325126647259)
            ·
              refine ⟨4735671667597987689970889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157114445065325126647259 4735671667597987689970889)
              ·
                refine ⟨3551753750698490767478167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4735671667597987689970889 3551753750698490767478167)
                ·
                  refine ⟨5327630626047736151217251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551753750698490767478167 5327630626047736151217251)
                  ·
                    refine ⟨7991445939071604226825877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5327630626047736151217251 7991445939071604226825877)
                    ·
                      refine ⟨374599028393981448132463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7991445939071604226825877 374599028393981448132463)
                      ·
                        rfl

theorem cell23_729529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_729529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729529 prefixEnd_729529 := by exact prefixLift 729529
  have htrace : WordTrace (prefixWord ++ tailWord_729529) baseStart_729529 baseEnd_729529 := by
    simpa [prefixWord, tailWord_729529, baseEnd_729529] using wordTrace_append hprefix tailTrace_729529
  have hstable : (prefixWord ++ tailWord_729529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729529).length < 2 ^ (prefixWord ++ tailWord_729529).sum := by decide
  have hdescent : baseEnd_729529 < baseStart_729529 := by decide
  rcases family_descends (prefixWord ++ tailWord_729529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729543 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 2, 4]
def baseStart_729543 : Nat := 118140960795 + 729543 * 2 ^ 59
def prefixEnd_729543 : Nat := 4983230072969 + 3 ^ 40 * 729543 * 2
def baseEnd_729543 : Nat := 124868739041048131119133

theorem tailTrace_729543 : CollatzResearch.WordTrace tailWord_729543 prefixEnd_729543 124868739041048131119133 := by
  unfold tailWord_729543
  simp only [CollatzResearch.WordTrace]
  refine ⟨26608619195997781869913283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17739079463998521246608855 26608619195997781869913283)
  ·
    refine ⟨39912928793996672804869925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26608619195997781869913283 39912928793996672804869925)
    ·
      refine ⟨7483674148874376150913111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39912928793996672804869925 7483674148874376150913111)
      ·
        refine ⟨11225511223311564226369667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7483674148874376150913111 11225511223311564226369667)
        ·
          refine ⟨16838266834967346339554501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11225511223311564226369667 16838266834967346339554501)
          ·
            refine ⟨3157175031556377438666469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16838266834967346339554501 3157175031556377438666469)
            ·
              refine ⟨591970318416820769749963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3157175031556377438666469 591970318416820769749963)
              ·
                refine ⟨887955477625231154624945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591970318416820769749963 887955477625231154624945)
                ·
                  refine ⟨665966608218923365968709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 887955477625231154624945 665966608218923365968709)
                  ·
                    refine ⟨124868739041048131119133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 665966608218923365968709 124868739041048131119133)
                    ·
                      rfl

theorem cell23_729543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_729543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729543 prefixEnd_729543 := by exact prefixLift 729543
  have htrace : WordTrace (prefixWord ++ tailWord_729543) baseStart_729543 baseEnd_729543 := by
    simpa [prefixWord, tailWord_729543, baseEnd_729543] using wordTrace_append hprefix tailTrace_729543
  have hstable : (prefixWord ++ tailWord_729543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729543).length < 2 ^ (prefixWord ++ tailWord_729543).sum := by decide
  have hdescent : baseEnd_729543 < baseStart_729543 := by decide
  rcases family_descends (prefixWord ++ tailWord_729543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729599 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 2, 6]
def baseStart_729599 : Nat := 118140960795 + 729599 * 2 ^ 59
def prefixEnd_729599 : Nat := 4983230072969 + 3 ^ 40 * 729599 * 2
def baseEnd_729599 : Nat := 124878324013265391419047

theorem tailTrace_729599 : CollatzResearch.WordTrace tailWord_729599 prefixEnd_729599 124878324013265391419047 := by
  unfold tailWord_729599
  simp only [CollatzResearch.WordTrace]
  refine ⟨26610661683794903433951851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17740441122529935622634567 26610661683794903433951851)
  ·
    refine ⟨39915992525692355150927777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26610661683794903433951851 39915992525692355150927777)
    ·
      refine ⟨29936994394269266363195833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39915992525692355150927777 29936994394269266363195833)
      ·
        refine ⟨22452745795701949772396875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29936994394269266363195833 22452745795701949772396875)
        ·
          refine ⟨33679118693552924658595313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22452745795701949772396875 33679118693552924658595313)
          ·
            refine ⟨25259339020164693493946485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33679118693552924658595313 25259339020164693493946485)
            ·
              refine ⟨2368063033140440015057483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25259339020164693493946485 2368063033140440015057483)
              ·
                refine ⟨3552094549710660022586225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368063033140440015057483 3552094549710660022586225)
                ·
                  refine ⟨2664070912282995016939669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3552094549710660022586225 2664070912282995016939669)
                  ·
                    refine ⟨124878324013265391419047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2664070912282995016939669 124878324013265391419047)
                    ·
                      rfl

theorem cell23_729599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_729599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729599 prefixEnd_729599 := by exact prefixLift 729599
  have htrace : WordTrace (prefixWord ++ tailWord_729599) baseStart_729599 baseEnd_729599 := by
    simpa [prefixWord, tailWord_729599, baseEnd_729599] using wordTrace_append hprefix tailTrace_729599
  have hstable : (prefixWord ++ tailWord_729599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729599).length < 2 ^ (prefixWord ++ tailWord_729599).sum := by decide
  have hdescent : baseEnd_729599 < baseStart_729599 := by decide
  rcases family_descends (prefixWord ++ tailWord_729599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729609 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 5]
def baseStart_729609 : Nat := 118140960795 + 729609 * 2 ^ 59
def prefixEnd_729609 : Nat := 4983230072969 + 3 ^ 40 * 729609 * 2
def baseEnd_729609 : Nat := 374640106846341135132095

theorem tailTrace_729609 : CollatzResearch.WordTrace tailWord_729609 prefixEnd_729609 374640106846341135132095 := by
  unfold tailWord_729609
  simp only [CollatzResearch.WordTrace]
  refine ⟨26611026413758675141815881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17740684275839116761210587 26611026413758675141815881)
  ·
    refine ⟨19958269810319006356361911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26611026413758675141815881 19958269810319006356361911)
    ·
      refine ⟨29937404715478509534542867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19958269810319006356361911 29937404715478509534542867)
      ·
        refine ⟨44906107073217764301814301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29937404715478509534542867 44906107073217764301814301)
        ·
          refine ⟨16839790152456661613180363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44906107073217764301814301 16839790152456661613180363)
          ·
            refine ⟨25259685228684992419770545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16839790152456661613180363 25259685228684992419770545)
            ·
              refine ⟨18944763921513744314827909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25259685228684992419770545 18944763921513744314827909)
              ·
                refine ⟨3552143235283827059030233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18944763921513744314827909 3552143235283827059030233)
                ·
                  refine ⟨2664107426462870294272675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3552143235283827059030233 2664107426462870294272675)
                  ·
                    refine ⟨3996161139694305441409013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2664107426462870294272675 3996161139694305441409013)
                    ·
                      refine ⟨374640106846341135132095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3996161139694305441409013 374640106846341135132095)
                      ·
                        rfl

theorem cell23_729609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_729609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729609 prefixEnd_729609 := by exact prefixLift 729609
  have htrace : WordTrace (prefixWord ++ tailWord_729609) baseStart_729609 baseEnd_729609 := by
    simpa [prefixWord, tailWord_729609, baseEnd_729609] using wordTrace_append hprefix tailTrace_729609
  have hstable : (prefixWord ++ tailWord_729609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729609).length < 2 ^ (prefixWord ++ tailWord_729609).sum := by decide
  have hdescent : baseEnd_729609 < baseStart_729609 := by decide
  rcases family_descends (prefixWord ++ tailWord_729609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729619 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 4]
def baseStart_729619 : Nat := 118140960795 + 729619 * 2 ^ 59
def prefixEnd_729619 : Nat := 4983230072969 + 3 ^ 40 * 729619 * 2
def baseEnd_729619 : Nat := 374645241652886096007049

theorem tailTrace_729619 : CollatzResearch.WordTrace tailWord_729619 prefixEnd_729619 374645241652886096007049 := by
  unfold tailWord_729619
  simp only [CollatzResearch.WordTrace]
  refine ⟨26611391143722446849679911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17740927429148297899786607 26611391143722446849679911)
  ·
    refine ⟨39917086715583670274519867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26611391143722446849679911 39917086715583670274519867)
    ·
      refine ⟨59875630073375505411779801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39917086715583670274519867 59875630073375505411779801)
      ·
        refine ⟨44906722555031629058834851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59875630073375505411779801 44906722555031629058834851)
        ·
          refine ⟨67360083832547443588252277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44906722555031629058834851 67360083832547443588252277)
          ·
            refine ⟨6315007859301322836398651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67360083832547443588252277 6315007859301322836398651)
            ·
              refine ⟨9472511788951984254597977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6315007859301322836398651 9472511788951984254597977)
              ·
                refine ⟨7104383841713988190948483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9472511788951984254597977 7104383841713988190948483)
                ·
                  refine ⟨10656575762570982286422725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7104383841713988190948483 10656575762570982286422725)
                  ·
                    refine ⟨1998107955482059178704261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10656575762570982286422725 1998107955482059178704261)
                    ·
                      refine ⟨374645241652886096007049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1998107955482059178704261 374645241652886096007049)
                      ·
                        rfl

theorem cell23_729619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_729619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729619 prefixEnd_729619 := by exact prefixLift 729619
  have htrace : WordTrace (prefixWord ++ tailWord_729619) baseStart_729619 baseEnd_729619 := by
    simpa [prefixWord, tailWord_729619, baseEnd_729619] using wordTrace_append hprefix tailTrace_729619
  have hstable : (prefixWord ++ tailWord_729619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729619).length < 2 ^ (prefixWord ++ tailWord_729619).sum := by decide
  have hdescent : baseEnd_729619 < baseStart_729619 := by decide
  rcases family_descends (prefixWord ++ tailWord_729619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729656 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 2, 3, 3]
def baseStart_729656 : Nat := 118140960795 + 729656 * 2 ^ 59
def prefixEnd_729656 : Nat := 4983230072969 + 3 ^ 40 * 729656 * 2
def baseEnd_729656 : Nat := 374664240437102451244379

theorem tailTrace_729656 : CollatzResearch.WordTrace tailWord_729656 prefixEnd_729656 374664240437102451244379 := by
  unfold tailWord_729656
  simp only [CollatzResearch.WordTrace]
  refine ⟨13306370322294201084388411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17741827096392268112517881 13306370322294201084388411)
  ·
    refine ⟨19959555483441301626582617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13306370322294201084388411 19959555483441301626582617)
    ·
      refine ⟨14969666612580976219936963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19959555483441301626582617 14969666612580976219936963)
      ·
        refine ⟨22454499918871464329905445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14969666612580976219936963 22454499918871464329905445)
        ·
          refine ⟨4210218734788399561857271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22454499918871464329905445 4210218734788399561857271)
          ·
            refine ⟨6315328102182599342785907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210218734788399561857271 6315328102182599342785907)
            ·
              refine ⟨9472992153273899014178861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6315328102182599342785907 9472992153273899014178861)
              ·
                refine ⟨3552372057477712130317073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9472992153273899014178861 3552372057477712130317073)
                ·
                  refine ⟨2664279043108284097737805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3552372057477712130317073 2664279043108284097737805)
                  ·
                    refine ⟨999104641165606536651677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664279043108284097737805 999104641165606536651677)
                    ·
                      refine ⟨374664240437102451244379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 999104641165606536651677 374664240437102451244379)
                      ·
                        rfl

theorem cell23_729656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_729656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729656 prefixEnd_729656 := by exact prefixLift 729656
  have htrace : WordTrace (prefixWord ++ tailWord_729656) baseStart_729656 baseEnd_729656 := by
    simpa [prefixWord, tailWord_729656, baseEnd_729656] using wordTrace_append hprefix tailTrace_729656
  have hstable : (prefixWord ++ tailWord_729656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729656).length < 2 ^ (prefixWord ++ tailWord_729656).sum := by decide
  have hdescent : baseEnd_729656 < baseStart_729656 := by decide
  rcases family_descends (prefixWord ++ tailWord_729656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729657 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 2, 2, 2]
def baseStart_729657 : Nat := 118140960795 + 729657 * 2 ^ 59
def prefixEnd_729657 : Nat := 4983230072969 + 3 ^ 40 * 729657 * 2
def baseEnd_729657 : Nat := 374664753917756947331875

theorem tailTrace_729657 : CollatzResearch.WordTrace tailWord_729657 prefixEnd_729657 374664753917756947331875 := by
  unfold tailWord_729657
  simp only [CollatzResearch.WordTrace]
  refine ⟨26612777117584779339563225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17741851411723186226375483 26612777117584779339563225)
  ·
    refine ⟨19959582838188584504672419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26612777117584779339563225 19959582838188584504672419)
    ·
      refine ⟨29939374257282876757008629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19959582838188584504672419 29939374257282876757008629)
      ·
        refine ⟨2806816336620269695969559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29939374257282876757008629 2806816336620269695969559)
        ·
          refine ⟨4210224504930404543954339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2806816336620269695969559 4210224504930404543954339)
          ·
            refine ⟨6315336757395606815931509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210224504930404543954339 6315336757395606815931509)
            ·
              refine ⟨592062821005838138993579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6315336757395606815931509 592062821005838138993579)
              ·
                refine ⟨888094231508757208490369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592062821005838138993579 888094231508757208490369)
                ·
                  refine ⟨666070673631567906367777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 888094231508757208490369 666070673631567906367777)
                  ·
                    refine ⟨499553005223675929775833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 666070673631567906367777 499553005223675929775833)
                    ·
                      refine ⟨374664753917756947331875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 499553005223675929775833 374664753917756947331875)
                      ·
                        rfl

theorem cell23_729657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_729657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729657 prefixEnd_729657 := by exact prefixLift 729657
  have htrace : WordTrace (prefixWord ++ tailWord_729657) baseStart_729657 baseEnd_729657 := by
    simpa [prefixWord, tailWord_729657, baseEnd_729657] using wordTrace_append hprefix tailTrace_729657
  have hstable : (prefixWord ++ tailWord_729657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729657).length < 2 ^ (prefixWord ++ tailWord_729657).sum := by decide
  have hdescent : baseEnd_729657 < baseStart_729657 := by decide
  rcases family_descends (prefixWord ++ tailWord_729657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729676 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_729676 : Nat := 118140960795 + 729676 * 2 ^ 59
def prefixEnd_729676 : Nat := 4983230072969 + 3 ^ 40 * 729676 * 2
def baseEnd_729676 : Nat := 124891503350064124331429

theorem tailTrace_729676 : CollatzResearch.WordTrace tailWord_729676 prefixEnd_729676 124891503350064124331429 := by
  unfold tailWord_729676
  simp only [CollatzResearch.WordTrace]
  refine ⟨13306735052257972792252441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17742313403010630389669921 13306735052257972792252441)
  ·
    refine ⟨9980051289193479594189331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13306735052257972792252441 9980051289193479594189331)
    ·
      refine ⟨14970076933790219391283997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9980051289193479594189331 14970076933790219391283997)
      ·
        refine ⟨5613778850171332271731499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14970076933790219391283997 5613778850171332271731499)
        ·
          refine ⟨8420668275256998407597249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5613778850171332271731499 8420668275256998407597249)
          ·
            refine ⟨6315501206442748805697937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8420668275256998407597249 6315501206442748805697937)
            ·
              refine ⟨4736625904832061604273453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6315501206442748805697937 4736625904832061604273453)
              ·
                refine ⟨1776234714312023101602545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4736625904832061604273453 1776234714312023101602545)
                ·
                  refine ⟨1332176035734017326201909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1776234714312023101602545 1332176035734017326201909)
                  ·
                    refine ⟨124891503350064124331429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1332176035734017326201909 124891503350064124331429)
                    ·
                      rfl

theorem cell23_729676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_729676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729676 prefixEnd_729676 := by exact prefixLift 729676
  have htrace : WordTrace (prefixWord ++ tailWord_729676) baseStart_729676 baseEnd_729676 := by
    simpa [prefixWord, tailWord_729676, baseEnd_729676] using wordTrace_append hprefix tailTrace_729676
  have hstable : (prefixWord ++ tailWord_729676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729676).length < 2 ^ (prefixWord ++ tailWord_729676).sum := by decide
  have hdescent : baseEnd_729676 < baseStart_729676 := by decide
  rcases family_descends (prefixWord ++ tailWord_729676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729696 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 4]
def baseStart_729696 : Nat := 118140960795 + 729696 * 2 ^ 59
def prefixEnd_729696 : Nat := 4983230072969 + 3 ^ 40 * 729696 * 2
def baseEnd_729696 : Nat := 374684779663282294744195

theorem tailTrace_729696 : CollatzResearch.WordTrace tailWord_729696 prefixEnd_729696 374684779663282294744195 := by
  unfold tailWord_729696
  simp only [CollatzResearch.WordTrace]
  refine ⟨13307099782221744500116471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17742799709628992666821961 13307099782221744500116471)
  ·
    refine ⟨19960649673332616750174707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13307099782221744500116471 19960649673332616750174707)
    ·
      refine ⟨29940974509998925125262061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19960649673332616750174707 29940974509998925125262061)
      ·
        refine ⟨11227865441249596921973273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29940974509998925125262061 11227865441249596921973273)
        ·
          refine ⟨8420899080937197691479955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11227865441249596921973273 8420899080937197691479955)
          ·
            refine ⟨12631348621405796537219933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8420899080937197691479955 12631348621405796537219933)
            ·
              refine ⟨4736755733027173701457475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12631348621405796537219933 4736755733027173701457475)
              ·
                refine ⟨7105133599540760552186213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736755733027173701457475 7105133599540760552186213)
                ·
                  refine ⟨1332212549913892603534915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7105133599540760552186213 1332212549913892603534915)
                  ·
                    refine ⟨1998318824870838905302373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1332212549913892603534915 1998318824870838905302373)
                    ·
                      refine ⟨374684779663282294744195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1998318824870838905302373 374684779663282294744195)
                      ·
                        rfl

theorem cell23_729696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_729696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729696 prefixEnd_729696 := by exact prefixLift 729696
  have htrace : WordTrace (prefixWord ++ tailWord_729696) baseStart_729696 baseEnd_729696 := by
    simpa [prefixWord, tailWord_729696, baseEnd_729696] using wordTrace_append hprefix tailTrace_729696
  have hstable : (prefixWord ++ tailWord_729696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729696).length < 2 ^ (prefixWord ++ tailWord_729696).sum := by decide
  have hdescent : baseEnd_729696 < baseStart_729696 := by decide
  rcases family_descends (prefixWord ++ tailWord_729696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729733 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 2, 2, 3]
def baseStart_729733 : Nat := 118140960795 + 729733 * 2 ^ 59
def prefixEnd_729733 : Nat := 4983230072969 + 3 ^ 40 * 729733 * 2
def baseEnd_729733 : Nat := 374703778447498649981525

theorem tailTrace_729733 : CollatzResearch.WordTrace tailWord_729733 prefixEnd_729733 374703778447498649981525 := by
  unfold tailWord_729733
  simp only [CollatzResearch.WordTrace]
  refine ⟨26615549065309444319329853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17743699376872962879553235 26615549065309444319329853)
  ·
    refine ⟨9980830899491041619748695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26615549065309444319329853 9980830899491041619748695)
    ·
      refine ⟨14971246349236562429623043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9980830899491041619748695 14971246349236562429623043)
      ·
        refine ⟨22456869523854843644434565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14971246349236562429623043 22456869523854843644434565)
        ·
          refine ⟨4210663035722783183331481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22456869523854843644434565 4210663035722783183331481)
          ·
            refine ⟨3157997276792087387498611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4210663035722783183331481 3157997276792087387498611)
            ·
              refine ⟨4736995915188131081247917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157997276792087387498611 4736995915188131081247917)
              ·
                refine ⟨1776373468195549155467969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4736995915188131081247917 1776373468195549155467969)
                ·
                  refine ⟨1332280101146661866600977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1776373468195549155467969 1332280101146661866600977)
                  ·
                    refine ⟨999210075859996399950733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1332280101146661866600977 999210075859996399950733)
                    ·
                      refine ⟨374703778447498649981525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 999210075859996399950733 374703778447498649981525)
                      ·
                        rfl

theorem cell23_729733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_729733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729733 prefixEnd_729733 := by exact prefixLift 729733
  have htrace : WordTrace (prefixWord ++ tailWord_729733) baseStart_729733 baseEnd_729733 := by
    simpa [prefixWord, tailWord_729733, baseEnd_729733] using wordTrace_append hprefix tailTrace_729733
  have hstable : (prefixWord ++ tailWord_729733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729733).length < 2 ^ (prefixWord ++ tailWord_729733).sum := by decide
  have hdescent : baseEnd_729733 < baseStart_729733 := by decide
  rcases family_descends (prefixWord ++ tailWord_729733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729757 : List Nat := [1, 4, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_729757 : Nat := 118140960795 + 729757 * 2 ^ 59
def prefixEnd_729757 : Nat := 4983230072969 + 3 ^ 40 * 729757 * 2
def baseEnd_729757 : Nat := 124905367327735518693805

theorem tailTrace_729757 : CollatzResearch.WordTrace tailWord_729757 prefixEnd_729757 124905367327735518693805 := by
  unfold tailWord_729757
  simp only [CollatzResearch.WordTrace]
  refine ⟨26616424417222496418203525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17744282944814997612135683 26616424417222496418203525)
  ·
    refine ⟨4990579578229218078413161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26616424417222496418203525 4990579578229218078413161)
    ·
      refine ⟨3742934683671913558809871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4990579578229218078413161 3742934683671913558809871)
      ·
        refine ⟨5614402025507870338214807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3742934683671913558809871 5614402025507870338214807)
        ·
          refine ⟨8421603038261805507322211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5614402025507870338214807 8421603038261805507322211)
          ·
            refine ⟨12632404557392708260983317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8421603038261805507322211 12632404557392708260983317)
            ·
              refine ⟨592143963627783199733593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12632404557392708260983317 592143963627783199733593)
              ·
                refine ⟨444107972720837399800195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 592143963627783199733593 444107972720837399800195)
                ·
                  refine ⟨666161959081256099700293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444107972720837399800195 666161959081256099700293)
                  ·
                    refine ⟨124905367327735518693805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 666161959081256099700293 124905367327735518693805)
                    ·
                      rfl

theorem cell23_729757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_729757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729757 prefixEnd_729757 := by exact prefixLift 729757
  have htrace : WordTrace (prefixWord ++ tailWord_729757) baseStart_729757 baseEnd_729757 := by
    simpa [prefixWord, tailWord_729757, baseEnd_729757] using wordTrace_append hprefix tailTrace_729757
  have hstable : (prefixWord ++ tailWord_729757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729757).length < 2 ^ (prefixWord ++ tailWord_729757).sum := by decide
  have hdescent : baseEnd_729757 < baseStart_729757 := by decide
  rcases family_descends (prefixWord ++ tailWord_729757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729790 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_729790 : Nat := 118140960795 + 729790 * 2 ^ 59
def prefixEnd_729790 : Nat := 4983230072969 + 3 ^ 40 * 729790 * 2
def baseEnd_729790 : Nat := 374733046844804926968763

theorem tailTrace_729790 : CollatzResearch.WordTrace tailWord_729790 prefixEnd_729790 374733046844804926968763 := by
  unfold tailWord_729790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3327203503262867881769353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17745085350735295369436549 3327203503262867881769353)
  ·
    refine ⟨2495402627447150911327015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3327203503262867881769353 2495402627447150911327015)
    ·
      refine ⟨3743103941170726366990523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2495402627447150911327015 3743103941170726366990523)
      ·
        refine ⟨5614655911756089550485785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3743103941170726366990523 5614655911756089550485785)
        ·
          refine ⟨4210991933817067162864339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5614655911756089550485785 4210991933817067162864339)
          ·
            refine ⟨6316487900725600744296509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210991933817067162864339 6316487900725600744296509)
            ·
              refine ⟨2368682962772100279111191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6316487900725600744296509 2368682962772100279111191)
              ·
                refine ⟨3553024444158150418666787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368682962772100279111191 3553024444158150418666787)
                ·
                  refine ⟨5329536666237225628000181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553024444158150418666787 5329536666237225628000181)
                  ·
                    refine ⟨499644062459739902625017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5329536666237225628000181 499644062459739902625017)
                    ·
                      refine ⟨374733046844804926968763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 499644062459739902625017 374733046844804926968763)
                      ·
                        rfl

theorem cell23_729790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_729790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729790 prefixEnd_729790 := by exact prefixLift 729790
  have htrace : WordTrace (prefixWord ++ tailWord_729790) baseStart_729790 baseEnd_729790 := by
    simpa [prefixWord, tailWord_729790, baseEnd_729790] using wordTrace_append hprefix tailTrace_729790
  have hstable : (prefixWord ++ tailWord_729790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729790).length < 2 ^ (prefixWord ++ tailWord_729790).sum := by decide
  have hdescent : baseEnd_729790 < baseStart_729790 := by decide
  rcases family_descends (prefixWord ++ tailWord_729790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729800 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 1, 5]
def baseStart_729800 : Nat := 118140960795 + 729800 * 2 ^ 59
def prefixEnd_729800 : Nat := 4983230072969 + 3 ^ 40 * 729800 * 2
def baseEnd_729800 : Nat := 124912727217116629281239

theorem tailTrace_729800 : CollatzResearch.WordTrace tailWord_729800 prefixEnd_729800 124912727217116629281239 := by
  unfold tailWord_729800
  simp only [CollatzResearch.WordTrace]
  refine ⟨13308996378033357381009427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17745328504044476508012569 13308996378033357381009427)
  ·
    refine ⟨19963494567050036071514141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13308996378033357381009427 19963494567050036071514141)
    ·
      refine ⟨7486310462643763526817803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19963494567050036071514141 7486310462643763526817803)
      ·
        refine ⟨11229465693965645290226705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7486310462643763526817803 11229465693965645290226705)
        ·
          refine ⟨8422099270474233967670029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11229465693965645290226705 8422099270474233967670029)
          ·
            refine ⟨3158287226427837737876261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8422099270474233967670029 3158287226427837737876261)
            ·
              refine ⟨592178854955219575851799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3158287226427837737876261 592178854955219575851799)
              ·
                refine ⟨888268282432829363777699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592178854955219575851799 888268282432829363777699)
                ·
                  refine ⟨1332402423649244045666549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888268282432829363777699 1332402423649244045666549)
                  ·
                    refine ⟨124912727217116629281239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1332402423649244045666549 124912727217116629281239)
                    ·
                      rfl

theorem cell23_729800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_729800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729800 prefixEnd_729800 := by exact prefixLift 729800
  have htrace : WordTrace (prefixWord ++ tailWord_729800) baseStart_729800 baseEnd_729800 := by
    simpa [prefixWord, tailWord_729800, baseEnd_729800] using wordTrace_append hprefix tailTrace_729800
  have hstable : (prefixWord ++ tailWord_729800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729800).length < 2 ^ (prefixWord ++ tailWord_729800).sum := by decide
  have hdescent : baseEnd_729800 < baseStart_729800 := by decide
  rcases family_descends (prefixWord ++ tailWord_729800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729823 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 5]
def baseStart_729823 : Nat := 118140960795 + 729823 * 2 ^ 59
def prefixEnd_729823 : Nat := 4983230072969 + 3 ^ 40 * 729823 * 2
def baseEnd_729823 : Nat := 374749991706403297856111

theorem tailTrace_729823 : CollatzResearch.WordTrace tailWord_729823 prefixEnd_729823 374749991706403297856111 := by
  unfold tailWord_729823
  simp only [CollatzResearch.WordTrace]
  refine ⟨26618831634983389690106123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17745887756655593126737415 26618831634983389690106123)
  ·
    refine ⟨39928247452475084535159185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26618831634983389690106123 39928247452475084535159185)
    ·
      refine ⟨29946185589356313401369389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39928247452475084535159185 29946185589356313401369389)
      ·
        refine ⟨11229819596008617525513521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29946185589356313401369389 11229819596008617525513521)
        ·
          refine ⟨8422364697006463144135141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11229819596008617525513521 8422364697006463144135141)
          ·
            refine ⟨1579193380688711839525339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8422364697006463144135141 1579193380688711839525339)
            ·
              refine ⟨2368790071033067759288009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579193380688711839525339 2368790071033067759288009)
              ·
                refine ⟨1776592553274800819466007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2368790071033067759288009 1776592553274800819466007)
                ·
                  refine ⟨2664888829912201229199011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776592553274800819466007 2664888829912201229199011)
                  ·
                    refine ⟨3997333244868301843798517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2664888829912201229199011 3997333244868301843798517)
                    ·
                      refine ⟨374749991706403297856111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3997333244868301843798517 374749991706403297856111)
                      ·
                        rfl

theorem cell23_729823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_729823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729823 prefixEnd_729823 := by exact prefixLift 729823
  have htrace : WordTrace (prefixWord ++ tailWord_729823) baseStart_729823 baseEnd_729823 := by
    simpa [prefixWord, tailWord_729823, baseEnd_729823] using wordTrace_append hprefix tailTrace_729823
  have hstable : (prefixWord ++ tailWord_729823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729823).length < 2 ^ (prefixWord ++ tailWord_729823).sum := by decide
  have hdescent : baseEnd_729823 < baseStart_729823 := by decide
  rcases family_descends (prefixWord ++ tailWord_729823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729833 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 4]
def baseStart_729833 : Nat := 118140960795 + 729833 * 2 ^ 59
def prefixEnd_729833 : Nat := 4983230072969 + 3 ^ 40 * 729833 * 2
def baseEnd_729833 : Nat := 374755126512948258731065

theorem tailTrace_729833 : CollatzResearch.WordTrace tailWord_729833 prefixEnd_729833 374755126512948258731065 := by
  unfold tailWord_729833
  simp only [CollatzResearch.WordTrace]
  refine ⟨26619196364947161397970153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17746130909964774265313435 26619196364947161397970153)
  ·
    refine ⟨19964397273710371048477615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26619196364947161397970153 19964397273710371048477615)
    ·
      refine ⟨29946595910565556572716423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19964397273710371048477615 29946595910565556572716423)
      ·
        refine ⟨44919893865848334859074635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29946595910565556572716423 44919893865848334859074635)
        ·
          refine ⟨67379840798772502288611953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44919893865848334859074635 67379840798772502288611953)
          ·
            refine ⟨50534880599079376716458965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67379840798772502288611953 50534880599079376716458965)
            ·
              refine ⟨1184411264040922891792007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 50534880599079376716458965 1184411264040922891792007)
              ·
                refine ⟨1776616896061384337688011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184411264040922891792007 1776616896061384337688011)
                ·
                  refine ⟨2664925344092076506532017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776616896061384337688011 2664925344092076506532017)
                  ·
                    refine ⟨1998694008069057379899013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2664925344092076506532017 1998694008069057379899013)
                    ·
                      refine ⟨374755126512948258731065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1998694008069057379899013 374755126512948258731065)
                      ·
                        rfl

theorem cell23_729833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 4].length) (baseStart_729833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729833 prefixEnd_729833 := by exact prefixLift 729833
  have htrace : WordTrace (prefixWord ++ tailWord_729833) baseStart_729833 baseEnd_729833 := by
    simpa [prefixWord, tailWord_729833, baseEnd_729833] using wordTrace_append hprefix tailTrace_729833
  have hstable : (prefixWord ++ tailWord_729833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729833).length < 2 ^ (prefixWord ++ tailWord_729833).sum := by decide
  have hdescent : baseEnd_729833 < baseStart_729833 := by decide
  rcases family_descends (prefixWord ++ tailWord_729833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729837 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_729837 : Nat := 118140960795 + 729837 * 2 ^ 59
def prefixEnd_729837 : Nat := 4983230072969 + 3 ^ 40 * 729837 * 2
def baseEnd_729837 : Nat := 374757180435566243081047

theorem tailTrace_729837 : CollatzResearch.WordTrace tailWord_729837 prefixEnd_729837 374757180435566243081047 := by
  unfold tailWord_729837
  simp only [CollatzResearch.WordTrace]
  refine ⟨26619342256932670081115765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17746228171288446720743843 26619342256932670081115765)
  ·
    refine ⟨2495563336587437820104603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26619342256932670081115765 2495563336587437820104603)
    ·
      refine ⟨3743345004881156730156905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2495563336587437820104603 3743345004881156730156905)
      ·
        refine ⟨2807508753660867547617679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3743345004881156730156905 2807508753660867547617679)
        ·
          refine ⟨4211263130491301321426519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807508753660867547617679 4211263130491301321426519)
          ·
            refine ⟨6316894695736951982139779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4211263130491301321426519 6316894695736951982139779)
            ·
              refine ⟨9475342043605427973209669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316894695736951982139779 9475342043605427973209669)
              ·
                refine ⟨1776626633176017744976813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9475342043605427973209669 1776626633176017744976813)
                ·
                  refine ⟨666234987441006654366305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1776626633176017744976813 666234987441006654366305)
                  ·
                    refine ⟨499676240580754990774729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 666234987441006654366305 499676240580754990774729)
                    ·
                      refine ⟨374757180435566243081047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 499676240580754990774729 374757180435566243081047)
                      ·
                        rfl

theorem cell23_729837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_729837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729837 prefixEnd_729837 := by exact prefixLift 729837
  have htrace : WordTrace (prefixWord ++ tailWord_729837) baseStart_729837 baseEnd_729837 := by
    simpa [prefixWord, tailWord_729837, baseEnd_729837] using wordTrace_append hprefix tailTrace_729837
  have hstable : (prefixWord ++ tailWord_729837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729837).length < 2 ^ (prefixWord ++ tailWord_729837).sum := by decide
  have hdescent : baseEnd_729837 < baseStart_729837 := by decide
  rcases family_descends (prefixWord ++ tailWord_729837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729840 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 3]
def baseStart_729840 : Nat := 118140960795 + 729840 * 2 ^ 59
def prefixEnd_729840 : Nat := 4983230072969 + 3 ^ 40 * 729840 * 2
def baseEnd_729840 : Nat := 374758720877529731343533

theorem tailTrace_729840 : CollatzResearch.WordTrace tailWord_729840 prefixEnd_729840 374758720877529731343533 := by
  unfold tailWord_729840
  simp only [CollatzResearch.WordTrace]
  refine ⟨13309725837960900796737487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17746301117281201062316649 13309725837960900796737487)
  ·
    refine ⟨19964588756941351195106231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13309725837960900796737487 19964588756941351195106231)
    ·
      refine ⟨29946883135412026792659347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19964588756941351195106231 29946883135412026792659347)
      ·
        refine ⟨44920324703118040188989021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29946883135412026792659347 44920324703118040188989021)
        ·
          refine ⟨16845121763669265070870883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44920324703118040188989021 16845121763669265070870883)
          ·
            refine ⟨25267682645503897606306325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16845121763669265070870883 25267682645503897606306325)
            ·
              refine ⟨1184422624007995200295609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25267682645503897606306325 1184422624007995200295609)
              ·
                refine ⟨888316968005996400221707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1184422624007995200295609 888316968005996400221707)
                ·
                  refine ⟨1332475452008994600332561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888316968005996400221707 1332475452008994600332561)
                  ·
                    refine ⟨999356589006745950249421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1332475452008994600332561 999356589006745950249421)
                    ·
                      refine ⟨374758720877529731343533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 999356589006745950249421 374758720877529731343533)
                      ·
                        rfl

theorem cell23_729840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 3].length) (baseStart_729840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729840 prefixEnd_729840 := by exact prefixLift 729840
  have htrace : WordTrace (prefixWord ++ tailWord_729840) baseStart_729840 baseEnd_729840 := by
    simpa [prefixWord, tailWord_729840, baseEnd_729840] using wordTrace_append hprefix tailTrace_729840
  have hstable : (prefixWord ++ tailWord_729840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729840).length < 2 ^ (prefixWord ++ tailWord_729840).sum := by decide
  have hdescent : baseEnd_729840 < baseStart_729840 := by decide
  rcases family_descends (prefixWord ++ tailWord_729840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729853 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_729853 : Nat := 118140960795 + 729853 * 2 ^ 59
def prefixEnd_729853 : Nat := 4983230072969 + 3 ^ 40 * 729853 * 2
def baseEnd_729853 : Nat := 374765396126038180480973

theorem tailTrace_729853 : CollatzResearch.WordTrace tailWord_729853 prefixEnd_729853 374765396126038180480973 := by
  unfold tailWord_729853
  simp only [CollatzResearch.WordTrace]
  refine ⟨26619925824874704813698213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17746617216583136542465475 26619925824874704813698213)
  ·
    refine ⟨4991236092164007152568415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26619925824874704813698213 4991236092164007152568415)
    ·
      refine ⟨7486854138246010728852623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4991236092164007152568415 7486854138246010728852623)
      ·
        refine ⟨11230281207369016093278935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7486854138246010728852623 11230281207369016093278935)
        ·
          refine ⟨16845421811053524139918403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11230281207369016093278935 16845421811053524139918403)
          ·
            refine ⟨25268132716580286209877605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16845421811053524139918403 25268132716580286209877605)
            ·
              refine ⟨4737774884358803664352051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25268132716580286209877605 4737774884358803664352051)
              ·
                refine ⟨7106662326538205496528077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737774884358803664352051 7106662326538205496528077)
                ·
                  refine ⟨2664998372451827061198029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7106662326538205496528077 2664998372451827061198029)
                  ·
                    refine ⟨999374389669435147949261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664998372451827061198029 999374389669435147949261)
                    ·
                      refine ⟨374765396126038180480973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 999374389669435147949261 374765396126038180480973)
                      ·
                        rfl

theorem cell23_729853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_729853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729853 prefixEnd_729853 := by exact prefixLift 729853
  have htrace : WordTrace (prefixWord ++ tailWord_729853) baseStart_729853 baseEnd_729853 := by
    simpa [prefixWord, tailWord_729853, baseEnd_729853] using wordTrace_append hprefix tailTrace_729853
  have hstable : (prefixWord ++ tailWord_729853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729853).length < 2 ^ (prefixWord ++ tailWord_729853).sum := by decide
  have hdescent : baseEnd_729853 < baseStart_729853 := by decide
  rcases family_descends (prefixWord ++ tailWord_729853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729880 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 3, 3, 2]
def baseStart_729880 : Nat := 118140960795 + 729880 * 2 ^ 59
def prefixEnd_729880 : Nat := 4983230072969 + 3 ^ 40 * 729880 * 2
def baseEnd_729880 : Nat := 374779260103709574843349

theorem tailTrace_729880 : CollatzResearch.WordTrace tailWord_729880 prefixEnd_729880 374779260103709574843349 := by
  unfold tailWord_729880
  simp only [CollatzResearch.WordTrace]
  refine ⟨13310455297888444212465547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17747273730517925616620729 13310455297888444212465547)
  ·
    refine ⟨19965682946832666318698321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13310455297888444212465547 19965682946832666318698321)
    ·
      refine ⟨14974262210124499739023741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19965682946832666318698321 14974262210124499739023741)
      ·
        refine ⟨5615348328796687402133903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14974262210124499739023741 5615348328796687402133903)
        ·
          refine ⟨8423022493195031103200855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615348328796687402133903 8423022493195031103200855)
          ·
            refine ⟨12634533739792546654801283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8423022493195031103200855 12634533739792546654801283)
            ·
              refine ⟨18951800609688819982201925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12634533739792546654801283 18951800609688819982201925)
              ·
                refine ⟨3553462614316653746662861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18951800609688819982201925 3553462614316653746662861)
                ·
                  refine ⟨1332548480368745154998573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3553462614316653746662861 1332548480368745154998573)
                  ·
                    refine ⟨499705680138279433124465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1332548480368745154998573 499705680138279433124465)
                    ·
                      refine ⟨374779260103709574843349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 499705680138279433124465 374779260103709574843349)
                      ·
                        rfl

theorem cell23_729880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_729880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729880 prefixEnd_729880 := by exact prefixLift 729880
  have htrace : WordTrace (prefixWord ++ tailWord_729880) baseStart_729880 baseEnd_729880 := by
    simpa [prefixWord, tailWord_729880, baseEnd_729880] using wordTrace_append hprefix tailTrace_729880
  have hstable : (prefixWord ++ tailWord_729880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729880).length < 2 ^ (prefixWord ++ tailWord_729880).sum := by decide
  have hdescent : baseEnd_729880 < baseStart_729880 := by decide
  rcases family_descends (prefixWord ++ tailWord_729880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729887 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 2, 1, 3]
def baseStart_729887 : Nat := 118140960795 + 729887 * 2 ^ 59
def prefixEnd_729887 : Nat := 4983230072969 + 3 ^ 40 * 729887 * 2
def baseEnd_729887 : Nat := 374782854468291047455817

theorem tailTrace_729887 : CollatzResearch.WordTrace tailWord_729887 prefixEnd_729887 374782854468291047455817 := by
  unfold tailWord_729887
  simp only [CollatzResearch.WordTrace]
  refine ⟨26621165906751528620435915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17747443937834352413623943 26621165906751528620435915)
  ·
    refine ⟨39931748860127292930653873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26621165906751528620435915 39931748860127292930653873)
    ·
      refine ⟨29948811645095469697990405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39931748860127292930653873 29948811645095469697990405)
      ·
        refine ⟨5615402183455400568373201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29948811645095469697990405 5615402183455400568373201)
        ·
          refine ⟨4211551637591550426279901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5615402183455400568373201 4211551637591550426279901)
          ·
            refine ⟨1579331864096831409854963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4211551637591550426279901 1579331864096831409854963)
            ·
              refine ⟨2368997796145247114782445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579331864096831409854963 2368997796145247114782445)
              ·
                refine ⟨888374173554467668043417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2368997796145247114782445 888374173554467668043417)
                ·
                  refine ⟨666280630165850751032563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 888374173554467668043417 666280630165850751032563)
                  ·
                    refine ⟨999420945248776126548845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 666280630165850751032563 999420945248776126548845)
                    ·
                      refine ⟨374782854468291047455817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 999420945248776126548845 374782854468291047455817)
                      ·
                        rfl

theorem cell23_729887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_729887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729887 prefixEnd_729887 := by exact prefixLift 729887
  have htrace : WordTrace (prefixWord ++ tailWord_729887) baseStart_729887 baseEnd_729887 := by
    simpa [prefixWord, tailWord_729887, baseEnd_729887] using wordTrace_append hprefix tailTrace_729887
  have hstable : (prefixWord ++ tailWord_729887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729887).length < 2 ^ (prefixWord ++ tailWord_729887).sum := by decide
  have hdescent : baseEnd_729887 < baseStart_729887 := by decide
  rcases family_descends (prefixWord ++ tailWord_729887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729921 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_729921 : Nat := 118140960795 + 729921 * 2 ^ 59
def prefixEnd_729921 : Nat := 4983230072969 + 3 ^ 40 * 729921 * 2
def baseEnd_729921 : Nat := 374800312810543914430661

theorem tailTrace_729921 : CollatzResearch.WordTrace tailWord_729921 prefixEnd_729921 374800312810543914430661 := by
  unfold tailWord_729921
  simp only [CollatzResearch.WordTrace]
  refine ⟨26622405988628352427173617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17748270659085568284782411 26622405988628352427173617)
  ·
    refine ⟨19966804491471264320380213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26622405988628352427173617 19966804491471264320380213)
    ·
      refine ⟨1871887921075431030035645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19966804491471264320380213 1871887921075431030035645)
      ·
        refine ⟨701957970403286636263367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1871887921075431030035645 701957970403286636263367)
        ·
          refine ⟨1052936955604929954395051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701957970403286636263367 1052936955604929954395051)
          ·
            refine ⟨1579405433407394931592577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052936955604929954395051 1579405433407394931592577)
            ·
              refine ⟨1184554075055546198694433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1579405433407394931592577 1184554075055546198694433)
              ·
                refine ⟨888415556291659649020825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1184554075055546198694433 888415556291659649020825)
                ·
                  refine ⟨666311667218744736765619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 888415556291659649020825 666311667218744736765619)
                  ·
                    refine ⟨999467500828117105148429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 666311667218744736765619 999467500828117105148429)
                    ·
                      refine ⟨374800312810543914430661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 999467500828117105148429 374800312810543914430661)
                      ·
                        rfl

theorem cell23_729921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_729921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729921 prefixEnd_729921 := by exact prefixLift 729921
  have htrace : WordTrace (prefixWord ++ tailWord_729921) baseStart_729921 baseEnd_729921 := by
    simpa [prefixWord, tailWord_729921, baseEnd_729921] using wordTrace_append hprefix tailTrace_729921
  have hstable : (prefixWord ++ tailWord_729921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729921).length < 2 ^ (prefixWord ++ tailWord_729921).sum := by decide
  have hdescent : baseEnd_729921 < baseStart_729921 := by decide
  rcases family_descends (prefixWord ++ tailWord_729921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729923 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 4]
def baseStart_729923 : Nat := 118140960795 + 729923 * 2 ^ 59
def prefixEnd_729923 : Nat := 4983230072969 + 3 ^ 40 * 729923 * 2
def baseEnd_729923 : Nat := 374801339771852906605651

theorem tailTrace_729923 : CollatzResearch.WordTrace tailWord_729923 prefixEnd_729923 374801339771852906605651 := by
  unfold tailWord_729923
  simp only [CollatzResearch.WordTrace]
  refine ⟨26622478934621106768746423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17748319289747404512497615 26622478934621106768746423)
  ·
    refine ⟨39933718401931660153119635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26622478934621106768746423 39933718401931660153119635)
    ·
      refine ⟨59900577602897490229679453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39933718401931660153119635 59900577602897490229679453)
      ·
        refine ⟨22462716601086558836129795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59900577602897490229679453 22462716601086558836129795)
        ·
          refine ⟨33694074901629838254194693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22462716601086558836129795 33694074901629838254194693)
          ·
            refine ⟨6317639044055594672661505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33694074901629838254194693 6317639044055594672661505)
            ·
              refine ⟨4738229283041696004496129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6317639044055594672661505 4738229283041696004496129)
              ·
                refine ⟨3553671962281272003372097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4738229283041696004496129 3553671962281272003372097)
                ·
                  refine ⟨2665253971710954002529073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3553671962281272003372097 2665253971710954002529073)
                  ·
                    refine ⟨1998940478783215501896805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2665253971710954002529073 1998940478783215501896805)
                    ·
                      refine ⟨374801339771852906605651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1998940478783215501896805 374801339771852906605651)
                      ·
                        rfl

theorem cell23_729923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_729923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_729923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_729923 prefixEnd_729923 := by exact prefixLift 729923
  have htrace : WordTrace (prefixWord ++ tailWord_729923) baseStart_729923 baseEnd_729923 := by
    simpa [prefixWord, tailWord_729923, baseEnd_729923] using wordTrace_append hprefix tailTrace_729923
  have hstable : (prefixWord ++ tailWord_729923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729923).length < 2 ^ (prefixWord ++ tailWord_729923).sum := by decide
  have hdescent : baseEnd_729923 < baseStart_729923 := by decide
  rcases family_descends (prefixWord ++ tailWord_729923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730000 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 6, 4, 2]
def baseStart_730000 : Nat := 118140960795 + 730000 * 2 ^ 59
def prefixEnd_730000 : Nat := 4983230072969 + 3 ^ 40 * 730000 * 2
def baseEnd_730000 : Nat := 374840877782249105342797

theorem tailTrace_730000 : CollatzResearch.WordTrace tailWord_730000 prefixEnd_730000 374840877782249105342797 := by
  unfold tailWord_730000
  simp only [CollatzResearch.WordTrace]
  refine ⟨13312643677671074459649727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17750191570228099279532969 13312643677671074459649727)
  ·
    refine ⟨19968965516506611689474591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13312643677671074459649727 19968965516506611689474591)
    ·
      refine ⟨29953448274759917534211887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19968965516506611689474591 29953448274759917534211887)
      ·
        refine ⟨44930172412139876301317831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29953448274759917534211887 44930172412139876301317831)
        ·
          refine ⟨67395258618209814451976747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44930172412139876301317831 67395258618209814451976747)
          ·
            refine ⟨101092887927314721677965121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67395258618209814451976747 101092887927314721677965121)
            ·
              refine ⟨75819665945486041258473841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101092887927314721677965121 75819665945486041258473841)
              ·
                refine ⟨56864749459114530943855381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75819665945486041258473841 56864749459114530943855381)
                ·
                  refine ⟨2665535130895993637993221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56864749459114530943855381 2665535130895993637993221)
                  ·
                    refine ⟨499787837042998807123729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665535130895993637993221 499787837042998807123729)
                    ·
                      refine ⟨374840877782249105342797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 499787837042998807123729 374840877782249105342797)
                      ·
                        rfl

theorem cell23_730000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 4, 2].length) (baseStart_730000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730000 prefixEnd_730000 := by exact prefixLift 730000
  have htrace : WordTrace (prefixWord ++ tailWord_730000) baseStart_730000 baseEnd_730000 := by
    simpa [prefixWord, tailWord_730000, baseEnd_730000] using wordTrace_append hprefix tailTrace_730000
  have hstable : (prefixWord ++ tailWord_730000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730000).length < 2 ^ (prefixWord ++ tailWord_730000).sum := by decide
  have hdescent : baseEnd_730000 < baseStart_730000 := by decide
  rcases family_descends (prefixWord ++ tailWord_730000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730020 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_730020 : Nat := 118140960795 + 730020 * 2 ^ 59
def prefixEnd_730020 : Nat := 4983230072969 + 3 ^ 40 * 730020 * 2
def baseEnd_730020 : Nat := 374851147395339027092705

theorem tailTrace_730020 : CollatzResearch.WordTrace tailWord_730020 prefixEnd_730020 374851147395339027092705 := by
  unfold tailWord_730020
  simp only [CollatzResearch.WordTrace]
  refine ⟨13313008407634846167513757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17750677876846461556685009 13313008407634846167513757)
  ·
    refine ⟨4992378152863067312817659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13313008407634846167513757 4992378152863067312817659)
    ·
      refine ⟨7488567229294600969226489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4992378152863067312817659 7488567229294600969226489)
      ·
        refine ⟨5616425421970950726919867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7488567229294600969226489 5616425421970950726919867)
        ·
          refine ⟨8424638132956426090379801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5616425421970950726919867 8424638132956426090379801)
          ·
            refine ⟨6318478599717319567784851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8424638132956426090379801 6318478599717319567784851)
            ·
              refine ⟨9477717899575979351677277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6318478599717319567784851 9477717899575979351677277)
              ·
                refine ⟨3554144212340992256878979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9477717899575979351677277 3554144212340992256878979)
                ·
                  refine ⟨5331216318511488385318469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554144212340992256878979 5331216318511488385318469)
                  ·
                    refine ⟨999603059720904072247213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5331216318511488385318469 999603059720904072247213)
                    ·
                      refine ⟨374851147395339027092705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 999603059720904072247213 374851147395339027092705)
                      ·
                        rfl

theorem cell23_730020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_730020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730020 prefixEnd_730020 := by exact prefixLift 730020
  have htrace : WordTrace (prefixWord ++ tailWord_730020) baseStart_730020 baseEnd_730020 := by
    simpa [prefixWord, tailWord_730020, baseEnd_730020] using wordTrace_append hprefix tailTrace_730020
  have hstable : (prefixWord ++ tailWord_730020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730020).length < 2 ^ (prefixWord ++ tailWord_730020).sum := by decide
  have hdescent : baseEnd_730020 < baseStart_730020 := by decide
  rcases family_descends (prefixWord ++ tailWord_730020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730037 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_730037 : Nat := 118140960795 + 730037 * 2 ^ 59
def prefixEnd_730037 : Nat := 4983230072969 + 3 ^ 40 * 730037 * 2
def baseEnd_730037 : Nat := 374859876566465460580127

theorem tailTrace_730037 : CollatzResearch.WordTrace tailWord_730037 prefixEnd_730037 374859876566465460580127 := by
  unfold tailWord_730037
  simp only [CollatzResearch.WordTrace]
  refine ⟨26626636856208104238396365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17751091237472069492264243 26626636856208104238396365)
  ·
    refine ⟨9984988821078039089398637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26626636856208104238396365 9984988821078039089398637)
    ·
      refine ⟨3744370807904264658524489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9984988821078039089398637 3744370807904264658524489)
      ·
        refine ⟨2808278105928198493893367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3744370807904264658524489 2808278105928198493893367)
        ·
          refine ⟨4212417158892297740840051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2808278105928198493893367 4212417158892297740840051)
          ·
            refine ⟨6318625738338446611260077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4212417158892297740840051 6318625738338446611260077)
            ·
              refine ⟨2369484651876917479222529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6318625738338446611260077 2369484651876917479222529)
              ·
                refine ⟨1777113488907688109416897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2369484651876917479222529 1777113488907688109416897)
                ·
                  refine ⟨1332835116680766082062673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1777113488907688109416897 1332835116680766082062673)
                  ·
                    refine ⟨999626337510574561547005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1332835116680766082062673 999626337510574561547005)
                    ·
                      refine ⟨374859876566465460580127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 999626337510574561547005 374859876566465460580127)
                      ·
                        rfl

theorem cell23_730037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_730037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730037 prefixEnd_730037 := by exact prefixLift 730037
  have htrace : WordTrace (prefixWord ++ tailWord_730037) baseStart_730037 baseEnd_730037 := by
    simpa [prefixWord, tailWord_730037, baseEnd_730037] using wordTrace_append hprefix tailTrace_730037
  have hstable : (prefixWord ++ tailWord_730037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730037).length < 2 ^ (prefixWord ++ tailWord_730037).sum := by decide
  have hdescent : baseEnd_730037 < baseStart_730037 := by decide
  rcases family_descends (prefixWord ++ tailWord_730037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730117 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 2, 4]
def baseStart_730117 : Nat := 118140960795 + 730117 * 2 ^ 59
def prefixEnd_730117 : Nat := 4983230072969 + 3 ^ 40 * 730117 * 2
def baseEnd_730117 : Nat := 124966985006275049193253

theorem tailTrace_730117 : CollatzResearch.WordTrace tailWord_730117 prefixEnd_730117 124966985006275049193253 := by
  unfold tailWord_730117
  simp only [CollatzResearch.WordTrace]
  refine ⟨26629554695918277901308605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17753036463945518600872403 26629554695918277901308605)
  ·
    refine ⟨9986083010969354212990727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26629554695918277901308605 9986083010969354212990727)
    ·
      refine ⟨14979124516454031319486091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9986083010969354212990727 14979124516454031319486091)
      ·
        refine ⟨22468686774681046979229137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14979124516454031319486091 22468686774681046979229137)
        ·
          refine ⟨16851515081010785234421853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22468686774681046979229137 16851515081010785234421853)
          ·
            refine ⟨6319318155379044462908195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16851515081010785234421853 6319318155379044462908195)
            ·
              refine ⟨9478977233068566694362293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6319318155379044462908195 9478977233068566694362293)
              ·
                refine ⟨888654115600178127596465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9478977233068566694362293 888654115600178127596465)
                ·
                  refine ⟨666490586700133595697349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 888654115600178127596465 666490586700133595697349)
                  ·
                    refine ⟨124966985006275049193253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 666490586700133595697349 124966985006275049193253)
                    ·
                      rfl

theorem cell23_730117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_730117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730117 prefixEnd_730117 := by exact prefixLift 730117
  have htrace : WordTrace (prefixWord ++ tailWord_730117) baseStart_730117 baseEnd_730117 := by
    simpa [prefixWord, tailWord_730117, baseEnd_730117] using wordTrace_append hprefix tailTrace_730117
  have hstable : (prefixWord ++ tailWord_730117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730117).length < 2 ^ (prefixWord ++ tailWord_730117).sum := by decide
  have hdescent : baseEnd_730117 < baseStart_730117 := by decide
  rcases family_descends (prefixWord ++ tailWord_730117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730124 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 5, 2, 2]
def baseStart_730124 : Nat := 118140960795 + 730124 * 2 ^ 59
def prefixEnd_730124 : Nat := 4983230072969 + 3 ^ 40 * 730124 * 2
def baseEnd_730124 : Nat := 374904549383406620192227

theorem tailTrace_730124 : CollatzResearch.WordTrace tailWord_730124 prefixEnd_730124 374904549383406620192227 := by
  unfold tailWord_730124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13314905003446459048406713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17753206671261945397875617 13314905003446459048406713)
  ·
    refine ⟨9986178752584844286305035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13314905003446459048406713 9986178752584844286305035)
    ·
      refine ⟨14979268128877266429457553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9986178752584844286305035 14979268128877266429457553)
      ·
        refine ⟨11234451096657949822093165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14979268128877266429457553 11234451096657949822093165)
        ·
          refine ⟨4212919161246731183284937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11234451096657949822093165 4212919161246731183284937)
          ·
            refine ⟨3159689370935048387463703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4212919161246731183284937 3159689370935048387463703)
            ·
              refine ⟨4739534056402572581195555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159689370935048387463703 4739534056402572581195555)
              ·
                refine ⟨7109301084603858871793333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739534056402572581195555 7109301084603858871793333)
                ·
                  refine ⟨666496976681611769230625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7109301084603858871793333 666496976681611769230625)
                  ·
                    refine ⟨499872732511208826922969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 666496976681611769230625 499872732511208826922969)
                    ·
                      refine ⟨374904549383406620192227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 499872732511208826922969 374904549383406620192227)
                      ·
                        rfl

theorem cell23_730124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_730124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730124 prefixEnd_730124 := by exact prefixLift 730124
  have htrace : WordTrace (prefixWord ++ tailWord_730124) baseStart_730124 baseEnd_730124 := by
    simpa [prefixWord, tailWord_730124, baseEnd_730124] using wordTrace_append hprefix tailTrace_730124
  have hstable : (prefixWord ++ tailWord_730124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730124).length < 2 ^ (prefixWord ++ tailWord_730124).sum := by decide
  have hdescent : baseEnd_730124 < baseStart_730124 := by decide
  rcases family_descends (prefixWord ++ tailWord_730124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730151 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 2, 4]
def baseStart_730151 : Nat := 118140960795 + 730151 * 2 ^ 59
def prefixEnd_730151 : Nat := 4983230072969 + 3 ^ 40 * 730151 * 2
def baseEnd_730151 : Nat := 124972804453692671518201

theorem tailTrace_730151 : CollatzResearch.WordTrace tailWord_730151 prefixEnd_730151 124972804453692671518201 := by
  unfold tailWord_730151
  simp only [CollatzResearch.WordTrace]
  refine ⟨26630794777795101708046307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17753863185196734472030871 26630794777795101708046307)
  ·
    refine ⟨39946192166692652562069461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26630794777795101708046307 39946192166692652562069461)
    ·
      refine ⟨936238878906859044423503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 39946192166692652562069461 936238878906859044423503)
      ·
        refine ⟨1404358318360288566635255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936238878906859044423503 1404358318360288566635255)
        ·
          refine ⟨2106537477540432849952883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404358318360288566635255 2106537477540432849952883)
          ·
            refine ⟨3159806216310649274929325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106537477540432849952883 3159806216310649274929325)
            ·
              refine ⟨1184927331116493478098497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3159806216310649274929325 1184927331116493478098497)
              ·
                refine ⟨888695498337370108573873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1184927331116493478098497 888695498337370108573873)
                ·
                  refine ⟨666521623753027581430405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 888695498337370108573873 666521623753027581430405)
                  ·
                    refine ⟨124972804453692671518201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 666521623753027581430405 124972804453692671518201)
                    ·
                      rfl

theorem cell23_730151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_730151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730151 prefixEnd_730151 := by exact prefixLift 730151
  have htrace : WordTrace (prefixWord ++ tailWord_730151) baseStart_730151 baseEnd_730151 := by
    simpa [prefixWord, tailWord_730151, baseEnd_730151] using wordTrace_append hprefix tailTrace_730151
  have hstable : (prefixWord ++ tailWord_730151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730151).length < 2 ^ (prefixWord ++ tailWord_730151).sum := by decide
  have hdescent : baseEnd_730151 < baseStart_730151 := by decide
  rcases family_descends (prefixWord ++ tailWord_730151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730158 : List Nat := [4, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_730158 : Nat := 118140960795 + 730158 * 2 ^ 59
def prefixEnd_730158 : Nat := 4983230072969 + 3 ^ 40 * 730158 * 2
def baseEnd_730158 : Nat := 374922007725659487167071

theorem tailTrace_730158 : CollatzResearch.WordTrace tailWord_730158 prefixEnd_730158 374922007725659487167071 := by
  unfold tailWord_730158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3328881261096217737943891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17754033392513161269034085 3328881261096217737943891)
  ·
    refine ⟨4993321891644326606915837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3328881261096217737943891 4993321891644326606915837)
    ·
      refine ⟨1872495709366622477593439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4993321891644326606915837 1872495709366622477593439)
      ·
        refine ⟨2808743564049933716390159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872495709366622477593439 2808743564049933716390159)
        ·
          refine ⟨4213115346074900574585239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2808743564049933716390159 4213115346074900574585239)
          ·
            refine ⟨6319673019112350861877859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213115346074900574585239 6319673019112350861877859)
            ·
              refine ⟨9479509528668526292816789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6319673019112350861877859 9479509528668526292816789)
              ·
                refine ⟨444352009156337169975787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9479509528668526292816789 444352009156337169975787)
                ·
                  refine ⟨666528013734505754963681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444352009156337169975787 666528013734505754963681)
                  ·
                    refine ⟨499896010300879316222761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 666528013734505754963681 499896010300879316222761)
                    ·
                      refine ⟨374922007725659487167071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 499896010300879316222761 374922007725659487167071)
                      ·
                        rfl

theorem cell23_730158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_730158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730158 prefixEnd_730158 := by exact prefixLift 730158
  have htrace : WordTrace (prefixWord ++ tailWord_730158) baseStart_730158 baseEnd_730158 := by
    simpa [prefixWord, tailWord_730158, baseEnd_730158] using wordTrace_append hprefix tailTrace_730158
  have hstable : (prefixWord ++ tailWord_730158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730158).length < 2 ^ (prefixWord ++ tailWord_730158).sum := by decide
  have hdescent : baseEnd_730158 < baseStart_730158 := by decide
  rcases family_descends (prefixWord ++ tailWord_730158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730231 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 2, 2, 2]
def baseStart_730231 : Nat := 118140960795 + 730231 * 2 ^ 59
def prefixEnd_730231 : Nat := 4983230072969 + 3 ^ 40 * 730231 * 2
def baseEnd_730231 : Nat := 374959491813437701554235

theorem tailTrace_730231 : CollatzResearch.WordTrace tailWord_730231 prefixEnd_730231 374959491813437701554235 := by
  unfold tailWord_730231
  simp only [CollatzResearch.WordTrace]
  refine ⟨26633712617505275370958547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17755808411670183580639031 26633712617505275370958547)
  ·
    refine ⟨39950568926257913056437821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26633712617505275370958547 39950568926257913056437821)
    ·
      refine ⟨14981463347346717396164183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39950568926257913056437821 14981463347346717396164183)
      ·
        refine ⟨22472195021020076094246275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14981463347346717396164183 22472195021020076094246275)
        ·
          refine ⟨33708292531530114141369413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22472195021020076094246275 33708292531530114141369413)
          ·
            refine ⟨6320304849661896401506765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33708292531530114141369413 6320304849661896401506765)
            ·
              refine ⟨2370114318623211150565037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6320304849661896401506765 2370114318623211150565037)
              ·
                refine ⟨888792869483704181461889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2370114318623211150565037 888792869483704181461889)
                ·
                  refine ⟨666594652112778136096417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 888792869483704181461889 666594652112778136096417)
                  ·
                    refine ⟨499945989084583602072313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 666594652112778136096417 499945989084583602072313)
                    ·
                      refine ⟨374959491813437701554235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 499945989084583602072313 374959491813437701554235)
                      ·
                        rfl

theorem cell23_730231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 2, 2].length) (baseStart_730231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730231 prefixEnd_730231 := by exact prefixLift 730231
  have htrace : WordTrace (prefixWord ++ tailWord_730231) baseStart_730231 baseEnd_730231 := by
    simpa [prefixWord, tailWord_730231, baseEnd_730231] using wordTrace_append hprefix tailTrace_730231
  have hstable : (prefixWord ++ tailWord_730231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730231).length < 2 ^ (prefixWord ++ tailWord_730231).sum := by decide
  have hdescent : baseEnd_730231 < baseStart_730231 := by decide
  rcases family_descends (prefixWord ++ tailWord_730231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730247 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_730247 : Nat := 118140960795 + 730247 * 2 ^ 59
def prefixEnd_730247 : Nat := 4983230072969 + 3 ^ 40 * 730247 * 2
def baseEnd_730247 : Nat := 374967707503909638954161

theorem tailTrace_730247 : CollatzResearch.WordTrace tailWord_730247 prefixEnd_730247 374967707503909638954161 := by
  unfold tailWord_730247
  simp only [CollatzResearch.WordTrace]
  refine ⟨26634296185447310103540995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17756197456964873402360663 26634296185447310103540995)
  ·
    refine ⟨39951444278170965155311493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26634296185447310103540995 39951444278170965155311493)
    ·
      refine ⟨7490895802157055966620905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39951444278170965155311493 7490895802157055966620905)
      ·
        refine ⟨5618171851617791974965679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7490895802157055966620905 5618171851617791974965679)
        ·
          refine ⟨8427257777426687962448519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5618171851617791974965679 8427257777426687962448519)
          ·
            refine ⟨12640886666140031943672779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8427257777426687962448519 12640886666140031943672779)
            ·
              refine ⟨18961329999210047915509169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12640886666140031943672779 18961329999210047915509169)
              ·
                refine ⟨14220997499407535936631877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18961329999210047915509169 14220997499407535936631877)
                ·
                  refine ⟨2666437031138912988118477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14220997499407535936631877 2666437031138912988118477)
                  ·
                    refine ⟨999913886677092370544429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666437031138912988118477 999913886677092370544429)
                    ·
                      refine ⟨374967707503909638954161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 999913886677092370544429 374967707503909638954161)
                      ·
                        rfl

theorem cell23_730247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_730247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730247 prefixEnd_730247 := by exact prefixLift 730247
  have htrace : WordTrace (prefixWord ++ tailWord_730247) baseStart_730247 baseEnd_730247 := by
    simpa [prefixWord, tailWord_730247, baseEnd_730247] using wordTrace_append hprefix tailTrace_730247
  have hstable : (prefixWord ++ tailWord_730247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730247).length < 2 ^ (prefixWord ++ tailWord_730247).sum := by decide
  have hdescent : baseEnd_730247 < baseStart_730247 := by decide
  rcases family_descends (prefixWord ++ tailWord_730247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730271 : List Nat := [1, 1, 2, 6, 2, 1, 1, 4, 5]
def baseStart_730271 : Nat := 118140960795 + 730271 * 2 ^ 59
def prefixEnd_730271 : Nat := 4983230072969 + 3 ^ 40 * 730271 * 2
def baseEnd_730271 : Nat := 41664447893290838339339

theorem tailTrace_730271 : CollatzResearch.WordTrace tailWord_730271 prefixEnd_730271 41664447893290838339339 := by
  unfold tailWord_730271
  simp only [CollatzResearch.WordTrace]
  refine ⟨26635171537360362202414667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17756781024906908134943111 26635171537360362202414667)
  ·
    refine ⟨39952757306040543303622001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26635171537360362202414667 39952757306040543303622001)
    ·
      refine ⟨29964567979530407477716501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39952757306040543303622001 29964567979530407477716501)
      ·
        refine ⟨1404589124040487850517961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29964567979530407477716501 1404589124040487850517961)
        ·
          refine ⟨1053441843030365887888471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1404589124040487850517961 1053441843030365887888471)
          ·
            refine ⟨1580162764545548831832707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053441843030365887888471 1580162764545548831832707)
            ·
              refine ⟨2370244146818323247749061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580162764545548831832707 2370244146818323247749061)
              ·
                refine ⟨444420777528435608952949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2370244146818323247749061 444420777528435608952949)
                ·
                  refine ⟨41664447893290838339339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 444420777528435608952949 41664447893290838339339)
                  ·
                    rfl

theorem cell23_730271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 5].length) (baseStart_730271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730271 prefixEnd_730271 := by exact prefixLift 730271
  have htrace : WordTrace (prefixWord ++ tailWord_730271) baseStart_730271 baseEnd_730271 := by
    simpa [prefixWord, tailWord_730271, baseEnd_730271] using wordTrace_append hprefix tailTrace_730271
  have hstable : (prefixWord ++ tailWord_730271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730271).length < 2 ^ (prefixWord ++ tailWord_730271).sum := by decide
  have hdescent : baseEnd_730271 < baseStart_730271 := by decide
  rcases family_descends (prefixWord ++ tailWord_730271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730277 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_730277 : Nat := 118140960795 + 730277 * 2 ^ 59
def prefixEnd_730277 : Nat := 4983230072969 + 3 ^ 40 * 730277 * 2
def baseEnd_730277 : Nat := 374983111923544521579023

theorem tailTrace_730277 : CollatzResearch.WordTrace tailWord_730277 prefixEnd_730277 374983111923544521579023 := by
  unfold tailWord_730277
  simp only [CollatzResearch.WordTrace]
  refine ⟨26635390375338625227133085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17756926916892416818088723 26635390375338625227133085)
  ·
    refine ⟨9988271390751984460174907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26635390375338625227133085 9988271390751984460174907)
    ·
      refine ⟨14982407086127976690262361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9988271390751984460174907 14982407086127976690262361)
      ·
        refine ⟨11236805314595982517696771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14982407086127976690262361 11236805314595982517696771)
        ·
          refine ⟨16855207971893973776545157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11236805314595982517696771 16855207971893973776545157)
          ·
            refine ⟨3160351494730120083102217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16855207971893973776545157 3160351494730120083102217)
            ·
              refine ⟨2370263621047590062326663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160351494730120083102217 2370263621047590062326663)
              ·
                refine ⟨3555395431571385093489995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370263621047590062326663 3555395431571385093489995)
                ·
                  refine ⟨5333093147357077640234993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555395431571385093489995 5333093147357077640234993)
                  ·
                    refine ⟨3999819860517808230176245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5333093147357077640234993 3999819860517808230176245)
                    ·
                      refine ⟨374983111923544521579023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3999819860517808230176245 374983111923544521579023)
                      ·
                        rfl

theorem cell23_730277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_730277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730277 prefixEnd_730277 := by exact prefixLift 730277
  have htrace : WordTrace (prefixWord ++ tailWord_730277) baseStart_730277 baseEnd_730277 := by
    simpa [prefixWord, tailWord_730277, baseEnd_730277] using wordTrace_append hprefix tailTrace_730277
  have hstable : (prefixWord ++ tailWord_730277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730277).length < 2 ^ (prefixWord ++ tailWord_730277).sum := by decide
  have hdescent : baseEnd_730277 < baseStart_730277 := by decide
  rcases family_descends (prefixWord ++ tailWord_730277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730287 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 4]
def baseStart_730287 : Nat := 118140960795 + 730287 * 2 ^ 59
def prefixEnd_730287 : Nat := 4983230072969 + 3 ^ 40 * 730287 * 2
def baseEnd_730287 : Nat := 374988246730089482453977

theorem tailTrace_730287 : CollatzResearch.WordTrace tailWord_730287 prefixEnd_730287 374988246730089482453977 := by
  unfold tailWord_730287
  simp only [CollatzResearch.WordTrace]
  refine ⟨26635755105302396934997115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17757170070201597956664743 26635755105302396934997115)
  ·
    refine ⟨39953632657953595402495673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26635755105302396934997115 39953632657953595402495673)
    ·
      refine ⟨29965224493465196551871755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39953632657953595402495673 29965224493465196551871755)
      ·
        refine ⟨44947836740197794827807633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29965224493465196551871755 44947836740197794827807633)
        ·
          refine ⟨33710877555148346120855725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44947836740197794827807633 33710877555148346120855725)
          ·
            refine ⟨12641579083180629795320897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33710877555148346120855725 12641579083180629795320897)
            ·
              refine ⟨9481184312385472346490673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12641579083180629795320897 9481184312385472346490673)
              ·
                refine ⟨7110888234289104259868005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9481184312385472346490673 7110888234289104259868005)
                ·
                  refine ⟨1333291543929207048725251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7110888234289104259868005 1333291543929207048725251)
                  ·
                    refine ⟨1999937315893810573087877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1333291543929207048725251 1999937315893810573087877)
                    ·
                      refine ⟨374988246730089482453977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1999937315893810573087877 374988246730089482453977)
                      ·
                        rfl

theorem cell23_730287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_730287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730287 prefixEnd_730287 := by exact prefixLift 730287
  have htrace : WordTrace (prefixWord ++ tailWord_730287) baseStart_730287 baseEnd_730287 := by
    simpa [prefixWord, tailWord_730287, baseEnd_730287] using wordTrace_append hprefix tailTrace_730287
  have hstable : (prefixWord ++ tailWord_730287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730287).length < 2 ^ (prefixWord ++ tailWord_730287).sum := by decide
  have hdescent : baseEnd_730287 < baseStart_730287 := by decide
  rcases family_descends (prefixWord ++ tailWord_730287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730304 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 4]
def baseStart_730304 : Nat := 118140960795 + 730304 * 2 ^ 59
def prefixEnd_730304 : Nat := 4983230072969 + 3 ^ 40 * 730304 * 2
def baseEnd_730304 : Nat := 374996975901215915941399

theorem tailTrace_730304 : CollatzResearch.WordTrace tailWord_730304 prefixEnd_730304 374996975901215915941399 := by
  unfold tailWord_730304
  simp only [CollatzResearch.WordTrace]
  refine ⟨13318187573120404419182983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17757583430827205892243977 13318187573120404419182983)
  ·
    refine ⟨19977281359680606628774475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13318187573120404419182983 19977281359680606628774475)
    ·
      refine ⟨29965922039520909943161713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19977281359680606628774475 29965922039520909943161713)
      ·
        refine ⟨22474441529640682457371285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29965922039520909943161713 22474441529640682457371285)
        ·
          refine ⟨1053489446701906990189279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22474441529640682457371285 1053489446701906990189279)
          ·
            refine ⟨1580234170052860485283919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053489446701906990189279 1580234170052860485283919)
            ·
              refine ⟨2370351255079290727925879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580234170052860485283919 2370351255079290727925879)
              ·
                refine ⟨3555526882618936091888819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370351255079290727925879 3555526882618936091888819)
                ·
                  refine ⟨5333290323928404137833229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555526882618936091888819 5333290323928404137833229)
                  ·
                    refine ⟨1999983871473151551687461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5333290323928404137833229 1999983871473151551687461)
                    ·
                      refine ⟨374996975901215915941399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1999983871473151551687461 374996975901215915941399)
                      ·
                        rfl

theorem cell23_730304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_730304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730304 prefixEnd_730304 := by exact prefixLift 730304
  have htrace : WordTrace (prefixWord ++ tailWord_730304) baseStart_730304 baseEnd_730304 := by
    simpa [prefixWord, tailWord_730304, baseEnd_730304] using wordTrace_append hprefix tailTrace_730304
  have hstable : (prefixWord ++ tailWord_730304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730304).length < 2 ^ (prefixWord ++ tailWord_730304).sum := by decide
  have hdescent : baseEnd_730304 < baseStart_730304 := by decide
  rcases family_descends (prefixWord ++ tailWord_730304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730404 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_730404 : Nat := 118140960795 + 730404 * 2 ^ 59
def prefixEnd_730404 : Nat := 4983230072969 + 3 ^ 40 * 730404 * 2
def baseEnd_730404 : Nat := 125016107988888508230313

theorem tailTrace_730404 : CollatzResearch.WordTrace tailWord_730404 prefixEnd_730404 125016107988888508230313 := by
  unfold tailWord_730404
  simp only [CollatzResearch.WordTrace]
  refine ⟨13320011222939262958503133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17760014963919017278004177 13320011222939262958503133)
  ·
    refine ⟨4995004208602223609438675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13320011222939262958503133 4995004208602223609438675)
    ·
      refine ⟨7492506312903335414158013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4995004208602223609438675 7492506312903335414158013)
      ·
        refine ⟨2809689867338750780309255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7492506312903335414158013 2809689867338750780309255)
        ·
          refine ⟨4214534801008126170463883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809689867338750780309255 4214534801008126170463883)
          ·
            refine ⟨6321802201512189255695825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214534801008126170463883 6321802201512189255695825)
            ·
              refine ⟨4741351651134141941771869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6321802201512189255695825 4741351651134141941771869)
              ·
                refine ⟨1778006869175303228164451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4741351651134141941771869 1778006869175303228164451)
                ·
                  refine ⟨2667010303762954842246677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778006869175303228164451 2667010303762954842246677)
                  ·
                    refine ⟨125016107988888508230313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2667010303762954842246677 125016107988888508230313)
                    ·
                      rfl

theorem cell23_730404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_730404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730404 prefixEnd_730404 := by exact prefixLift 730404
  have htrace : WordTrace (prefixWord ++ tailWord_730404) baseStart_730404 baseEnd_730404 := by
    simpa [prefixWord, tailWord_730404, baseEnd_730404] using wordTrace_append hprefix tailTrace_730404
  have hstable : (prefixWord ++ tailWord_730404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730404).length < 2 ^ (prefixWord ++ tailWord_730404).sum := by decide
  have hdescent : baseEnd_730404 < baseStart_730404 := by decide
  rcases family_descends (prefixWord ++ tailWord_730404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730408 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 1, 5]
def baseStart_730408 : Nat := 118140960795 + 730408 * 2 ^ 59
def prefixEnd_730408 : Nat := 4983230072969 + 3 ^ 40 * 730408 * 2
def baseEnd_730408 : Nat := 125016792629761169680307

theorem tailTrace_730408 : CollatzResearch.WordTrace tailWord_730408 prefixEnd_730408 125016792629761169680307 := by
  unfold tailWord_730408
  simp only [CollatzResearch.WordTrace]
  refine ⟨13320084168932017300075939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17760112225242689733434585 13320084168932017300075939)
  ·
    refine ⟨19980126253398025950113909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13320084168932017300075939 19980126253398025950113909)
    ·
      refine ⟨1873136836256064932823179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19980126253398025950113909 1873136836256064932823179)
      ·
        refine ⟨2809705254384097399234769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1873136836256064932823179 2809705254384097399234769)
        ·
          refine ⟨2107278940788073049426077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2809705254384097399234769 2107278940788073049426077)
          ·
            refine ⟨790229602795527393534779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2107278940788073049426077 790229602795527393534779)
            ·
              refine ⟨1185344404193291090302169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790229602795527393534779 1185344404193291090302169)
              ·
                refine ⟨889008303144968317726627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185344404193291090302169 889008303144968317726627)
                ·
                  refine ⟨1333512454717452476589941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889008303144968317726627 1333512454717452476589941)
                  ·
                    refine ⟨125016792629761169680307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1333512454717452476589941 125016792629761169680307)
                    ·
                      rfl

theorem cell23_730408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_730408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730408 prefixEnd_730408 := by exact prefixLift 730408
  have htrace : WordTrace (prefixWord ++ tailWord_730408) baseStart_730408 baseEnd_730408 := by
    simpa [prefixWord, tailWord_730408, baseEnd_730408] using wordTrace_append hprefix tailTrace_730408
  have hstable : (prefixWord ++ tailWord_730408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730408).length < 2 ^ (prefixWord ++ tailWord_730408).sum := by decide
  have hdescent : baseEnd_730408 < baseStart_730408 := by decide
  rcases family_descends (prefixWord ++ tailWord_730408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730428 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 1, 1, 4]
def baseStart_730428 : Nat := 118140960795 + 730428 * 2 ^ 59
def prefixEnd_730428 : Nat := 4983230072969 + 3 ^ 40 * 730428 * 2
def baseEnd_730428 : Nat := 375060647502373430790829

theorem tailTrace_730428 : CollatzResearch.WordTrace tailWord_730428 prefixEnd_730428 375060647502373430790829 := by
  unfold tailWord_730428
  simp only [CollatzResearch.WordTrace]
  refine ⟨13320448898895789007939969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17760598531861052010586625 13320448898895789007939969)
  ·
    refine ⟨9990336674171841755954977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13320448898895789007939969 9990336674171841755954977)
    ·
      refine ⟨7492752505628881316966233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9990336674171841755954977 7492752505628881316966233)
      ·
        refine ⟨5619564379221660987724675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7492752505628881316966233 5619564379221660987724675)
        ·
          refine ⟨8429346568832491481587013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5619564379221660987724675 8429346568832491481587013)
          ·
            refine ⟨1580502481656092152797565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8429346568832491481587013 1580502481656092152797565)
            ·
              refine ⟨592688430621034557299087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1580502481656092152797565 592688430621034557299087)
              ·
                refine ⟨889032645931551835948631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592688430621034557299087 889032645931551835948631)
                ·
                  refine ⟨1333548968897327753922947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889032645931551835948631 1333548968897327753922947)
                  ·
                    refine ⟨2000323453345991630884421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1333548968897327753922947 2000323453345991630884421)
                    ·
                      refine ⟨375060647502373430790829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2000323453345991630884421 375060647502373430790829)
                      ·
                        rfl

theorem cell23_730428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_730428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730428 prefixEnd_730428 := by exact prefixLift 730428
  have htrace : WordTrace (prefixWord ++ tailWord_730428) baseStart_730428 baseEnd_730428 := by
    simpa [prefixWord, tailWord_730428, baseEnd_730428] using wordTrace_append hprefix tailTrace_730428
  have hstable : (prefixWord ++ tailWord_730428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730428).length < 2 ^ (prefixWord ++ tailWord_730428).sum := by decide
  have hdescent : baseEnd_730428 < baseStart_730428 := by decide
  rcases family_descends (prefixWord ++ tailWord_730428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730431 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 5]
def baseStart_730431 : Nat := 118140960795 + 730431 * 2 ^ 59
def prefixEnd_730431 : Nat := 4983230072969 + 3 ^ 40 * 730431 * 2
def baseEnd_730431 : Nat := 375062187944336919053315

theorem tailTrace_730431 : CollatzResearch.WordTrace tailWord_730431 prefixEnd_730431 375062187944336919053315 := by
  unfold tailWord_730431
  simp only [CollatzResearch.WordTrace]
  refine ⟨26641007216780709528239147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17760671477853806352159431 26641007216780709528239147)
  ·
    refine ⟨39961510825171064292358721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26641007216780709528239147 39961510825171064292358721)
    ·
      refine ⟨29971133118878298219269041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39961510825171064292358721 29971133118878298219269041)
      ·
        refine ⟨22478349839158723664451781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29971133118878298219269041 22478349839158723664451781)
        ·
          refine ⟨4214690594842260687084709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22478349839158723664451781 4214690594842260687084709)
          ·
            refine ⟨790254486532923878828383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4214690594842260687084709 790254486532923878828383)
            ·
              refine ⟨1185381729799385818242575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790254486532923878828383 1185381729799385818242575)
              ·
                refine ⟨1778072594699078727363863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185381729799385818242575 1778072594699078727363863)
                ·
                  refine ⟨2667108892048618091045795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778072594699078727363863 2667108892048618091045795)
                  ·
                    refine ⟨4000663338072927136568693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2667108892048618091045795 4000663338072927136568693)
                    ·
                      refine ⟨375062187944336919053315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4000663338072927136568693 375062187944336919053315)
                      ·
                        rfl

theorem cell23_730431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_730431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730431 prefixEnd_730431 := by exact prefixLift 730431
  have htrace : WordTrace (prefixWord ++ tailWord_730431) baseStart_730431 baseEnd_730431 := by
    simpa [prefixWord, tailWord_730431, baseEnd_730431] using wordTrace_append hprefix tailTrace_730431
  have hstable : (prefixWord ++ tailWord_730431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730431).length < 2 ^ (prefixWord ++ tailWord_730431).sum := by decide
  have hdescent : baseEnd_730431 < baseStart_730431 := by decide
  rcases family_descends (prefixWord ++ tailWord_730431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730501 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 3, 4, 2]
def baseStart_730501 : Nat := 118140960795 + 730501 * 2 ^ 59
def prefixEnd_730501 : Nat := 4983230072969 + 3 ^ 40 * 730501 * 2
def baseEnd_730501 : Nat := 375098131590151645177993

theorem tailTrace_730501 : CollatzResearch.WordTrace tailWord_730501 prefixEnd_730501 375098131590151645177993 := by
  unfold tailWord_730501
  simp only [CollatzResearch.WordTrace]
  refine ⟨26643560326527111483287357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17762373551018074322191571 26643560326527111483287357)
  ·
    refine ⟨9991335122447666806232759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26643560326527111483287357 9991335122447666806232759)
    ·
      refine ⟨14987002683671500209349139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9991335122447666806232759 14987002683671500209349139)
      ·
        refine ⟨22480504025507250314023709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14987002683671500209349139 22480504025507250314023709)
        ·
          refine ⟨8430189009565218867758891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22480504025507250314023709 8430189009565218867758891)
          ·
            refine ⟨12645283514347828301638337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8430189009565218867758891 12645283514347828301638337)
            ·
              refine ⟨9483962635760871226228753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12645283514347828301638337 9483962635760871226228753)
              ·
                refine ⟨7112971976820653419671565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9483962635760871226228753 7112971976820653419671565)
                ·
                  refine ⟨2667364491307745032376837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7112971976820653419671565 2667364491307745032376837)
                  ·
                    refine ⟨500130842120202193570657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2667364491307745032376837 500130842120202193570657)
                    ·
                      refine ⟨375098131590151645177993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500130842120202193570657 375098131590151645177993)
                      ·
                        rfl

theorem cell23_730501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 4, 2].length) (baseStart_730501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730501 prefixEnd_730501 := by exact prefixLift 730501
  have htrace : WordTrace (prefixWord ++ tailWord_730501) baseStart_730501 baseEnd_730501 := by
    simpa [prefixWord, tailWord_730501, baseEnd_730501] using wordTrace_append hprefix tailTrace_730501
  have hstable : (prefixWord ++ tailWord_730501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730501).length < 2 ^ (prefixWord ++ tailWord_730501).sum := by decide
  have hdescent : baseEnd_730501 < baseStart_730501 := by decide
  rcases family_descends (prefixWord ++ tailWord_730501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730584 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 2, 8]
def baseStart_730584 : Nat := 118140960795 + 730584 * 2 ^ 59
def prefixEnd_730584 : Nat := 4983230072969 + 3 ^ 40 * 730584 * 2
def baseEnd_730584 : Nat := 125046916828158273480037

theorem tailTrace_730584 : CollatzResearch.WordTrace tailWord_730584 prefixEnd_730584 125046916828158273480037 := by
  unfold tailWord_730584
  simp only [CollatzResearch.WordTrace]
  refine ⟨13323293792613208329279403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17764391723484277772372537 13323293792613208329279403)
  ·
    refine ⟨19984940688919812493919105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13323293792613208329279403 19984940688919812493919105)
    ·
      refine ⟨14988705516689859370439329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19984940688919812493919105 14988705516689859370439329)
      ·
        refine ⟨11241529137517394527829497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14988705516689859370439329 11241529137517394527829497)
        ·
          refine ⟨8431146853138045895872123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11241529137517394527829497 8431146853138045895872123)
          ·
            refine ⟨12646720279707068843808185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8431146853138045895872123 12646720279707068843808185)
            ·
              refine ⟨9485040209780301632856139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12646720279707068843808185 9485040209780301632856139)
              ·
                refine ⟨14227560314670452449284209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9485040209780301632856139 14227560314670452449284209)
                ·
                  refine ⟨10670670236002839336963157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14227560314670452449284209 10670670236002839336963157)
                  ·
                    refine ⟨125046916828158273480037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10670670236002839336963157 125046916828158273480037)
                    ·
                      rfl

theorem cell23_730584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_730584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730584 prefixEnd_730584 := by exact prefixLift 730584
  have htrace : WordTrace (prefixWord ++ tailWord_730584) baseStart_730584 baseEnd_730584 := by
    simpa [prefixWord, tailWord_730584, baseEnd_730584] using wordTrace_append hprefix tailTrace_730584
  have hstable : (prefixWord ++ tailWord_730584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730584).length < 2 ^ (prefixWord ++ tailWord_730584).sum := by decide
  have hdescent : baseEnd_730584 < baseStart_730584 := by decide
  rcases family_descends (prefixWord ++ tailWord_730584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730611 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 3]
def baseStart_730611 : Nat := 118140960795 + 730611 * 2 ^ 59
def prefixEnd_730611 : Nat := 4983230072969 + 3 ^ 40 * 730611 * 2
def baseEnd_730611 : Nat := 375154614462146214802487

theorem tailTrace_730611 : CollatzResearch.WordTrace tailWord_730611 prefixEnd_730611 375154614462146214802487 := by
  unfold tailWord_730611
  simp only [CollatzResearch.WordTrace]
  refine ⟨26647572356128600269791687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17765048237419066846527791 26647572356128600269791687)
  ·
    refine ⟨39971358534192900404687531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26647572356128600269791687 39971358534192900404687531)
    ·
      refine ⟨59957037801289350607031297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39971358534192900404687531 59957037801289350607031297)
      ·
        refine ⟨44967778350967012955273473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59957037801289350607031297 44967778350967012955273473)
        ·
          refine ⟨33725833763225259716455105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44967778350967012955273473 33725833763225259716455105)
          ·
            refine ⟨25294375322418944787341329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33725833763225259716455105 25294375322418944787341329)
            ·
              refine ⟨18970781491814208590505997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25294375322418944787341329 18970781491814208590505997)
              ·
                refine ⟨7114043059430328221439749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18970781491814208590505997 7114043059430328221439749)
                ·
                  refine ⟨1333883073643186541519953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7114043059430328221439749 1333883073643186541519953)
                  ·
                    refine ⟨1000412305232389906139965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1333883073643186541519953 1000412305232389906139965)
                    ·
                      refine ⟨375154614462146214802487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1000412305232389906139965 375154614462146214802487)
                      ·
                        rfl

theorem cell23_730611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 3].length) (baseStart_730611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730611 prefixEnd_730611 := by exact prefixLift 730611
  have htrace : WordTrace (prefixWord ++ tailWord_730611) baseStart_730611 baseEnd_730611 := by
    simpa [prefixWord, tailWord_730611, baseEnd_730611] using wordTrace_append hprefix tailTrace_730611
  have hstable : (prefixWord ++ tailWord_730611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730611).length < 2 ^ (prefixWord ++ tailWord_730611).sum := by decide
  have hdescent : baseEnd_730611 < baseStart_730611 := by decide
  rcases family_descends (prefixWord ++ tailWord_730611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730625 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_730625 : Nat := 118140960795 + 730625 * 2 ^ 59
def prefixEnd_730625 : Nat := 4983230072969 + 3 ^ 40 * 730625 * 2
def baseEnd_730625 : Nat := 375161803191309160027423

theorem tailTrace_730625 : CollatzResearch.WordTrace tailWord_730625 prefixEnd_730625 375161803191309160027423 := by
  unfold tailWord_730625
  simp only [CollatzResearch.WordTrace]
  refine ⟨26648082978077880660801329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17765388652051920440534219 26648082978077880660801329)
  ·
    refine ⟨19986062233558410495600997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26648082978077880660801329 19986062233558410495600997)
    ·
      refine ⟨3747386668792201967925187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19986062233558410495600997 3747386668792201967925187)
      ·
        refine ⟨5621080003188302951887781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3747386668792201967925187 5621080003188302951887781)
        ·
          refine ⟨1053952500597806803478959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5621080003188302951887781 1053952500597806803478959)
          ·
            refine ⟨1580928750896710205218439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053952500597806803478959 1580928750896710205218439)
            ·
              refine ⟨2371393126345065307827659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580928750896710205218439 2371393126345065307827659)
              ·
                refine ⟨3557089689517597961741489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371393126345065307827659 3557089689517597961741489)
                ·
                  refine ⟨2667817267138198471306117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3557089689517597961741489 2667817267138198471306117)
                  ·
                    refine ⟨500215737588412213369897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2667817267138198471306117 500215737588412213369897)
                    ·
                      refine ⟨375161803191309160027423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500215737588412213369897 375161803191309160027423)
                      ·
                        rfl

theorem cell23_730625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_730625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730625 prefixEnd_730625 := by exact prefixLift 730625
  have htrace : WordTrace (prefixWord ++ tailWord_730625) baseStart_730625 baseEnd_730625 := by
    simpa [prefixWord, tailWord_730625, baseEnd_730625] using wordTrace_append hprefix tailTrace_730625
  have hstable : (prefixWord ++ tailWord_730625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730625).length < 2 ^ (prefixWord ++ tailWord_730625).sum := by decide
  have hdescent : baseEnd_730625 < baseStart_730625 := by decide
  rcases family_descends (prefixWord ++ tailWord_730625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730645 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_730645 : Nat := 118140960795 + 730645 * 2 ^ 59
def prefixEnd_730645 : Nat := 4983230072969 + 3 ^ 40 * 730645 * 2
def baseEnd_730645 : Nat := 375172072804399081777331

theorem tailTrace_730645 : CollatzResearch.WordTrace tailWord_730645 prefixEnd_730645 375172072804399081777331 := by
  unfold tailWord_730645
  simp only [CollatzResearch.WordTrace]
  refine ⟨26648812438005424076529389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17765874958670282717686259 26648812438005424076529389)
  ·
    refine ⟨9993304664252034028698521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26648812438005424076529389 9993304664252034028698521)
    ·
      refine ⟨7494978498189025521523891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9993304664252034028698521 7494978498189025521523891)
      ·
        refine ⟨11242467747283538282285837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7494978498189025521523891 11242467747283538282285837)
        ·
          refine ⟨4215925405231326855857189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11242467747283538282285837 4215925405231326855857189)
          ·
            refine ⟨790486013480873785473223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4215925405231326855857189 790486013480873785473223)
            ·
              refine ⟨1185729020221310678209835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790486013480873785473223 1185729020221310678209835)
              ·
                refine ⟨1778593530331966017314753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185729020221310678209835 1778593530331966017314753)
                ·
                  refine ⟨1333945147748974512986065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1778593530331966017314753 1333945147748974512986065)
                  ·
                    refine ⟨1000458860811730884739549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1333945147748974512986065 1000458860811730884739549)
                    ·
                      refine ⟨375172072804399081777331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1000458860811730884739549 375172072804399081777331)
                      ·
                        rfl

theorem cell23_730645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_730645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730645 prefixEnd_730645 := by exact prefixLift 730645
  have htrace : WordTrace (prefixWord ++ tailWord_730645) baseStart_730645 baseEnd_730645 := by
    simpa [prefixWord, tailWord_730645, baseEnd_730645] using wordTrace_append hprefix tailTrace_730645
  have hstable : (prefixWord ++ tailWord_730645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730645).length < 2 ^ (prefixWord ++ tailWord_730645).sum := by decide
  have hdescent : baseEnd_730645 < baseStart_730645 := by decide
  rcases family_descends (prefixWord ++ tailWord_730645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730675 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 3, 1, 3]
def baseStart_730675 : Nat := 118140960795 + 730675 * 2 ^ 59
def prefixEnd_730675 : Nat := 4983230072969 + 3 ^ 40 * 730675 * 2
def baseEnd_730675 : Nat := 375187477224033964402193

theorem tailTrace_730675 : CollatzResearch.WordTrace tailWord_730675 prefixEnd_730675 375187477224033964402193 := by
  unfold tailWord_730675
  simp only [CollatzResearch.WordTrace]
  refine ⟨26649906627896739200121479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17766604418597826133414319 26649906627896739200121479)
  ·
    refine ⟨39974859941845108800182219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26649906627896739200121479 39974859941845108800182219)
    ·
      refine ⟨59962289912767663200273329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39974859941845108800182219 59962289912767663200273329)
      ·
        refine ⟨44971717434575747400204997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59962289912767663200273329 44971717434575747400204997)
        ·
          refine ⟨8432197018982952637538437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44971717434575747400204997 8432197018982952637538437)
          ·
            refine ⟨1581036941059303619538457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8432197018982952637538437 1581036941059303619538457)
            ·
              refine ⟨1185777705794477714653843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581036941059303619538457 1185777705794477714653843)
              ·
                refine ⟨1778666558691716571980765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185777705794477714653843 1778666558691716571980765)
                ·
                  refine ⟨666999959509393714492787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1778666558691716571980765 666999959509393714492787)
                  ·
                    refine ⟨1000499939264090571739181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 666999959509393714492787 1000499939264090571739181)
                    ·
                      refine ⟨375187477224033964402193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1000499939264090571739181 375187477224033964402193)
                      ·
                        rfl

theorem cell23_730675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 1, 3].length) (baseStart_730675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730675 prefixEnd_730675 := by exact prefixLift 730675
  have htrace : WordTrace (prefixWord ++ tailWord_730675) baseStart_730675 baseEnd_730675 := by
    simpa [prefixWord, tailWord_730675, baseEnd_730675] using wordTrace_append hprefix tailTrace_730675
  have hstable : (prefixWord ++ tailWord_730675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730675).length < 2 ^ (prefixWord ++ tailWord_730675).sum := by decide
  have hdescent : baseEnd_730675 < baseStart_730675 := by decide
  rcases family_descends (prefixWord ++ tailWord_730675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730695 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 1, 5]
def baseStart_730695 : Nat := 118140960795 + 730695 * 2 ^ 59
def prefixEnd_730695 : Nat := 4983230072969 + 3 ^ 40 * 730695 * 2
def baseEnd_730695 : Nat := 125065915612374628717367

theorem tailTrace_730695 : CollatzResearch.WordTrace tailWord_730695 prefixEnd_730695 125065915612374628717367 := by
  unfold tailWord_730695
  simp only [CollatzResearch.WordTrace]
  refine ⟨26650636087824282615849539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17767090725216188410566359 26650636087824282615849539)
  ·
    refine ⟨39975954131736423923774309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26650636087824282615849539 39975954131736423923774309)
    ·
      refine ⟨7495491399700579485707683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39975954131736423923774309 7495491399700579485707683)
      ·
        refine ⟨11243237099550869228561525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7495491399700579485707683 11243237099550869228561525)
        ·
          refine ⟨1054053478082893990177643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11243237099550869228561525 1054053478082893990177643)
          ·
            refine ⟨1581080217124340985266465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054053478082893990177643 1581080217124340985266465)
            ·
              refine ⟨1185810162843255738949849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581080217124340985266465 1185810162843255738949849)
              ·
                refine ⟨889357622132441804212387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185810162843255738949849 889357622132441804212387)
                ·
                  refine ⟨1334036433198662706318581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889357622132441804212387 1334036433198662706318581)
                  ·
                    refine ⟨125065915612374628717367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1334036433198662706318581 125065915612374628717367)
                    ·
                      rfl

theorem cell23_730695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_730695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730695 prefixEnd_730695 := by exact prefixLift 730695
  have htrace : WordTrace (prefixWord ++ tailWord_730695) baseStart_730695 baseEnd_730695 := by
    simpa [prefixWord, tailWord_730695, baseEnd_730695] using wordTrace_append hprefix tailTrace_730695
  have hstable : (prefixWord ++ tailWord_730695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730695).length < 2 ^ (prefixWord ++ tailWord_730695).sum := by decide
  have hdescent : baseEnd_730695 < baseStart_730695 := by decide
  rcases family_descends (prefixWord ++ tailWord_730695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730698 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2]
def baseStart_730698 : Nat := 118140960795 + 730698 * 2 ^ 59
def prefixEnd_730698 : Nat := 4983230072969 + 3 ^ 40 * 730698 * 2
def baseEnd_730698 : Nat := 375199287279087374414587

theorem tailTrace_730698 : CollatzResearch.WordTrace tailWord_730698 prefixEnd_730698 375199287279087374414587 := by
  unfold tailWord_730698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6662686376703353532052187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17767163671208942752139165 6662686376703353532052187)
  ·
    refine ⟨9994029565055030298078281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6662686376703353532052187 9994029565055030298078281)
    ·
      refine ⟨7495522173791272723558711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9994029565055030298078281 7495522173791272723558711)
      ·
        refine ⟨11243283260686909085338067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7495522173791272723558711 11243283260686909085338067)
        ·
          refine ⟨16864924891030363628007101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11243283260686909085338067 16864924891030363628007101)
          ·
            refine ⟨6324346834136386360502663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16864924891030363628007101 6324346834136386360502663)
            ·
              refine ⟨9486520251204579540753995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6324346834136386360502663 9486520251204579540753995)
              ·
                refine ⟨14229780376806869311130993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9486520251204579540753995 14229780376806869311130993)
                ·
                  refine ⟨10672335282605151983348245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14229780376806869311130993 10672335282605151983348245)
                  ·
                    refine ⟨500265716372116499219449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10672335282605151983348245 500265716372116499219449)
                    ·
                      refine ⟨375199287279087374414587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500265716372116499219449 375199287279087374414587)
                      ·
                        rfl

theorem cell23_730698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_730698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730698 prefixEnd_730698 := by exact prefixLift 730698
  have htrace : WordTrace (prefixWord ++ tailWord_730698) baseStart_730698 baseEnd_730698 := by
    simpa [prefixWord, tailWord_730698, baseEnd_730698] using wordTrace_append hprefix tailTrace_730698
  have hstable : (prefixWord ++ tailWord_730698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730698).length < 2 ^ (prefixWord ++ tailWord_730698).sum := by decide
  have hdescent : baseEnd_730698 < baseStart_730698 := by decide
  rcases family_descends (prefixWord ++ tailWord_730698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730708 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_730708 : Nat := 118140960795 + 730708 * 2 ^ 59
def prefixEnd_730708 : Nat := 4983230072969 + 3 ^ 40 * 730708 * 2
def baseEnd_730708 : Nat := 125068140695210778429847

theorem tailTrace_730708 : CollatzResearch.WordTrace tailWord_730708 prefixEnd_730708 125068140695210778429847 := by
  unfold tailWord_730708
  simp only [CollatzResearch.WordTrace]
  refine ⟨13325555118388592918036389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17767406824518123890715185 13325555118388592918036389)
  ·
    refine ⟨2498541584697861172131823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13325555118388592918036389 2498541584697861172131823)
    ·
      refine ⟨3747812377046791758197735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2498541584697861172131823 3747812377046791758197735)
      ·
        refine ⟨5621718565570187637296603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3747812377046791758197735 5621718565570187637296603)
        ·
          refine ⟨8432577848355281455944905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5621718565570187637296603 8432577848355281455944905)
          ·
            refine ⟨6324433386266461091958679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8432577848355281455944905 6324433386266461091958679)
            ·
              refine ⟨9486650079399691637938019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6324433386266461091958679 9486650079399691637938019)
              ·
                refine ⟨14229975119099537456907029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9486650079399691637938019 14229975119099537456907029)
                ·
                  refine ⟨667030083707790818292517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14229975119099537456907029 667030083707790818292517)
                  ·
                    refine ⟨125068140695210778429847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 667030083707790818292517 125068140695210778429847)
                    ·
                      rfl

theorem cell23_730708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_730708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730708 prefixEnd_730708 := by exact prefixLift 730708
  have htrace : WordTrace (prefixWord ++ tailWord_730708) baseStart_730708 baseEnd_730708 := by
    simpa [prefixWord, tailWord_730708, baseEnd_730708] using wordTrace_append hprefix tailTrace_730708
  have hstable : (prefixWord ++ tailWord_730708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730708).length < 2 ^ (prefixWord ++ tailWord_730708).sum := by decide
  have hdescent : baseEnd_730708 < baseStart_730708 := by decide
  rcases family_descends (prefixWord ++ tailWord_730708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730728 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_730728 : Nat := 118140960795 + 730728 * 2 ^ 59
def prefixEnd_730728 : Nat := 4983230072969 + 3 ^ 40 * 730728 * 2
def baseEnd_730728 : Nat := 375214691698722257039449

theorem tailTrace_730728 : CollatzResearch.WordTrace tailWord_730728 prefixEnd_730728 375214691698722257039449 := by
  unfold tailWord_730728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13325919848352364625900419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17767893131136486167867225 13325919848352364625900419)
  ·
    refine ⟨19988879772528546938850629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13325919848352364625900419 19988879772528546938850629)
    ·
      refine ⟨3747914957349102551034493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19988879772528546938850629 3747914957349102551034493)
      ·
        refine ⟨1405468109005913456637935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3747914957349102551034493 1405468109005913456637935)
        ·
          refine ⟨2108202163508870184956903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405468109005913456637935 2108202163508870184956903)
          ·
            refine ⟨3162303245263305277435355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108202163508870184956903 3162303245263305277435355)
            ·
              refine ⟨4743454867894957916153033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162303245263305277435355 4743454867894957916153033)
              ·
                refine ⟨3557591150921218437114775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4743454867894957916153033 3557591150921218437114775)
                ·
                  refine ⟨5336386726381827655672163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3557591150921218437114775 5336386726381827655672163)
                  ·
                    refine ⟨8004580089572741483508245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5336386726381827655672163 8004580089572741483508245)
                    ·
                      refine ⟨375214691698722257039449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8004580089572741483508245 375214691698722257039449)
                      ·
                        rfl

theorem cell23_730728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_730728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730728 prefixEnd_730728 := by exact prefixLift 730728
  have htrace : WordTrace (prefixWord ++ tailWord_730728) baseStart_730728 baseEnd_730728 := by
    simpa [prefixWord, tailWord_730728, baseEnd_730728] using wordTrace_append hprefix tailTrace_730728
  have hstable : (prefixWord ++ tailWord_730728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730728).length < 2 ^ (prefixWord ++ tailWord_730728).sum := by decide
  have hdescent : baseEnd_730728 < baseStart_730728 := by decide
  rcases family_descends (prefixWord ++ tailWord_730728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730738 : List Nat := [3, 2, 1, 2, 3, 2, 2, 8]
def baseStart_730738 : Nat := 118140960795 + 730738 * 2 ^ 59
def prefixEnd_730738 : Nat := 4983230072969 + 3 ^ 40 * 730738 * 2
def baseEnd_730738 : Nat := 13897030611306193256089

theorem tailTrace_730738 : CollatzResearch.WordTrace tailWord_730738 prefixEnd_730738 13897030611306193256089 := by
  unfold tailWord_730738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663051106667125239916217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17768136284445667306443245 6663051106667125239916217)
  ·
    refine ⟨4997288330000343929937163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6663051106667125239916217 4997288330000343929937163)
    ·
      refine ⟨7495932495000515894905745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4997288330000343929937163 7495932495000515894905745)
      ·
        refine ⟨5621949371250386921179309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7495932495000515894905745 5621949371250386921179309)
        ·
          refine ⟨2108231014218895095442241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5621949371250386921179309 2108231014218895095442241)
          ·
            refine ⟨1581173260664171321581681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2108231014218895095442241 1581173260664171321581681)
            ·
              refine ⟨1185879945498128491186261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581173260664171321581681 1185879945498128491186261)
              ·
                refine ⟨13897030611306193256089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1185879945498128491186261 13897030611306193256089)
                ·
                  rfl

theorem cell23_730738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 8].length) (baseStart_730738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730738 prefixEnd_730738 := by exact prefixLift 730738
  have htrace : WordTrace (prefixWord ++ tailWord_730738) baseStart_730738 baseEnd_730738 := by
    simpa [prefixWord, tailWord_730738, baseEnd_730738] using wordTrace_append hprefix tailTrace_730738
  have hstable : (prefixWord ++ tailWord_730738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730738).length < 2 ^ (prefixWord ++ tailWord_730738).sum := by decide
  have hdescent : baseEnd_730738 < baseStart_730738 := by decide
  rcases family_descends (prefixWord ++ tailWord_730738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730742 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_730742 : Nat := 118140960795 + 730742 * 2 ^ 59
def prefixEnd_730742 : Nat := 4983230072969 + 3 ^ 40 * 730742 * 2
def baseEnd_730742 : Nat := 125073960142628400754795

theorem tailTrace_730742 : CollatzResearch.WordTrace tailWord_730742 prefixEnd_730742 125073960142628400754795 := by
  unfold tailWord_730742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1665771894915875602675655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17768233545769339761873653 1665771894915875602675655)
  ·
    refine ⟨2498657842373813404013483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1665771894915875602675655 2498657842373813404013483)
    ·
      refine ⟨3747986763560720106020225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2498657842373813404013483 3747986763560720106020225)
      ·
        refine ⟨2810990072670540079515169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3747986763560720106020225 2810990072670540079515169)
        ·
          refine ⟨2108242554502905059636377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2810990072670540079515169 2108242554502905059636377)
          ·
            refine ⟨1581181915877178794727283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2108242554502905059636377 1581181915877178794727283)
            ·
              refine ⟨2371772873815768192090925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581181915877178794727283 2371772873815768192090925)
              ·
                refine ⟨889414827680913072034097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2371772873815768192090925 889414827680913072034097)
                ·
                  refine ⟨667061120760684804025573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 889414827680913072034097 667061120760684804025573)
                  ·
                    refine ⟨125073960142628400754795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 667061120760684804025573 125073960142628400754795)
                    ·
                      rfl

theorem cell23_730742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_730742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730742 prefixEnd_730742 := by exact prefixLift 730742
  have htrace : WordTrace (prefixWord ++ tailWord_730742) baseStart_730742 baseEnd_730742 := by
    simpa [prefixWord, tailWord_730742, baseEnd_730742] using wordTrace_append hprefix tailTrace_730742
  have hstable : (prefixWord ++ tailWord_730742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730742).length < 2 ^ (prefixWord ++ tailWord_730742).sum := by decide
  have hdescent : baseEnd_730742 < baseStart_730742 := by decide
  rcases family_descends (prefixWord ++ tailWord_730742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730748 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_730748 : Nat := 118140960795 + 730748 * 2 ^ 59
def prefixEnd_730748 : Nat := 4983230072969 + 3 ^ 40 * 730748 * 2
def baseEnd_730748 : Nat := 375224961311812178789357

theorem tailTrace_730748 : CollatzResearch.WordTrace tailWord_730748 prefixEnd_730748 375224961311812178789357 := by
  unfold tailWord_730748
  simp only [CollatzResearch.WordTrace]
  refine ⟨13326284578316136333764449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17768379437754848445019265 13326284578316136333764449)
  ·
    refine ⟨9994713433737102250323337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13326284578316136333764449 9994713433737102250323337)
    ·
      refine ⟨7496035075302826687742503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9994713433737102250323337 7496035075302826687742503)
      ·
        refine ⟨11244052612954240031613755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7496035075302826687742503 11244052612954240031613755)
        ·
          refine ⟨16866078919431360047420633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11244052612954240031613755 16866078919431360047420633)
          ·
            refine ⟨12649559189573520035565475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16866078919431360047420633 12649559189573520035565475)
            ·
              refine ⟨18974338784360280053348213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12649559189573520035565475 18974338784360280053348213)
              ·
                refine ⟨1778844261033776255001395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18974338784360280053348213 1778844261033776255001395)
                ·
                  refine ⟨2668266391550664382502093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778844261033776255001395 2668266391550664382502093)
                  ·
                    refine ⟨1000599896831499143438285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2668266391550664382502093 1000599896831499143438285)
                    ·
                      refine ⟨375224961311812178789357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1000599896831499143438285 375224961311812178789357)
                      ·
                        rfl

theorem cell23_730748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_730748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730748 prefixEnd_730748 := by exact prefixLift 730748
  have htrace : WordTrace (prefixWord ++ tailWord_730748) baseStart_730748 baseEnd_730748 := by
    simpa [prefixWord, tailWord_730748, baseEnd_730748] using wordTrace_append hprefix tailTrace_730748
  have hstable : (prefixWord ++ tailWord_730748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730748).length < 2 ^ (prefixWord ++ tailWord_730748).sum := by decide
  have hdescent : baseEnd_730748 < baseStart_730748 := by decide
  rcases family_descends (prefixWord ++ tailWord_730748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730761 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_730761 : Nat := 118140960795 + 730761 * 2 ^ 59
def prefixEnd_730761 : Nat := 4983230072969 + 3 ^ 40 * 730761 * 2
def baseEnd_730761 : Nat := 375231636560320627926797

theorem tailTrace_730761 : CollatzResearch.WordTrace tailWord_730761 prefixEnd_730761 375231636560320627926797 := by
  unfold tailWord_730761
  simp only [CollatzResearch.WordTrace]
  refine ⟨26653043305585175887752137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17768695537056783925168091 26653043305585175887752137)
  ·
    refine ⟨19989782479188881915814103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26653043305585175887752137 19989782479188881915814103)
    ·
      refine ⟨29984673718783322873721155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19989782479188881915814103 29984673718783322873721155)
      ·
        refine ⟨44977010578174984310581733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29984673718783322873721155 44977010578174984310581733)
        ·
          refine ⟨8433189483407809558234075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44977010578174984310581733 8433189483407809558234075)
          ·
            refine ⟨12649784225111714337351113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8433189483407809558234075 12649784225111714337351113)
            ·
              refine ⟨9487338168833785753013335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12649784225111714337351113 9487338168833785753013335)
              ·
                refine ⟨14231007253250678629520003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9487338168833785753013335 14231007253250678629520003)
                ·
                  refine ⟨21346510879876017944280005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14231007253250678629520003 21346510879876017944280005)
                  ·
                    refine ⟨4002470789976753364552501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21346510879876017944280005 4002470789976753364552501)
                    ·
                      refine ⟨375231636560320627926797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4002470789976753364552501 375231636560320627926797)
                      ·
                        rfl

theorem cell23_730761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_730761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730761 prefixEnd_730761 := by exact prefixLift 730761
  have htrace : WordTrace (prefixWord ++ tailWord_730761) baseStart_730761 baseEnd_730761 := by
    simpa [prefixWord, tailWord_730761, baseEnd_730761] using wordTrace_append hprefix tailTrace_730761
  have hstable : (prefixWord ++ tailWord_730761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730761).length < 2 ^ (prefixWord ++ tailWord_730761).sum := by decide
  have hdescent : baseEnd_730761 < baseStart_730761 := by decide
  rcases family_descends (prefixWord ++ tailWord_730761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730771 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 4]
def baseStart_730771 : Nat := 118140960795 + 730771 * 2 ^ 59
def prefixEnd_730771 : Nat := 4983230072969 + 3 ^ 40 * 730771 * 2
def baseEnd_730771 : Nat := 375236771366865588801751

theorem tailTrace_730771 : CollatzResearch.WordTrace tailWord_730771 prefixEnd_730771 375236771366865588801751 := by
  unfold tailWord_730771
  simp only [CollatzResearch.WordTrace]
  refine ⟨26653408035548947595616167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17768938690365965063744111 26653408035548947595616167)
  ·
    refine ⟨39980112053323421393424251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26653408035548947595616167 39980112053323421393424251)
    ·
      refine ⟨59970168079985132090136377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39980112053323421393424251 59970168079985132090136377)
      ·
        refine ⟨44977626059988849067602283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59970168079985132090136377 44977626059988849067602283)
        ·
          refine ⟨67466439089983273601403425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44977626059988849067602283 67466439089983273601403425)
          ·
            refine ⟨50599829317487455201052569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67466439089983273601403425 50599829317487455201052569)
            ·
              refine ⟨37949871988115591400789427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50599829317487455201052569 37949871988115591400789427)
              ·
                refine ⟨56924807982173387101184141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37949871988115591400789427 56924807982173387101184141)
                ·
                  refine ⟨21346802993315020162944053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56924807982173387101184141 21346802993315020162944053)
                  ·
                    refine ⟨2001262780623283140276005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21346802993315020162944053 2001262780623283140276005)
                    ·
                      refine ⟨375236771366865588801751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2001262780623283140276005 375236771366865588801751)
                      ·
                        rfl

theorem cell23_730771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_730771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730771 prefixEnd_730771 := by exact prefixLift 730771
  have htrace : WordTrace (prefixWord ++ tailWord_730771) baseStart_730771 baseEnd_730771 := by
    simpa [prefixWord, tailWord_730771, baseEnd_730771] using wordTrace_append hprefix tailTrace_730771
  have hstable : (prefixWord ++ tailWord_730771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730771).length < 2 ^ (prefixWord ++ tailWord_730771).sum := by decide
  have hdescent : baseEnd_730771 < baseStart_730771 := by decide
  rcases family_descends (prefixWord ++ tailWord_730771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730788 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_730788 : Nat := 118140960795 + 730788 * 2 ^ 59
def prefixEnd_730788 : Nat := 4983230072969 + 3 ^ 40 * 730788 * 2
def baseEnd_730788 : Nat := 375245500537992022289173

theorem tailTrace_730788 : CollatzResearch.WordTrace tailWord_730788 prefixEnd_730788 375245500537992022289173 := by
  unfold tailWord_730788
  simp only [CollatzResearch.WordTrace]
  refine ⟨13327014038243679749492509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17769352050991572999323345 13327014038243679749492509)
  ·
    refine ⟨4997630264341379906059691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13327014038243679749492509 4997630264341379906059691)
    ·
      refine ⟨7496445396512069859089537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4997630264341379906059691 7496445396512069859089537)
      ·
        refine ⟨5622334047384052394317153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7496445396512069859089537 5622334047384052394317153)
        ·
          refine ⟨4216750535538039295737865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5622334047384052394317153 4216750535538039295737865)
          ·
            refine ⟨3162562901653529471803399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4216750535538039295737865 3162562901653529471803399)
            ·
              refine ⟨4743844352480294207705099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162562901653529471803399 4743844352480294207705099)
              ·
                refine ⟨7115766528720441311557649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743844352480294207705099 7115766528720441311557649)
                ·
                  refine ⟨5336824896540330983668237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7115766528720441311557649 5336824896540330983668237)
                  ·
                    refine ⟨2001309336202624118875589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5336824896540330983668237 2001309336202624118875589)
                    ·
                      refine ⟨375245500537992022289173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2001309336202624118875589 375245500537992022289173)
                      ·
                        rfl

theorem cell23_730788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_730788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730788 prefixEnd_730788 := by exact prefixLift 730788
  have htrace : WordTrace (prefixWord ++ tailWord_730788) baseStart_730788 baseEnd_730788 := by
    simpa [prefixWord, tailWord_730788, baseEnd_730788] using wordTrace_append hprefix tailTrace_730788
  have hstable : (prefixWord ++ tailWord_730788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730788).length < 2 ^ (prefixWord ++ tailWord_730788).sum := by decide
  have hdescent : baseEnd_730788 < baseStart_730788 := by decide
  rcases family_descends (prefixWord ++ tailWord_730788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730826 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2]
def baseStart_730826 : Nat := 118140960795 + 730826 * 2 ^ 59
def prefixEnd_730826 : Nat := 4983230072969 + 3 ^ 40 * 730826 * 2
def baseEnd_730826 : Nat := 375265012802862873613999

theorem tailTrace_730826 : CollatzResearch.WordTrace tailWord_730826 prefixEnd_730826 375265012802862873613999 := by
  unfold tailWord_730826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663853512587422997217083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17770276033566461325912221 6663853512587422997217083)
  ·
    refine ⟨9995780268881134495825625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6663853512587422997217083 9995780268881134495825625)
    ·
      refine ⟨7496835201660850871869219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9995780268881134495825625 7496835201660850871869219)
      ·
        refine ⟨11245252802491276307803829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7496835201660850871869219 11245252802491276307803829)
        ·
          refine ⟨1054242450233557153856609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11245252802491276307803829 1054242450233557153856609)
          ·
            refine ⟨790681837675167865392457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1054242450233557153856609 790681837675167865392457)
            ·
              refine ⟨593011378256375899044343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790681837675167865392457 593011378256375899044343)
              ·
                refine ⟨889517067384563848566515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593011378256375899044343 889517067384563848566515)
                ·
                  refine ⟨1334275601076845772849773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889517067384563848566515 1334275601076845772849773)
                  ·
                    refine ⟨500353350403817164818665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1334275601076845772849773 500353350403817164818665)
                    ·
                      refine ⟨375265012802862873613999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500353350403817164818665 375265012802862873613999)
                      ·
                        rfl

theorem cell23_730826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_730826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730826 prefixEnd_730826 := by exact prefixLift 730826
  have htrace : WordTrace (prefixWord ++ tailWord_730826) baseStart_730826 baseEnd_730826 := by
    simpa [prefixWord, tailWord_730826, baseEnd_730826] using wordTrace_append hprefix tailTrace_730826
  have hstable : (prefixWord ++ tailWord_730826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730826).length < 2 ^ (prefixWord ++ tailWord_730826).sum := by decide
  have hdescent : baseEnd_730826 < baseStart_730826 := by decide
  rcases family_descends (prefixWord ++ tailWord_730826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730856 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_730856 : Nat := 118140960795 + 730856 * 2 ^ 59
def prefixEnd_730856 : Nat := 4983230072969 + 3 ^ 40 * 730856 * 2
def baseEnd_730856 : Nat := 375280417222497756238861

theorem tailTrace_730856 : CollatzResearch.WordTrace tailWord_730856 prefixEnd_730856 375280417222497756238861 := by
  unfold tailWord_730856
  simp only [CollatzResearch.WordTrace]
  refine ⟨13328254120120503556230211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17771005493494004741640281 13328254120120503556230211)
  ·
    refine ⟨19992381180180755334345317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13328254120120503556230211 19992381180180755334345317)
    ·
      refine ⟨3748571471283891625189747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19992381180180755334345317 3748571471283891625189747)
      ·
        refine ⟨5622857206925837437784621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3748571471283891625189747 5622857206925837437784621)
        ·
          refine ⟨2108571452597189039169233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5622857206925837437784621 2108571452597189039169233)
          ·
            refine ⟨1581428589447891779376925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2108571452597189039169233 1581428589447891779376925)
            ·
              refine ⟨593035721042959417266347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1581428589447891779376925 593035721042959417266347)
              ·
                refine ⟨889553581564439125899521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593035721042959417266347 889553581564439125899521)
                ·
                  refine ⟨667165186173329344424641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 889553581564439125899521 667165186173329344424641)
                  ·
                    refine ⟨500373889629997008318481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 667165186173329344424641 500373889629997008318481)
                    ·
                      refine ⟨375280417222497756238861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500373889629997008318481 375280417222497756238861)
                      ·
                        rfl

theorem cell23_730856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_730856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730856 prefixEnd_730856 := by exact prefixLift 730856
  have htrace : WordTrace (prefixWord ++ tailWord_730856) baseStart_730856 baseEnd_730856 := by
    simpa [prefixWord, tailWord_730856, baseEnd_730856] using wordTrace_append hprefix tailTrace_730856
  have hstable : (prefixWord ++ tailWord_730856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730856).length < 2 ^ (prefixWord ++ tailWord_730856).sum := by decide
  have hdescent : baseEnd_730856 < baseStart_730856 := by decide
  rcases family_descends (prefixWord ++ tailWord_730856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730858 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_730858 : Nat := 118140960795 + 730858 * 2 ^ 59
def prefixEnd_730858 : Nat := 4983230072969 + 3 ^ 40 * 730858 * 2
def baseEnd_730858 : Nat := 125093814727935582804617

theorem tailTrace_730858 : CollatzResearch.WordTrace tailWord_730858 prefixEnd_730858 125093814727935582804617 := by
  unfold tailWord_730858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6664145296558440363508307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17771054124155840969355485 6664145296558440363508307)
  ·
    refine ⟨9996217944837660545262461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6664145296558440363508307 9996217944837660545262461)
    ·
      refine ⟨3748581729314122704473423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9996217944837660545262461 3748581729314122704473423)
      ·
        refine ⟨5622872593971184056710135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3748581729314122704473423 5622872593971184056710135)
        ·
          refine ⟨8434308890956776085065203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622872593971184056710135 8434308890956776085065203)
          ·
            refine ⟨12651463336435164127597805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8434308890956776085065203 12651463336435164127597805)
            ·
              refine ⟨4744298751163186547849177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12651463336435164127597805 4744298751163186547849177)
              ·
                refine ⟨3558224063372389910886883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4744298751163186547849177 3558224063372389910886883)
                ·
                  refine ⟨5337336095058584866330325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3558224063372389910886883 5337336095058584866330325)
                  ·
                    refine ⟨125093814727935582804617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5337336095058584866330325 125093814727935582804617)
                    ·
                      rfl

theorem cell23_730858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_730858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730858 prefixEnd_730858 := by exact prefixLift 730858
  have htrace : WordTrace (prefixWord ++ tailWord_730858) baseStart_730858 baseEnd_730858 := by
    simpa [prefixWord, tailWord_730858, baseEnd_730858] using wordTrace_append hprefix tailTrace_730858
  have hstable : (prefixWord ++ tailWord_730858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730858).length < 2 ^ (prefixWord ++ tailWord_730858).sum := by decide
  have hdescent : baseEnd_730858 < baseStart_730858 := by decide
  rcases family_descends (prefixWord ++ tailWord_730858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730895 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 2, 4, 2]
def baseStart_730895 : Nat := 118140960795 + 730895 * 2 ^ 59
def prefixEnd_730895 : Nat := 4983230072969 + 3 ^ 40 * 730895 * 2
def baseEnd_730895 : Nat := 375300442968023103651181

theorem tailTrace_730895 : CollatzResearch.WordTrace tailWord_730895 prefixEnd_730895 375300442968023103651181 := by
  unfold tailWord_730895
  simp only [CollatzResearch.WordTrace]
  refine ⟨26657930687099716773130139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17771953791399811182086759 26657930687099716773130139)
  ·
    refine ⟨39986896030649575159695209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26657930687099716773130139 39986896030649575159695209)
    ·
      refine ⟨29990172022987181369771407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39986896030649575159695209 29990172022987181369771407)
      ·
        refine ⟨44985258034480772054657111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29990172022987181369771407 44985258034480772054657111)
        ·
          refine ⟨67477887051721158081985667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44985258034480772054657111 67477887051721158081985667)
          ·
            refine ⟨101216830577581737122978501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67477887051721158081985667 101216830577581737122978501)
            ·
              refine ⟨18978155733296575710558469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101216830577581737122978501 18978155733296575710558469)
              ·
                refine ⟨3558404199993107945729713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18978155733296575710558469 3558404199993107945729713)
                ·
                  refine ⟨2668803149994830959297285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3558404199993107945729713 2668803149994830959297285)
                  ·
                    refine ⟨500400590624030804868241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668803149994830959297285 500400590624030804868241)
                    ·
                      refine ⟨375300442968023103651181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500400590624030804868241 375300442968023103651181)
                      ·
                        rfl

theorem cell23_730895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 4, 2].length) (baseStart_730895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730895 prefixEnd_730895 := by exact prefixLift 730895
  have htrace : WordTrace (prefixWord ++ tailWord_730895) baseStart_730895 baseEnd_730895 := by
    simpa [prefixWord, tailWord_730895, baseEnd_730895] using wordTrace_append hprefix tailTrace_730895
  have hstable : (prefixWord ++ tailWord_730895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730895).length < 2 ^ (prefixWord ++ tailWord_730895).sum := by decide
  have hdescent : baseEnd_730895 < baseStart_730895 := by decide
  rcases family_descends (prefixWord ++ tailWord_730895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730965 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_730965 : Nat := 118140960795 + 730965 * 2 ^ 59
def prefixEnd_730965 : Nat := 4983230072969 + 3 ^ 40 * 730965 * 2
def baseEnd_730965 : Nat := 125112128871279276591953

theorem tailTrace_730965 : CollatzResearch.WordTrace tailWord_730965 prefixEnd_730965 125112128871279276591953 := by
  unfold tailWord_730965
  simp only [CollatzResearch.WordTrace]
  refine ⟨26660483796846118728178349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17773655864564079152118899 26660483796846118728178349)
  ·
    refine ⟨9997681423817294523066881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26660483796846118728178349 9997681423817294523066881)
    ·
      refine ⟨7498261067862970892300161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9997681423817294523066881 7498261067862970892300161)
      ·
        refine ⟨5623695800897228169225121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7498261067862970892300161 5623695800897228169225121)
        ·
          refine ⟨4217771850672921126918841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5623695800897228169225121 4217771850672921126918841)
          ·
            refine ⟨3163328888004690845189131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4217771850672921126918841 3163328888004690845189131)
            ·
              refine ⟨4744993332007036267783697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163328888004690845189131 4744993332007036267783697)
              ·
                refine ⟨3558744999005277200837773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4744993332007036267783697 3558744999005277200837773)
                ·
                  refine ⟨1334529374626978950314165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3558744999005277200837773 1334529374626978950314165)
                  ·
                    refine ⟨125112128871279276591953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1334529374626978950314165 125112128871279276591953)
                    ·
                      rfl

theorem cell23_730965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_730965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730965 prefixEnd_730965 := by exact prefixLift 730965
  have htrace : WordTrace (prefixWord ++ tailWord_730965) baseStart_730965 baseEnd_730965 := by
    simpa [prefixWord, tailWord_730965, baseEnd_730965] using wordTrace_append hprefix tailTrace_730965
  have hstable : (prefixWord ++ tailWord_730965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730965).length < 2 ^ (prefixWord ++ tailWord_730965).sum := by decide
  have hdescent : baseEnd_730965 < baseStart_730965 := by decide
  rcases family_descends (prefixWord ++ tailWord_730965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730979 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 3, 1, 3]
def baseStart_730979 : Nat := 118140960795 + 730979 * 2 ^ 59
def prefixEnd_730979 : Nat := 4983230072969 + 3 ^ 40 * 730979 * 2
def baseEnd_730979 : Nat := 375343575343000775000795

theorem tailTrace_730979 : CollatzResearch.WordTrace tailWord_730979 prefixEnd_730979 375343575343000775000795 := by
  unfold tailWord_730979
  simp only [CollatzResearch.WordTrace]
  refine ⟨26660994418795399119187991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17773996279196932746125327 26660994418795399119187991)
  ·
    refine ⟨39991491628193098678781987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26660994418795399119187991 39991491628193098678781987)
    ·
      refine ⟨59987237442289648018172981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39991491628193098678781987 59987237442289648018172981)
      ·
        refine ⟨5623803510214654501703717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59987237442289648018172981 5623803510214654501703717)
        ·
          refine ⟨1054463158165247719069447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5623803510214654501703717 1054463158165247719069447)
          ·
            refine ⟨1581694737247871578604171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054463158165247719069447 1581694737247871578604171)
            ·
              refine ⟨2372542105871807367906257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581694737247871578604171 2372542105871807367906257)
              ·
                refine ⟨1779406579403855525929693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372542105871807367906257 1779406579403855525929693)
                ·
                  refine ⟨667277467276445822223635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1779406579403855525929693 667277467276445822223635)
                  ·
                    refine ⟨1000916200914668733335453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 667277467276445822223635 1000916200914668733335453)
                    ·
                      refine ⟨375343575343000775000795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1000916200914668733335453 375343575343000775000795)
                      ·
                        rfl

theorem cell23_730979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_730979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730979 prefixEnd_730979 := by exact prefixLift 730979
  have htrace : WordTrace (prefixWord ++ tailWord_730979) baseStart_730979 baseEnd_730979 := by
    simpa [prefixWord, tailWord_730979, baseEnd_730979] using wordTrace_append hprefix tailTrace_730979
  have hstable : (prefixWord ++ tailWord_730979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730979).length < 2 ^ (prefixWord ++ tailWord_730979).sum := by decide
  have hdescent : baseEnd_730979 < baseStart_730979 := by decide
  rcases family_descends (prefixWord ++ tailWord_730979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730989 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_730989 : Nat := 118140960795 + 730989 * 2 ^ 59
def prefixEnd_730989 : Nat := 4983230072969 + 3 ^ 40 * 730989 * 2
def baseEnd_730989 : Nat := 375348710149545735875749

theorem tailTrace_730989 : CollatzResearch.WordTrace tailWord_730989 prefixEnd_730989 375348710149545735875749 := by
  unfold tailWord_730989
  simp only [CollatzResearch.WordTrace]
  refine ⟨26661359148759170827052021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17774239432506113884701347 26661359148759170827052021)
  ·
    refine ⟨2499502420196172265036127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26661359148759170827052021 2499502420196172265036127)
    ·
      refine ⟨3749253630294258397554191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2499502420196172265036127 3749253630294258397554191)
      ·
        refine ⟨5623880445441387596331287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3749253630294258397554191 5623880445441387596331287)
        ·
          refine ⟨8435820668162081394496931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5623880445441387596331287 8435820668162081394496931)
          ·
            refine ⟨12653731002243122091745397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8435820668162081394496931 12653731002243122091745397)
            ·
              refine ⟨1186287281460292696101131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12653731002243122091745397 1186287281460292696101131)
              ·
                refine ⟨1779430922190439044151697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186287281460292696101131 1779430922190439044151697)
                ·
                  refine ⟨1334573191642829283113773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1779430922190439044151697 1334573191642829283113773)
                  ·
                    refine ⟨500464946866060981167665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1334573191642829283113773 500464946866060981167665)
                    ·
                      refine ⟨375348710149545735875749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500464946866060981167665 375348710149545735875749)
                      ·
                        rfl

theorem cell23_730989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_730989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730989 prefixEnd_730989 := by exact prefixLift 730989
  have htrace : WordTrace (prefixWord ++ tailWord_730989) baseStart_730989 baseEnd_730989 := by
    simpa [prefixWord, tailWord_730989, baseEnd_730989] using wordTrace_append hprefix tailTrace_730989
  have hstable : (prefixWord ++ tailWord_730989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730989).length < 2 ^ (prefixWord ++ tailWord_730989).sum := by decide
  have hdescent : baseEnd_730989 < baseStart_730989 := by decide
  rcases family_descends (prefixWord ++ tailWord_730989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730995 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 4, 4]
def baseStart_730995 : Nat := 118140960795 + 730995 * 2 ^ 59
def prefixEnd_730995 : Nat := 4983230072969 + 3 ^ 40 * 730995 * 2
def baseEnd_730995 : Nat := 125117263677824237466907

theorem tailTrace_730995 : CollatzResearch.WordTrace tailWord_730995 prefixEnd_730995 125117263677824237466907 := by
  unfold tailWord_730995
  simp only [CollatzResearch.WordTrace]
  refine ⟨26661577986737433851770439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17774385324491622567846959 26661577986737433851770439)
  ·
    refine ⟨39992366980106150777655659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26661577986737433851770439 39992366980106150777655659)
    ·
      refine ⟨59988550470159226166483489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39992366980106150777655659 59988550470159226166483489)
      ·
        refine ⟨44991412852619419624862617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59988550470159226166483489 44991412852619419624862617)
        ·
          refine ⟨33743559639464564718646963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44991412852619419624862617 33743559639464564718646963)
          ·
            refine ⟨50615339459196847077970445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33743559639464564718646963 50615339459196847077970445)
            ·
              refine ⟨18980752297198817654238917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50615339459196847077970445 18980752297198817654238917)
              ·
                refine ⟨3558891055724778310169797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18980752297198817654238917 3558891055724778310169797)
                ·
                  refine ⟨667292072948395933156837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3558891055724778310169797 667292072948395933156837)
                  ·
                    refine ⟨125117263677824237466907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 667292072948395933156837 125117263677824237466907)
                    ·
                      rfl

theorem cell23_730995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 4].length) (baseStart_730995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_730995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_730995 prefixEnd_730995 := by exact prefixLift 730995
  have htrace : WordTrace (prefixWord ++ tailWord_730995) baseStart_730995 baseEnd_730995 := by
    simpa [prefixWord, tailWord_730995, baseEnd_730995] using wordTrace_append hprefix tailTrace_730995
  have hstable : (prefixWord ++ tailWord_730995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730995).length < 2 ^ (prefixWord ++ tailWord_730995).sum := by decide
  have hdescent : baseEnd_730995 < baseStart_730995 := by decide
  rcases family_descends (prefixWord ++ tailWord_730995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731005 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_731005 : Nat := 118140960795 + 731005 * 2 ^ 59
def prefixEnd_731005 : Nat := 4983230072969 + 3 ^ 40 * 731005 * 2
def baseEnd_731005 : Nat := 375356925840017673275675

theorem tailTrace_731005 : CollatzResearch.WordTrace tailWord_731005 prefixEnd_731005 375356925840017673275675 := by
  unfold tailWord_731005
  simp only [CollatzResearch.WordTrace]
  refine ⟨26661942716701205559634469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17774628477800803706422979 26661942716701205559634469)
  ·
    refine ⟨4999114259381476042431463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26661942716701205559634469 4999114259381476042431463)
    ·
      refine ⟨7498671389072214063647195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999114259381476042431463 7498671389072214063647195)
      ·
        refine ⟨11248007083608321095470793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7498671389072214063647195 11248007083608321095470793)
        ·
          refine ⟨8436005312706240821603095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11248007083608321095470793 8436005312706240821603095)
          ·
            refine ⟨12654007969059361232404643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8436005312706240821603095 12654007969059361232404643)
            ·
              refine ⟨18981011953589041848606965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12654007969059361232404643 18981011953589041848606965)
              ·
                refine ⟨1779469870648972673306903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18981011953589041848606965 1779469870648972673306903)
                ·
                  refine ⟨2669204805973459009960355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779469870648972673306903 2669204805973459009960355)
                  ·
                    refine ⟨4003807208960188514940533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2669204805973459009960355 4003807208960188514940533)
                    ·
                      refine ⟨375356925840017673275675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4003807208960188514940533 375356925840017673275675)
                      ·
                        rfl

theorem cell23_731005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_731005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731005 prefixEnd_731005 := by exact prefixLift 731005
  have htrace : WordTrace (prefixWord ++ tailWord_731005) baseStart_731005 baseEnd_731005 := by
    simpa [prefixWord, tailWord_731005, baseEnd_731005] using wordTrace_append hprefix tailTrace_731005
  have hstable : (prefixWord ++ tailWord_731005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731005).length < 2 ^ (prefixWord ++ tailWord_731005).sum := by decide
  have hdescent : baseEnd_731005 < baseStart_731005 := by decide
  rcases family_descends (prefixWord ++ tailWord_731005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731008 : List Nat := [2, 1, 1, 2, 1, 2, 14]
def baseStart_731008 : Nat := 118140960795 + 731008 * 2 ^ 59
def prefixEnd_731008 : Nat := 4983230072969 + 3 ^ 40 * 731008 * 2
def baseEnd_731008 : Nat := 4634055139283718043681

theorem tailTrace_731008 : CollatzResearch.WordTrace tailWord_731008 prefixEnd_731008 4634055139283718043681 := by
  unfold tailWord_731008
  simp only [CollatzResearch.WordTrace]
  refine ⟨13331026067845168535996839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17774701423793558047995785 13331026067845168535996839)
  ·
    refine ⟨19996539101767752803995259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13331026067845168535996839 19996539101767752803995259)
    ·
      refine ⟨29994808652651629205992889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19996539101767752803995259 29994808652651629205992889)
      ·
        refine ⟨22496106489488721904494667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29994808652651629205992889 22496106489488721904494667)
        ·
          refine ⟨33744159734233082856742001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22496106489488721904494667 33744159734233082856742001)
          ·
            refine ⟨25308119800674812142556501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33744159734233082856742001 25308119800674812142556501)
            ·
              refine ⟨4634055139283718043681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 25308119800674812142556501 4634055139283718043681)
              ·
                rfl

theorem cell23_731008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 14].length) (baseStart_731008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731008 prefixEnd_731008 := by exact prefixLift 731008
  have htrace : WordTrace (prefixWord ++ tailWord_731008) baseStart_731008 baseEnd_731008 := by
    simpa [prefixWord, tailWord_731008, baseEnd_731008] using wordTrace_append hprefix tailTrace_731008
  have hstable : (prefixWord ++ tailWord_731008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731008).length < 2 ^ (prefixWord ++ tailWord_731008).sum := by decide
  have hdescent : baseEnd_731008 < baseStart_731008 := by decide
  rcases family_descends (prefixWord ++ tailWord_731008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731029 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 2, 4]
def baseStart_731029 : Nat := 118140960795 + 731029 * 2 ^ 59
def prefixEnd_731029 : Nat := 4983230072969 + 3 ^ 40 * 731029 * 2
def baseEnd_731029 : Nat := 125123083125241859791855

theorem tailTrace_731029 : CollatzResearch.WordTrace tailWord_731029 prefixEnd_731029 125123083125241859791855 := by
  unfold tailWord_731029
  simp only [CollatzResearch.WordTrace]
  refine ⟨26662818068614257658508141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17775212045742838439005427 26662818068614257658508141)
  ·
    refine ⟨9998556775730346621940553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26662818068614257658508141 9998556775730346621940553)
    ·
      refine ⟨7498917581797759966455415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9998556775730346621940553 7498917581797759966455415)
      ·
        refine ⟨11248376372696639949683123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7498917581797759966455415 11248376372696639949683123)
        ·
          refine ⟨16872564559044959924524685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11248376372696639949683123 16872564559044959924524685)
          ·
            refine ⟨6327211709641859971696757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16872564559044959924524685 6327211709641859971696757)
            ·
              refine ⟨593176097778924372346571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6327211709641859971696757 593176097778924372346571)
              ·
                refine ⟨889764146668386558519857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593176097778924372346571 889764146668386558519857)
                ·
                  refine ⟨667323110001289918889893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 889764146668386558519857 667323110001289918889893)
                  ·
                    refine ⟨125123083125241859791855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 667323110001289918889893 125123083125241859791855)
                    ·
                      rfl

theorem cell23_731029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_731029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731029 prefixEnd_731029 := by exact prefixLift 731029
  have htrace : WordTrace (prefixWord ++ tailWord_731029) baseStart_731029 baseEnd_731029 := by
    simpa [prefixWord, tailWord_731029, baseEnd_731029] using wordTrace_append hprefix tailTrace_731029
  have hstable : (prefixWord ++ tailWord_731029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731029).length < 2 ^ (prefixWord ++ tailWord_731029).sum := by decide
  have hdescent : baseEnd_731029 < baseStart_731029 := by decide
  rcases family_descends (prefixWord ++ tailWord_731029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731036 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_731036 : Nat := 118140960795 + 731036 * 2 ^ 59
def prefixEnd_731036 : Nat := 4983230072969 + 3 ^ 40 * 731036 * 2
def baseEnd_731036 : Nat := 375372843740307051988033

theorem tailTrace_731036 : CollatzResearch.WordTrace tailWord_731036 prefixEnd_731036 375372843740307051988033 := by
  unfold tailWord_731036
  simp only [CollatzResearch.WordTrace]
  refine ⟨13331536689794448927006481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17775382253059265236008641 13331536689794448927006481)
  ·
    refine ⟨9998652517345836695254861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13331536689794448927006481 9998652517345836695254861)
    ·
      refine ⟨3749494694004688760720573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9998652517345836695254861 3749494694004688760720573)
      ·
        refine ⟨1406060510251758285270215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3749494694004688760720573 1406060510251758285270215)
        ·
          refine ⟨2109090765377637427905323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406060510251758285270215 2109090765377637427905323)
          ·
            refine ⟨3163636148066456141857985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109090765377637427905323 3163636148066456141857985)
            ·
              refine ⟨2372727111049842106393489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3163636148066456141857985 2372727111049842106393489)
              ·
                refine ⟨1779545333287381579795117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372727111049842106393489 1779545333287381579795117)
                ·
                  refine ⟨667329499982768092423169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1779545333287381579795117 667329499982768092423169)
                  ·
                    refine ⟨500497124987076069317377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 667329499982768092423169 500497124987076069317377)
                    ·
                      refine ⟨375372843740307051988033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500497124987076069317377 375372843740307051988033)
                      ·
                        rfl

theorem cell23_731036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_731036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731036 prefixEnd_731036 := by exact prefixLift 731036
  have htrace : WordTrace (prefixWord ++ tailWord_731036) baseStart_731036 baseEnd_731036 := by
    simpa [prefixWord, tailWord_731036, baseEnd_731036] using wordTrace_append hprefix tailTrace_731036
  have hstable : (prefixWord ++ tailWord_731036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731036).length < 2 ^ (prefixWord ++ tailWord_731036).sum := by decide
  have hdescent : baseEnd_731036 < baseStart_731036 := by decide
  rcases family_descends (prefixWord ++ tailWord_731036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731042 : List Nat := [3, 3, 1, 2, 3, 1, 1, 9]
def baseStart_731042 : Nat := 118140960795 + 731042 * 2 ^ 59
def prefixEnd_731042 : Nat := 4983230072969 + 3 ^ 40 * 731042 * 2
def baseEnd_731042 : Nat := 13902812023119778833815

theorem tailTrace_731042 : CollatzResearch.WordTrace tailWord_731042 prefixEnd_731042 13902812023119778833815 := by
  unfold tailWord_731042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6665823054391790219682845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17775528145044773919154253 6665823054391790219682845)
  ·
    refine ⟨2499683645396921332381067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6665823054391790219682845 2499683645396921332381067)
    ·
      refine ⟨3749525468095381998571601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2499683645396921332381067 3749525468095381998571601)
      ·
        refine ⟨2812144101071536498928701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3749525468095381998571601 2812144101071536498928701)
        ·
          refine ⟨1054554037901826187098263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2812144101071536498928701 1054554037901826187098263)
          ·
            refine ⟨1581831056852739280647395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054554037901826187098263 1581831056852739280647395)
            ·
              refine ⟨2372746585279108920971093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581831056852739280647395 2372746585279108920971093)
              ·
                refine ⟨13902812023119778833815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2372746585279108920971093 13902812023119778833815)
                ·
                  rfl

theorem cell23_731042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 9].length) (baseStart_731042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731042 prefixEnd_731042 := by exact prefixLift 731042
  have htrace : WordTrace (prefixWord ++ tailWord_731042) baseStart_731042 baseEnd_731042 := by
    simpa [prefixWord, tailWord_731042, baseEnd_731042] using wordTrace_append hprefix tailTrace_731042
  have hstable : (prefixWord ++ tailWord_731042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731042).length < 2 ^ (prefixWord ++ tailWord_731042).sum := by decide
  have hdescent : baseEnd_731042 < baseStart_731042 := by decide
  rcases family_descends (prefixWord ++ tailWord_731042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731065 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_731065 : Nat := 118140960795 + 731065 * 2 ^ 59
def prefixEnd_731065 : Nat := 4983230072969 + 3 ^ 40 * 731065 * 2
def baseEnd_731065 : Nat := 375387734679287438525399

theorem tailTrace_731065 : CollatzResearch.WordTrace tailWord_731065 prefixEnd_731065 375387734679287438525399 := by
  unfold tailWord_731065
  simp only [CollatzResearch.WordTrace]
  refine ⟨26664131096483835806818649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17776087397655890537879099 26664131096483835806818649)
  ·
    refine ⟨19998098322362876855113987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26664131096483835806818649 19998098322362876855113987)
    ·
      refine ⟨29997147483544315282670981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19998098322362876855113987 29997147483544315282670981)
      ·
        refine ⟨5624465153164559115500809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29997147483544315282670981 5624465153164559115500809)
        ·
          refine ⟨4218348864873419336625607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5624465153164559115500809 4218348864873419336625607)
          ·
            refine ⟨6327523297310129004938411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4218348864873419336625607 6327523297310129004938411)
            ·
              refine ⟨9491284945965193507407617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6327523297310129004938411 9491284945965193507407617)
              ·
                refine ⟨7118463709473895130555713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9491284945965193507407617 7118463709473895130555713)
                ·
                  refine ⟨5338847782105421347916785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7118463709473895130555713 5338847782105421347916785)
                  ·
                    refine ⟨4004135836579066010937589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5338847782105421347916785 4004135836579066010937589)
                    ·
                      refine ⟨375387734679287438525399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4004135836579066010937589 375387734679287438525399)
                      ·
                        rfl

theorem cell23_731065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_731065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731065 prefixEnd_731065 := by exact prefixLift 731065
  have htrace : WordTrace (prefixWord ++ tailWord_731065) baseStart_731065 baseEnd_731065 := by
    simpa [prefixWord, tailWord_731065, baseEnd_731065] using wordTrace_append hprefix tailTrace_731065
  have hstable : (prefixWord ++ tailWord_731065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731065).length < 2 ^ (prefixWord ++ tailWord_731065).sum := by decide
  have hdescent : baseEnd_731065 < baseStart_731065 := by decide
  rcases family_descends (prefixWord ++ tailWord_731065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731069 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_731069 : Nat := 118140960795 + 731069 * 2 ^ 59
def prefixEnd_731069 : Nat := 4983230072969 + 3 ^ 40 * 731069 * 2
def baseEnd_731069 : Nat := 375389788601905422875381

theorem tailTrace_731069 : CollatzResearch.WordTrace tailWord_731069 prefixEnd_731069 375389788601905422875381 := by
  unfold tailWord_731069
  simp only [CollatzResearch.WordTrace]
  refine ⟨26664276988469344489964261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17776184658979562993309507 26664276988469344489964261)
  ·
    refine ⟨4999551935338002091868299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26664276988469344489964261 4999551935338002091868299)
    ·
      refine ⟨7499327903007003137802449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999551935338002091868299 7499327903007003137802449)
      ·
        refine ⟨5624495927255252353351837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7499327903007003137802449 5624495927255252353351837)
        ·
          refine ⟨2109185972720719632506939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5624495927255252353351837 2109185972720719632506939)
          ·
            refine ⟨3163778959081079448760409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109185972720719632506939 3163778959081079448760409)
            ·
              refine ⟨2372834219310809586570307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3163778959081079448760409 2372834219310809586570307)
              ·
                refine ⟨3559251328966214379855461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2372834219310809586570307 3559251328966214379855461)
                ·
                  refine ⟨667359624181165196222899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3559251328966214379855461 667359624181165196222899)
                  ·
                    refine ⟨1001039436271747794334349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 667359624181165196222899 1001039436271747794334349)
                    ·
                      refine ⟨375389788601905422875381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1001039436271747794334349 375389788601905422875381)
                      ·
                        rfl

theorem cell23_731069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_731069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731069 prefixEnd_731069 := by exact prefixLift 731069
  have htrace : WordTrace (prefixWord ++ tailWord_731069) baseStart_731069 baseEnd_731069 := by
    simpa [prefixWord, tailWord_731069, baseEnd_731069] using wordTrace_append hprefix tailTrace_731069
  have hstable : (prefixWord ++ tailWord_731069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731069).length < 2 ^ (prefixWord ++ tailWord_731069).sum := by decide
  have hdescent : baseEnd_731069 < baseStart_731069 := by decide
  rcases family_descends (prefixWord ++ tailWord_731069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731070 : List Nat := [4, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_731070 : Nat := 118140960795 + 731070 * 2 ^ 59
def prefixEnd_731070 : Nat := 4983230072969 + 3 ^ 40 * 731070 * 2
def baseEnd_731070 : Nat := 375390302082559918962877

theorem tailTrace_731070 : CollatzResearch.WordTrace tailWord_731070 prefixEnd_731070 375390302082559918962877 := by
  unfold tailWord_731070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333039182683215207593833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17776208974310481107167109 3333039182683215207593833)
  ·
    refine ⟨2499779387012411405695375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3333039182683215207593833 2499779387012411405695375)
    ·
      refine ⟨3749669080518617108543063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2499779387012411405695375 3749669080518617108543063)
      ·
        refine ⟨5624503620777925662814595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3749669080518617108543063 5624503620777925662814595)
        ·
          refine ⟨8436755431166888494221893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624503620777925662814595 8436755431166888494221893)
          ·
            refine ⟨1581891643343791592666605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8436755431166888494221893 1581891643343791592666605)
            ·
              refine ⟨593209366253921847249977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1581891643343791592666605 593209366253921847249977)
              ·
                refine ⟨444907024690441385437483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593209366253921847249977 444907024690441385437483)
                ·
                  refine ⟨667360537035662078156225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444907024690441385437483 667360537035662078156225)
                  ·
                    refine ⟨500520402776746558617169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 667360537035662078156225 500520402776746558617169)
                    ·
                      refine ⟨375390302082559918962877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500520402776746558617169 375390302082559918962877)
                      ·
                        rfl

theorem cell23_731070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_731070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731070 prefixEnd_731070 := by exact prefixLift 731070
  have htrace : WordTrace (prefixWord ++ tailWord_731070) baseStart_731070 baseEnd_731070 := by
    simpa [prefixWord, tailWord_731070, baseEnd_731070] using wordTrace_append hprefix tailTrace_731070
  have hstable : (prefixWord ++ tailWord_731070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731070).length < 2 ^ (prefixWord ++ tailWord_731070).sum := by decide
  have hdescent : baseEnd_731070 < baseStart_731070 := by decide
  rcases family_descends (prefixWord ++ tailWord_731070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731095 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_731095 : Nat := 118140960795 + 731095 * 2 ^ 59
def prefixEnd_731095 : Nat := 4983230072969 + 3 ^ 40 * 731095 * 2
def baseEnd_731095 : Nat := 375403139098922321150261

theorem tailTrace_731095 : CollatzResearch.WordTrace tailWord_731095 prefixEnd_731095 375403139098922321150261 := by
  unfold tailWord_731095
  simp only [CollatzResearch.WordTrace]
  refine ⟨26665225286375150930410739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17776816857583433953607159 26665225286375150930410739)
  ·
    refine ⟨39997837929562726395616109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26665225286375150930410739 39997837929562726395616109)
    ·
      refine ⟨14999189223586022398356041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39997837929562726395616109 14999189223586022398356041)
      ·
        refine ⟨11249391917689516798767031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14999189223586022398356041 11249391917689516798767031)
        ·
          refine ⟨16874087876534275198150547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11249391917689516798767031 16874087876534275198150547)
          ·
            refine ⟨25311131814801412797225821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16874087876534275198150547 25311131814801412797225821)
            ·
              refine ⟨9491674430550529798959683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25311131814801412797225821 9491674430550529798959683)
              ·
                refine ⟨14237511645825794698439525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9491674430550529798959683 14237511645825794698439525)
                ·
                  refine ⟨2669533433592336505957411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14237511645825794698439525 2669533433592336505957411)
                  ·
                    refine ⟨4004300150388504758936117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2669533433592336505957411 4004300150388504758936117)
                    ·
                      refine ⟨375403139098922321150261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4004300150388504758936117 375403139098922321150261)
                      ·
                        rfl

theorem cell23_731095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_731095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731095 prefixEnd_731095 := by exact prefixLift 731095
  have htrace : WordTrace (prefixWord ++ tailWord_731095) baseStart_731095 baseEnd_731095 := by
    simpa [prefixWord, tailWord_731095, baseEnd_731095] using wordTrace_append hprefix tailTrace_731095
  have hstable : (prefixWord ++ tailWord_731095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731095).length < 2 ^ (prefixWord ++ tailWord_731095).sum := by decide
  have hdescent : baseEnd_731095 < baseStart_731095 := by decide
  rcases family_descends (prefixWord ++ tailWord_731095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731155 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 7]
def baseStart_731155 : Nat := 118140960795 + 731155 * 2 ^ 59
def prefixEnd_731155 : Nat := 4983230072969 + 3 ^ 40 * 731155 * 2
def baseEnd_731155 : Nat := 375433947938192086399985

theorem tailTrace_731155 : CollatzResearch.WordTrace tailWord_731155 prefixEnd_731155 375433947938192086399985 := by
  unfold tailWord_731155
  simp only [CollatzResearch.WordTrace]
  refine ⟨26667413666157781177594919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17778275777438520785063279 26667413666157781177594919)
  ·
    refine ⟨40001120499236671766392379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26667413666157781177594919 40001120499236671766392379)
    ·
      refine ⟨60001680748855007649588569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40001120499236671766392379 60001680748855007649588569)
      ·
        refine ⟨45001260561641255737191427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60001680748855007649588569 45001260561641255737191427)
        ·
          refine ⟨67501890842461883605787141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45001260561641255737191427 67501890842461883605787141)
          ·
            refine ⟨12656604532961603176085089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67501890842461883605787141 12656604532961603176085089)
            ·
              refine ⟨9492453399721202382063817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12656604532961603176085089 9492453399721202382063817)
              ·
                refine ⟨7119340049790901786547863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9492453399721202382063817 7119340049790901786547863)
                ·
                  refine ⟨10679010074686352679821795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7119340049790901786547863 10679010074686352679821795)
                  ·
                    refine ⟨16018515112029529019732693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10679010074686352679821795 16018515112029529019732693)
                    ·
                      refine ⟨375433947938192086399985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16018515112029529019732693 375433947938192086399985)
                      ·
                        rfl

theorem cell23_731155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_731155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731155 prefixEnd_731155 := by exact prefixLift 731155
  have htrace : WordTrace (prefixWord ++ tailWord_731155) baseStart_731155 baseEnd_731155 := by
    simpa [prefixWord, tailWord_731155, baseEnd_731155] using wordTrace_append hprefix tailTrace_731155
  have hstable : (prefixWord ++ tailWord_731155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731155).length < 2 ^ (prefixWord ++ tailWord_731155).sum := by decide
  have hdescent : baseEnd_731155 < baseStart_731155 := by decide
  rcases family_descends (prefixWord ++ tailWord_731155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731162 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_731162 : Nat := 118140960795 + 731162 * 2 ^ 59
def prefixEnd_731162 : Nat := 4983230072969 + 3 ^ 40 * 731162 * 2
def baseEnd_731162 : Nat := 125145847434257853004151

theorem tailTrace_731162 : CollatzResearch.WordTrace tailWord_731162 prefixEnd_731162 125145847434257853004151 := by
  unfold tailWord_731162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6666917244283105343274935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17778445984754947582066493 6666917244283105343274935)
  ·
    refine ⟨10000375866424658014912403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6666917244283105343274935 10000375866424658014912403)
    ·
      refine ⟨15000563799636987022368605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10000375866424658014912403 15000563799636987022368605)
      ·
        refine ⟨5625211424863870133388227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15000563799636987022368605 5625211424863870133388227)
        ·
          refine ⟨8437817137295805200082341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5625211424863870133388227 8437817137295805200082341)
          ·
            refine ⟨1582090713242963475015439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8437817137295805200082341 1582090713242963475015439)
            ·
              refine ⟨2373136069864445212523159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582090713242963475015439 2373136069864445212523159)
              ·
                refine ⟨3559704104796667818784739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373136069864445212523159 3559704104796667818784739)
                ·
                  refine ⟨5339556157195001728177109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559704104796667818784739 5339556157195001728177109)
                  ·
                    refine ⟨125145847434257853004151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5339556157195001728177109 125145847434257853004151)
                    ·
                      rfl

theorem cell23_731162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_731162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731162 prefixEnd_731162 := by exact prefixLift 731162
  have htrace : WordTrace (prefixWord ++ tailWord_731162) baseStart_731162 baseEnd_731162 := by
    simpa [prefixWord, tailWord_731162, baseEnd_731162] using wordTrace_append hprefix tailTrace_731162
  have hstable : (prefixWord ++ tailWord_731162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731162).length < 2 ^ (prefixWord ++ tailWord_731162).sum := by decide
  have hdescent : baseEnd_731162 < baseStart_731162 := by decide
  rcases family_descends (prefixWord ++ tailWord_731162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731199 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 2, 4, 2]
def baseStart_731199 : Nat := 118140960795 + 731199 * 2 ^ 59
def prefixEnd_731199 : Nat := 4983230072969 + 3 ^ 40 * 731199 * 2
def baseEnd_731199 : Nat := 375456541086989914249783

theorem tailTrace_731199 : CollatzResearch.WordTrace tailWord_731199 prefixEnd_731199 375456541086989914249783 := by
  unfold tailWord_731199
  simp only [CollatzResearch.WordTrace]
  refine ⟨26669018477998376692196651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17779345651998917794797767 26669018477998376692196651)
  ·
    refine ⟨40003527716997565038294977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26669018477998376692196651 40003527716997565038294977)
    ·
      refine ⟨30002645787748173778721233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40003527716997565038294977 30002645787748173778721233)
      ·
        refine ⟨22501984340811130334040925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30002645787748173778721233 22501984340811130334040925)
        ·
          refine ⟨8438244127804173875265347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22501984340811130334040925 8438244127804173875265347)
          ·
            refine ⟨12657366191706260812898021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8438244127804173875265347 12657366191706260812898021)
            ·
              refine ⟨2373256160944923902418379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12657366191706260812898021 2373256160944923902418379)
              ·
                refine ⟨3559884241417385853627569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373256160944923902418379 3559884241417385853627569)
                ·
                  refine ⟨2669913181063039390220677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3559884241417385853627569 2669913181063039390220677)
                  ·
                    refine ⟨500608721449319885666377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2669913181063039390220677 500608721449319885666377)
                    ·
                      refine ⟨375456541086989914249783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500608721449319885666377 375456541086989914249783)
                      ·
                        rfl

theorem cell23_731199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 4, 2].length) (baseStart_731199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731199 prefixEnd_731199 := by exact prefixLift 731199
  have htrace : WordTrace (prefixWord ++ tailWord_731199) baseStart_731199 baseEnd_731199 := by
    simpa [prefixWord, tailWord_731199, baseEnd_731199] using wordTrace_append hprefix tailTrace_731199
  have hstable : (prefixWord ++ tailWord_731199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731199).length < 2 ^ (prefixWord ++ tailWord_731199).sum := by decide
  have hdescent : baseEnd_731199 < baseStart_731199 := by decide
  rcases family_descends (prefixWord ++ tailWord_731199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731269 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_731269 : Nat := 118140960795 + 731269 * 2 ^ 59
def prefixEnd_731269 : Nat := 4983230072969 + 3 ^ 40 * 731269 * 2
def baseEnd_731269 : Nat := 125164161577601546791487

theorem tailTrace_731269 : CollatzResearch.WordTrace tailWord_731269 prefixEnd_731269 125164161577601546791487 := by
  unfold tailWord_731269
  simp only [CollatzResearch.WordTrace]
  refine ⟨26671571587744778647244861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17781047725163185764829907 26671571587744778647244861)
  ·
    refine ⟨10001839345404291992716823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26671571587744778647244861 10001839345404291992716823)
    ·
      refine ⟨15002759018106437989075235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10001839345404291992716823 15002759018106437989075235)
      ·
        refine ⟨22504138527159656983612853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15002759018106437989075235 22504138527159656983612853)
        ·
          refine ⟨2109762986921217842213705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22504138527159656983612853 2109762986921217842213705)
          ·
            refine ⟨1582322240190913381660279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2109762986921217842213705 1582322240190913381660279)
            ·
              refine ⟨2373483360286370072490419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582322240190913381660279 2373483360286370072490419)
              ·
                refine ⟨3560225040429555108735629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373483360286370072490419 3560225040429555108735629)
                ·
                  refine ⟨1335084390161083165775861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3560225040429555108735629 1335084390161083165775861)
                  ·
                    refine ⟨125164161577601546791487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1335084390161083165775861 125164161577601546791487)
                    ·
                      rfl

theorem cell23_731269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_731269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731269 prefixEnd_731269 := by exact prefixLift 731269
  have htrace : WordTrace (prefixWord ++ tailWord_731269) baseStart_731269 baseEnd_731269 := by
    simpa [prefixWord, tailWord_731269, baseEnd_731269] using wordTrace_append hprefix tailTrace_731269
  have hstable : (prefixWord ++ tailWord_731269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731269).length < 2 ^ (prefixWord ++ tailWord_731269).sum := by decide
  have hdescent : baseEnd_731269 < baseStart_731269 := by decide
  rcases family_descends (prefixWord ++ tailWord_731269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731289 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 4]
def baseStart_731289 : Nat := 118140960795 + 731289 * 2 ^ 59
def prefixEnd_731289 : Nat := 4983230072969 + 3 ^ 40 * 731289 * 2
def baseEnd_731289 : Nat := 375502754345894562124369

theorem tailTrace_731289 : CollatzResearch.WordTrace tailWord_731289 prefixEnd_731289 375502754345894562124369 := by
  unfold tailWord_731289
  simp only [CollatzResearch.WordTrace]
  refine ⟨26672301047672322062972921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17781534031781548041981947 26672301047672322062972921)
  ·
    refine ⟨20004225785754241547229691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26672301047672322062972921 20004225785754241547229691)
    ·
      refine ⟨30006338678631362320844537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20004225785754241547229691 30006338678631362320844537)
      ·
        refine ⟨22504754008973521740633403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30006338678631362320844537 22504754008973521740633403)
        ·
          refine ⟨33757131013460282610950105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22504754008973521740633403 33757131013460282610950105)
          ·
            refine ⟨25317848260095211958212579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33757131013460282610950105 25317848260095211958212579)
            ·
              refine ⟨37976772390142817937318869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25317848260095211958212579 37976772390142817937318869)
              ·
                refine ⟨890080602893972295405911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37976772390142817937318869 890080602893972295405911)
                ·
                  refine ⟨1335120904340958443108867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 890080602893972295405911 1335120904340958443108867)
                  ·
                    refine ⟨2002681356511437664663301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1335120904340958443108867 2002681356511437664663301)
                    ·
                      refine ⟨375502754345894562124369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2002681356511437664663301 375502754345894562124369)
                      ·
                        rfl

theorem cell23_731289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_731289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731289 prefixEnd_731289 := by exact prefixLift 731289
  have htrace : WordTrace (prefixWord ++ tailWord_731289) baseStart_731289 baseEnd_731289 := by
    simpa [prefixWord, tailWord_731289, baseEnd_731289] using wordTrace_append hprefix tailTrace_731289
  have hstable : (prefixWord ++ tailWord_731289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731289).length < 2 ^ (prefixWord ++ tailWord_731289).sum := by decide
  have hdescent : baseEnd_731289 < baseStart_731289 := by decide
  rcases family_descends (prefixWord ++ tailWord_731289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731294 : List Nat := [4, 3, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_731294 : Nat := 118140960795 + 731294 * 2 ^ 59
def prefixEnd_731294 : Nat := 4983230072969 + 3 ^ 40 * 731294 * 2
def baseEnd_731294 : Nat := 125168440583055680853949

theorem tailTrace_731294 : CollatzResearch.WordTrace tailWord_731294 prefixEnd_731294 125168440583055680853949 := by
  unfold tailWord_731294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334060426581775989613117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17781655608436138611269957 3334060426581775989613117)
  ·
    refine ⟨1250272659968165996104919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3334060426581775989613117 1250272659968165996104919)
    ·
      refine ⟨1875408989952248994157379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250272659968165996104919 1875408989952248994157379)
      ·
        refine ⟨2813113484928373491236069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875408989952248994157379 2813113484928373491236069)
        ·
          refine ⟨527458778424070029606763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2813113484928373491236069 527458778424070029606763)
          ·
            refine ⟨791188167636105044410145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527458778424070029606763 791188167636105044410145)
            ·
              refine ⟨593391125727078783307609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791188167636105044410145 593391125727078783307609)
              ·
                refine ⟨445043344295309087480707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593391125727078783307609 445043344295309087480707)
                ·
                  refine ⟨667565016442963631221061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445043344295309087480707 667565016442963631221061)
                  ·
                    refine ⟨125168440583055680853949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 667565016442963631221061 125168440583055680853949)
                    ·
                      rfl

theorem cell23_731294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_731294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731294 prefixEnd_731294 := by exact prefixLift 731294
  have htrace : WordTrace (prefixWord ++ tailWord_731294) baseStart_731294 baseEnd_731294 := by
    simpa [prefixWord, tailWord_731294, baseEnd_731294] using wordTrace_append hprefix tailTrace_731294
  have hstable : (prefixWord ++ tailWord_731294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731294).length < 2 ^ (prefixWord ++ tailWord_731294).sum := by decide
  have hdescent : baseEnd_731294 < baseStart_731294 := by decide
  rcases family_descends (prefixWord ++ tailWord_731294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731300 : List Nat := [2, 3, 1, 2, 4, 1, 1, 4, 1, 1, 3]
def baseStart_731300 : Nat := 118140960795 + 731300 * 2 ^ 59
def prefixEnd_731300 : Nat := 4983230072969 + 3 ^ 40 * 731300 * 2
def baseEnd_731300 : Nat := 375508402633094019086819

theorem tailTrace_731300 : CollatzResearch.WordTrace tailWord_731300 prefixEnd_731300 375508402633094019086819 := by
  unfold tailWord_731300
  simp only [CollatzResearch.WordTrace]
  refine ⟨13336351125316235470811677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17781801500421647294415569 13336351125316235470811677)
  ·
    refine ⟨5001131671993588301554379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13336351125316235470811677 5001131671993588301554379)
    ·
      refine ⟨7501697507990382452331569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5001131671993588301554379 7501697507990382452331569)
      ·
        refine ⟨5626273130992786839248677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7501697507990382452331569 5626273130992786839248677)
        ·
          refine ⟨1054926212061147532359127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5626273130992786839248677 1054926212061147532359127)
          ·
            refine ⟨1582389318091721298538691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054926212061147532359127 1582389318091721298538691)
            ·
              refine ⟨2373583977137581947808037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582389318091721298538691 2373583977137581947808037)
              ·
                refine ⟨445046995713296615214007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2373583977137581947808037 445046995713296615214007)
                ·
                  refine ⟨667570493569944922821011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445046995713296615214007 667570493569944922821011)
                  ·
                    refine ⟨1001355740354917384231517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 667570493569944922821011 1001355740354917384231517)
                    ·
                      refine ⟨375508402633094019086819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1001355740354917384231517 375508402633094019086819)
                      ·
                        rfl

theorem cell23_731300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_731300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731300 prefixEnd_731300 := by exact prefixLift 731300
  have htrace : WordTrace (prefixWord ++ tailWord_731300) baseStart_731300 baseEnd_731300 := by
    simpa [prefixWord, tailWord_731300, baseEnd_731300] using wordTrace_append hprefix tailTrace_731300
  have hstable : (prefixWord ++ tailWord_731300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731300).length < 2 ^ (prefixWord ++ tailWord_731300).sum := by decide
  have hdescent : baseEnd_731300 < baseStart_731300 := by decide
  rcases family_descends (prefixWord ++ tailWord_731300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731319 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_731319 : Nat := 118140960795 + 731319 * 2 ^ 59
def prefixEnd_731319 : Nat := 4983230072969 + 3 ^ 40 * 731319 * 2
def baseEnd_731319 : Nat := 375518158765529444749231

theorem tailTrace_731319 : CollatzResearch.WordTrace tailWord_731319 prefixEnd_731319 375518158765529444749231 := by
  unfold tailWord_731319
  simp only [CollatzResearch.WordTrace]
  refine ⟨26673395237563637186565011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17782263491709091457710007 26673395237563637186565011)
  ·
    refine ⟨40010092856345455779847517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26673395237563637186565011 40010092856345455779847517)
    ·
      refine ⟨15003784821129545917442819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40010092856345455779847517 15003784821129545917442819)
      ·
        refine ⟨22505677231694318876164229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15003784821129545917442819 22505677231694318876164229)
        ·
          refine ⟨4219814480942684789280793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22505677231694318876164229 4219814480942684789280793)
          ·
            refine ⟨3164860860707013591960595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4219814480942684789280793 3164860860707013591960595)
            ·
              refine ⟨4747291291060520387940893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164860860707013591960595 4747291291060520387940893)
              ·
                refine ⟨1780234234147695145477835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4747291291060520387940893 1780234234147695145477835)
                ·
                  refine ⟨2670351351221542718216753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780234234147695145477835 2670351351221542718216753)
                  ·
                    refine ⟨2002763513416157038662565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2670351351221542718216753 2002763513416157038662565)
                    ·
                      refine ⟨375518158765529444749231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2002763513416157038662565 375518158765529444749231)
                      ·
                        rfl

theorem cell23_731319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_731319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731319 prefixEnd_731319 := by exact prefixLift 731319
  have htrace : WordTrace (prefixWord ++ tailWord_731319) baseStart_731319 baseEnd_731319 := by
    simpa [prefixWord, tailWord_731319, baseEnd_731319] using wordTrace_append hprefix tailTrace_731319
  have hstable : (prefixWord ++ tailWord_731319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731319).length < 2 ^ (prefixWord ++ tailWord_731319).sum := by decide
  have hdescent : baseEnd_731319 < baseStart_731319 := by decide
  rcases family_descends (prefixWord ++ tailWord_731319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731339 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 3]
def baseStart_731339 : Nat := 118140960795 + 731339 * 2 ^ 59
def prefixEnd_731339 : Nat := 4983230072969 + 3 ^ 40 * 731339 * 2
def baseEnd_731339 : Nat := 375528428378619366499139

theorem tailTrace_731339 : CollatzResearch.WordTrace tailWord_731339 prefixEnd_731339 375528428378619366499139 := by
  unfold tailWord_731339
  simp only [CollatzResearch.WordTrace]
  refine ⟨26674124697491180602293071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17782749798327453734862047 26674124697491180602293071)
  ·
    refine ⟨40011187046236770903439607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26674124697491180602293071 40011187046236770903439607)
    ·
      refine ⟨60016780569355156355159411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40011187046236770903439607 60016780569355156355159411)
      ·
        refine ⟨90025170854032734532739117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60016780569355156355159411 90025170854032734532739117)
        ·
          refine ⟨33759439070262275449777169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90025170854032734532739117 33759439070262275449777169)
          ·
            refine ⟨25319579302696706587332877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33759439070262275449777169 25319579302696706587332877)
            ·
              refine ⟨9494842238511264970249829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25319579302696706587332877 9494842238511264970249829)
              ·
                refine ⟨1780282919720862181921843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9494842238511264970249829 1780282919720862181921843)
                ·
                  refine ⟨2670424379581293272882765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780282919720862181921843 2670424379581293272882765)
                  ·
                    refine ⟨1001409142342984977331037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2670424379581293272882765 1001409142342984977331037)
                    ·
                      refine ⟨375528428378619366499139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1001409142342984977331037 375528428378619366499139)
                      ·
                        rfl

theorem cell23_731339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 3].length) (baseStart_731339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731339 prefixEnd_731339 := by exact prefixLift 731339
  have htrace : WordTrace (prefixWord ++ tailWord_731339) baseStart_731339 baseEnd_731339 := by
    simpa [prefixWord, tailWord_731339, baseEnd_731339] using wordTrace_append hprefix tailTrace_731339
  have hstable : (prefixWord ++ tailWord_731339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731339).length < 2 ^ (prefixWord ++ tailWord_731339).sum := by decide
  have hdescent : baseEnd_731339 < baseStart_731339 := by decide
  rcases family_descends (prefixWord ++ tailWord_731339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731350 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_731350 : Nat := 118140960795 + 731350 * 2 ^ 59
def prefixEnd_731350 : Nat := 4983230072969 + 3 ^ 40 * 731350 * 2
def baseEnd_731350 : Nat := 125178025555272941153863

theorem tailTrace_731350 : CollatzResearch.WordTrace tailWord_731350 prefixEnd_731350 125178025555272941153863 := by
  unfold tailWord_731350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1667157868778208092558969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17783017266967552987295669 1667157868778208092558969)
  ·
    refine ⟨1250368401583656069419227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1667157868778208092558969 1250368401583656069419227)
    ·
      refine ⟨1875552602375484104128841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250368401583656069419227 1875552602375484104128841)
      ·
        refine ⟨1406664451781613078096631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1875552602375484104128841 1406664451781613078096631)
        ·
          refine ⟨2109996677672419617144947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406664451781613078096631 2109996677672419617144947)
          ·
            refine ⟨3164995016508629425717421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109996677672419617144947 3164995016508629425717421)
            ·
              refine ⟨1186873131190736034644033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3164995016508629425717421 1186873131190736034644033)
              ·
                refine ⟨890154848393052025983025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186873131190736034644033 890154848393052025983025)
                ·
                  refine ⟨667616136294789019487269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 890154848393052025983025 667616136294789019487269)
                  ·
                    refine ⟨125178025555272941153863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 667616136294789019487269 125178025555272941153863)
                    ·
                      rfl

theorem cell23_731350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_731350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731350 prefixEnd_731350 := by exact prefixLift 731350
  have htrace : WordTrace (prefixWord ++ tailWord_731350) baseStart_731350 baseEnd_731350 := by
    simpa [prefixWord, tailWord_731350, baseEnd_731350] using wordTrace_append hprefix tailTrace_731350
  have hstable : (prefixWord ++ tailWord_731350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731350).length < 2 ^ (prefixWord ++ tailWord_731350).sum := by decide
  have hdescent : baseEnd_731350 < baseStart_731350 := by decide
  rcases family_descends (prefixWord ++ tailWord_731350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731357 : List Nat := [1, 4, 3, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_731357 : Nat := 118140960795 + 731357 * 2 ^ 59
def prefixEnd_731357 : Nat := 4983230072969 + 3 ^ 40 * 731357 * 2
def baseEnd_731357 : Nat := 375537671030400296074057

theorem tailTrace_731357 : CollatzResearch.WordTrace tailWord_731357 prefixEnd_731357 375537671030400296074057 := by
  unfold tailWord_731357
  simp only [CollatzResearch.WordTrace]
  refine ⟨26674781211425969676448325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17783187474283979784298883 26674781211425969676448325)
  ·
    refine ⟨5001521477142369314334061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26674781211425969676448325 5001521477142369314334061)
    ·
      refine ⟨1875570553928388492875273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5001521477142369314334061 1875570553928388492875273)
      ·
        refine ⟨1406677915446291369656455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1875570553928388492875273 1406677915446291369656455)
        ·
          refine ⟨2110016873169437054484683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406677915446291369656455 2110016873169437054484683)
          ·
            refine ⟨3165025309754155581727025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110016873169437054484683 3165025309754155581727025)
            ·
              refine ⟨2373768982315616686295269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3165025309754155581727025 2373768982315616686295269)
              ·
                refine ⟨445081684184178128680363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2373768982315616686295269 445081684184178128680363)
                ·
                  refine ⟨667622526276267193020545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445081684184178128680363 667622526276267193020545)
                  ·
                    refine ⟨500716894707200394765409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 667622526276267193020545 500716894707200394765409)
                    ·
                      refine ⟨375537671030400296074057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500716894707200394765409 375537671030400296074057)
                      ·
                        rfl

theorem cell23_731357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_731357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731357 prefixEnd_731357 := by exact prefixLift 731357
  have htrace : WordTrace (prefixWord ++ tailWord_731357) baseStart_731357 baseEnd_731357 := by
    simpa [prefixWord, tailWord_731357, baseEnd_731357] using wordTrace_append hprefix tailTrace_731357
  have hstable : (prefixWord ++ tailWord_731357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731357).length < 2 ^ (prefixWord ++ tailWord_731357).sum := by decide
  have hdescent : baseEnd_731357 < baseStart_731357 := by decide
  rcases family_descends (prefixWord ++ tailWord_731357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731413 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 4, 2, 2]
def baseStart_731413 : Nat := 118140960795 + 731413 * 2 ^ 59
def prefixEnd_731413 : Nat := 4983230072969 + 3 ^ 40 * 731413 * 2
def baseEnd_731413 : Nat := 375566425947052076973799

theorem tailTrace_731413 : CollatzResearch.WordTrace tailWord_731413 prefixEnd_731413 375566425947052076973799 := by
  unfold tailWord_731413
  simp only [CollatzResearch.WordTrace]
  refine ⟨26676823699223091240486893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17784549132815394160324595 26676823699223091240486893)
  ·
    refine ⟨10003808887208659215182585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26676823699223091240486893 10003808887208659215182585)
    ·
      refine ⟨7502856665406494411386939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10003808887208659215182585 7502856665406494411386939)
      ·
        refine ⟨11254284998109741617080409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7502856665406494411386939 11254284998109741617080409)
        ·
          refine ⟨8440713748582306212810307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11254284998109741617080409 8440713748582306212810307)
          ·
            refine ⟨12661070622873459319215461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8440713748582306212810307 12661070622873459319215461)
            ·
              refine ⟨2373950741788773622352899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12661070622873459319215461 2373950741788773622352899)
              ·
                refine ⟨3560926112683160433529349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373950741788773622352899 3560926112683160433529349)
                ·
                  refine ⟨667673646128092581286753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3560926112683160433529349 667673646128092581286753)
                  ·
                    refine ⟨500755234596069435965065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 667673646128092581286753 500755234596069435965065)
                    ·
                      refine ⟨375566425947052076973799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500755234596069435965065 375566425947052076973799)
                      ·
                        rfl

theorem cell23_731413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_731413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731413 prefixEnd_731413 := by exact prefixLift 731413
  have htrace : WordTrace (prefixWord ++ tailWord_731413) baseStart_731413 baseEnd_731413 := by
    simpa [prefixWord, tailWord_731413, baseEnd_731413] using wordTrace_append hprefix tailTrace_731413
  have hstable : (prefixWord ++ tailWord_731413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731413).length < 2 ^ (prefixWord ++ tailWord_731413).sum := by decide
  have hdescent : baseEnd_731413 < baseStart_731413 := by decide
  rcases family_descends (prefixWord ++ tailWord_731413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731419 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 7]
def baseStart_731419 : Nat := 118140960795 + 731419 * 2 ^ 59
def prefixEnd_731419 : Nat := 4983230072969 + 3 ^ 40 * 731419 * 2
def baseEnd_731419 : Nat := 41729945203442117055419

theorem tailTrace_731419 : CollatzResearch.WordTrace tailWord_731419 prefixEnd_731419 41729945203442117055419 := by
  unfold tailWord_731419
  simp only [CollatzResearch.WordTrace]
  refine ⟨26677042537201354265205311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17784695024800902843470207 26677042537201354265205311)
  ·
    refine ⟨40015563805802031397807967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26677042537201354265205311 40015563805802031397807967)
    ·
      refine ⟨60023345708703047096711951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40015563805802031397807967 60023345708703047096711951)
      ·
        refine ⟨90035018563054570645067927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60023345708703047096711951 90035018563054570645067927)
        ·
          refine ⟨135052527844581855967601891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90035018563054570645067927 135052527844581855967601891)
          ·
            refine ⟨202578791766872783951402837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135052527844581855967601891 202578791766872783951402837)
            ·
              refine ⟨1186985108009020218465251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 202578791766872783951402837 1186985108009020218465251)
              ·
                refine ⟨1780477662013530327697877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186985108009020218465251 1780477662013530327697877)
                ·
                  refine ⟨41729945203442117055419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1780477662013530327697877 41729945203442117055419)
                  ·
                    rfl

theorem cell23_731419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 7].length) (baseStart_731419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731419 prefixEnd_731419 := by exact prefixLift 731419
  have htrace : WordTrace (prefixWord ++ tailWord_731419) baseStart_731419 baseEnd_731419 := by
    simpa [prefixWord, tailWord_731419, baseEnd_731419] using wordTrace_append hprefix tailTrace_731419
  have hstable : (prefixWord ++ tailWord_731419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731419).length < 2 ^ (prefixWord ++ tailWord_731419).sum := by decide
  have hdescent : baseEnd_731419 < baseStart_731419 := by decide
  rcases family_descends (prefixWord ++ tailWord_731419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731434 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_731434 : Nat := 118140960795 + 731434 * 2 ^ 59
def prefixEnd_731434 : Nat := 4983230072969 + 3 ^ 40 * 731434 * 2
def baseEnd_731434 : Nat := 375577209040796494811203

theorem tailTrace_731434 : CollatzResearch.WordTrace tailWord_731434 prefixEnd_731434 375577209040796494811203 := by
  unfold tailWord_731434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6669397408036752956750339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17785059754764674551334237 6669397408036752956750339)
  ·
    refine ⟨10004096112055129435125509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6669397408036752956750339 10004096112055129435125509)
    ·
      refine ⟨1875768021010336769086033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10004096112055129435125509 1875768021010336769086033)
      ·
        refine ⟨1406826015757752576814525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1875768021010336769086033 1406826015757752576814525)
        ·
          refine ⟨527559755909157216305447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1406826015757752576814525 527559755909157216305447)
          ·
            refine ⟨791339633863735824458171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527559755909157216305447 791339633863735824458171)
            ·
              refine ⟨1187009450795603736687257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791339633863735824458171 1187009450795603736687257)
              ·
                refine ⟨890257088096702802515443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1187009450795603736687257 890257088096702802515443)
                ·
                  refine ⟨1335385632145054203773165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 890257088096702802515443 1335385632145054203773165)
                  ·
                    refine ⟨500769612054395326414937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1335385632145054203773165 500769612054395326414937)
                    ·
                      refine ⟨375577209040796494811203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500769612054395326414937 375577209040796494811203)
                      ·
                        rfl

theorem cell23_731434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_731434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731434 prefixEnd_731434 := by exact prefixLift 731434
  have htrace : WordTrace (prefixWord ++ tailWord_731434) baseStart_731434 baseEnd_731434 := by
    simpa [prefixWord, tailWord_731434, baseEnd_731434] using wordTrace_append hprefix tailTrace_731434
  have hstable : (prefixWord ++ tailWord_731434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731434).length < 2 ^ (prefixWord ++ tailWord_731434).sum := by decide
  have hdescent : baseEnd_731434 < baseStart_731434 := by decide
  rcases family_descends (prefixWord ++ tailWord_731434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731459 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 5]
def baseStart_731459 : Nat := 118140960795 + 731459 * 2 ^ 59
def prefixEnd_731459 : Nat := 4983230072969 + 3 ^ 40 * 731459 * 2
def baseEnd_731459 : Nat := 375590046057158896998587

theorem tailTrace_731459 : CollatzResearch.WordTrace tailWord_731459 prefixEnd_731459 375590046057158896998587 := by
  unfold tailWord_731459
  simp only [CollatzResearch.WordTrace]
  refine ⟨26678501457056441096661431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17785667638037627397774287 26678501457056441096661431)
  ·
    refine ⟨40017752185584661644992147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26678501457056441096661431 40017752185584661644992147)
    ·
      refine ⟨60026628278376992467488221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40017752185584661644992147 60026628278376992467488221)
      ·
        refine ⟨22509985604391372175308083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60026628278376992467488221 22509985604391372175308083)
        ·
          refine ⟨33764978406587058262962125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22509985604391372175308083 33764978406587058262962125)
          ·
            refine ⟨12661866902470146848610797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33764978406587058262962125 12661866902470146848610797)
            ·
              refine ⟨4748200088426305068229049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12661866902470146848610797 4748200088426305068229049)
              ·
                refine ⟨3561150066319728801171787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4748200088426305068229049 3561150066319728801171787)
                ·
                  refine ⟨5341725099479593201757681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561150066319728801171787 5341725099479593201757681)
                  ·
                    refine ⟨4006293824609694901318261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5341725099479593201757681 4006293824609694901318261)
                    ·
                      refine ⟨375590046057158896998587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4006293824609694901318261 375590046057158896998587)
                      ·
                        rfl

theorem cell23_731459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_731459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731459 prefixEnd_731459 := by exact prefixLift 731459
  have htrace : WordTrace (prefixWord ++ tailWord_731459) baseStart_731459 baseEnd_731459 := by
    simpa [prefixWord, tailWord_731459, baseEnd_731459] using wordTrace_append hprefix tailTrace_731459
  have hstable : (prefixWord ++ tailWord_731459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731459).length < 2 ^ (prefixWord ++ tailWord_731459).sum := by decide
  have hdescent : baseEnd_731459 < baseStart_731459 := by decide
  rcases family_descends (prefixWord ++ tailWord_731459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731476 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_731476 : Nat := 118140960795 + 731476 * 2 ^ 59
def prefixEnd_731476 : Nat := 4983230072969 + 3 ^ 40 * 731476 * 2
def baseEnd_731476 : Nat := 375598775228285330486009

theorem tailTrace_731476 : CollatzResearch.WordTrace tailWord_731476 prefixEnd_731476 375598775228285330486009 := by
  unfold tailWord_731476
  simp only [CollatzResearch.WordTrace]
  refine ⟨13339560748997426500015141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17786080998663235333353521 13339560748997426500015141)
  ·
    refine ⟨2501167640437017468752839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13339560748997426500015141 2501167640437017468752839)
    ·
      refine ⟨3751751460655526203129259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2501167640437017468752839 3751751460655526203129259)
      ·
        refine ⟨5627627190983289304693889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751751460655526203129259 5627627190983289304693889)
        ·
          refine ⟨4220720393237466978520417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5627627190983289304693889 4220720393237466978520417)
          ·
            refine ⟨3165540294928100233890313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4220720393237466978520417 3165540294928100233890313)
            ·
              refine ⟨2374155221196075175417735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3165540294928100233890313 2374155221196075175417735)
              ·
                refine ⟨3561232831794112763126603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374155221196075175417735 3561232831794112763126603)
                ·
                  refine ⟨5341849247691169144689905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3561232831794112763126603 5341849247691169144689905)
                  ·
                    refine ⟨4006386935768376858517429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5341849247691169144689905 4006386935768376858517429)
                    ·
                      refine ⟨375598775228285330486009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4006386935768376858517429 375598775228285330486009)
                      ·
                        rfl

theorem cell23_731476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_731476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731476 prefixEnd_731476 := by exact prefixLift 731476
  have htrace : WordTrace (prefixWord ++ tailWord_731476) baseStart_731476 baseEnd_731476 := by
    simpa [prefixWord, tailWord_731476, baseEnd_731476] using wordTrace_append hprefix tailTrace_731476
  have hstable : (prefixWord ++ tailWord_731476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731476).length < 2 ^ (prefixWord ++ tailWord_731476).sum := by decide
  have hdescent : baseEnd_731476 < baseStart_731476 := by decide
  rcases family_descends (prefixWord ++ tailWord_731476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731499 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 4]
def baseStart_731499 : Nat := 118140960795 + 731499 * 2 ^ 59
def prefixEnd_731499 : Nat := 4983230072969 + 3 ^ 40 * 731499 * 2
def baseEnd_731499 : Nat := 375610585283338740498403

theorem tailTrace_731499 : CollatzResearch.WordTrace tailWord_731499 prefixEnd_731499 375610585283338740498403 := by
  unfold tailWord_731499
  simp only [CollatzResearch.WordTrace]
  refine ⟨26679960376911527928117551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17786640251274351952078367 26679960376911527928117551)
  ·
    refine ⟨40019940565367291892176327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26679960376911527928117551 40019940565367291892176327)
    ·
      refine ⟨60029910848050937838264491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40019940565367291892176327 60029910848050937838264491)
      ·
        refine ⟨90044866272076406757396737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60029910848050937838264491 90044866272076406757396737)
        ·
          refine ⟨67533649704057305068047553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90044866272076406757396737 67533649704057305068047553)
          ·
            refine ⟨50650237278042978801035665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67533649704057305068047553 50650237278042978801035665)
            ·
              refine ⟨37987677958532234100776749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50650237278042978801035665 37987677958532234100776749)
              ·
                refine ⟨14245379234449587787791281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37987677958532234100776749 14245379234449587787791281)
                ·
                  refine ⟨10684034425837190840843461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14245379234449587787791281 10684034425837190840843461)
                  ·
                    refine ⟨2003256454844473282658149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10684034425837190840843461 2003256454844473282658149)
                    ·
                      refine ⟨375610585283338740498403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2003256454844473282658149 375610585283338740498403)
                      ·
                        rfl

theorem cell23_731499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 4].length) (baseStart_731499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731499 prefixEnd_731499 := by exact prefixLift 731499
  have htrace : WordTrace (prefixWord ++ tailWord_731499) baseStart_731499 baseEnd_731499 := by
    simpa [prefixWord, tailWord_731499, baseEnd_731499] using wordTrace_append hprefix tailTrace_731499
  have hstable : (prefixWord ++ tailWord_731499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731499).length < 2 ^ (prefixWord ++ tailWord_731499).sum := by decide
  have hdescent : baseEnd_731499 < baseStart_731499 := by decide
  rcases family_descends (prefixWord ++ tailWord_731499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731500 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 2, 5]
def baseStart_731500 : Nat := 118140960795 + 731500 * 2 ^ 59
def prefixEnd_731500 : Nat := 4983230072969 + 3 ^ 40 * 731500 * 2
def baseEnd_731500 : Nat := 125203699587997745528633

theorem tailTrace_731500 : CollatzResearch.WordTrace tailWord_731500 prefixEnd_731500 125203699587997745528633 := by
  unfold tailWord_731500
  simp only [CollatzResearch.WordTrace]
  refine ⟨13339998424953952549451977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17786664566605270065935969 13339998424953952549451977)
  ·
    refine ⟨10004998818715464412088983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13339998424953952549451977 10004998818715464412088983)
    ·
      refine ⟨15007498228073196618133475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10004998818715464412088983 15007498228073196618133475)
      ·
        refine ⟨22511247342109794927200213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15007498228073196618133475 22511247342109794927200213)
        ·
          refine ⟨527607359580698318606255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 22511247342109794927200213 527607359580698318606255)
          ·
            refine ⟨791411039371047477909383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527607359580698318606255 791411039371047477909383)
            ·
              refine ⟨1187116559056571216864075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791411039371047477909383 1187116559056571216864075)
              ·
                refine ⟨1780674838584856825296113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187116559056571216864075 1780674838584856825296113)
                ·
                  refine ⟨1335506128938642618972085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1780674838584856825296113 1335506128938642618972085)
                  ·
                    refine ⟨125203699587997745528633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1335506128938642618972085 125203699587997745528633)
                    ·
                      rfl

theorem cell23_731500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_731500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731500 prefixEnd_731500 := by exact prefixLift 731500
  have htrace : WordTrace (prefixWord ++ tailWord_731500) baseStart_731500 baseEnd_731500 := by
    simpa [prefixWord, tailWord_731500, baseEnd_731500] using wordTrace_append hprefix tailTrace_731500
  have hstable : (prefixWord ++ tailWord_731500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731500).length < 2 ^ (prefixWord ++ tailWord_731500).sum := by decide
  have hdescent : baseEnd_731500 < baseStart_731500 := by decide
  rcases family_descends (prefixWord ++ tailWord_731500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731556 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_731556 : Nat := 118140960795 + 731556 * 2 ^ 59
def prefixEnd_731556 : Nat := 4983230072969 + 3 ^ 40 * 731556 * 2
def baseEnd_731556 : Nat := 125213284560215005828547

theorem tailTrace_731556 : CollatzResearch.WordTrace tailWord_731556 prefixEnd_731556 125213284560215005828547 := by
  unfold tailWord_731556
  simp only [CollatzResearch.WordTrace]
  refine ⟨13341019668852513331471261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17788026225136684441961681 13341019668852513331471261)
  ·
    refine ⟨5002882375819692499301723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13341019668852513331471261 5002882375819692499301723)
    ·
      refine ⟨7504323563729538748952585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5002882375819692499301723 7504323563729538748952585)
      ·
        refine ⟨5628242672797154061714439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7504323563729538748952585 5628242672797154061714439)
        ·
          refine ⟨8442364009195731092571659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5628242672797154061714439 8442364009195731092571659)
          ·
            refine ⟨12663546013793596638857489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8442364009195731092571659 12663546013793596638857489)
            ·
              refine ⟨9497659510345197479143117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12663546013793596638857489 9497659510345197479143117)
              ·
                refine ⟨3561622316379449054678669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9497659510345197479143117 3561622316379449054678669)
                ·
                  refine ⟨1335608368642293395504501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3561622316379449054678669 1335608368642293395504501)
                  ·
                    refine ⟨125213284560215005828547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1335608368642293395504501 125213284560215005828547)
                    ·
                      rfl

theorem cell23_731556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_731556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731556 prefixEnd_731556 := by exact prefixLift 731556
  have htrace : WordTrace (prefixWord ++ tailWord_731556) baseStart_731556 baseEnd_731556 := by
    simpa [prefixWord, tailWord_731556, baseEnd_731556] using wordTrace_append hprefix tailTrace_731556
  have hstable : (prefixWord ++ tailWord_731556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731556).length < 2 ^ (prefixWord ++ tailWord_731556).sum := by decide
  have hdescent : baseEnd_731556 < baseStart_731556 := by decide
  rcases family_descends (prefixWord ++ tailWord_731556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731576 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_731576 : Nat := 118140960795 + 731576 * 2 ^ 59
def prefixEnd_731576 : Nat := 4983230072969 + 3 ^ 40 * 731576 * 2
def baseEnd_731576 : Nat := 375650123293734939235549

theorem tailTrace_731576 : CollatzResearch.WordTrace tailWord_731576 prefixEnd_731576 375650123293734939235549 := by
  unfold tailWord_731576
  simp only [CollatzResearch.WordTrace]
  refine ⟨13341384398816285039335291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17788512531755046719113721 13341384398816285039335291)
  ·
    refine ⟨20012076598224427559002937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13341384398816285039335291 20012076598224427559002937)
    ·
      refine ⟨15009057448668320669252203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20012076598224427559002937 15009057448668320669252203)
      ·
        refine ⟨22513586173002481003878305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15009057448668320669252203 22513586173002481003878305)
        ·
          refine ⟨16885189629751860752908729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22513586173002481003878305 16885189629751860752908729)
          ·
            refine ⟨12663892222313895564681547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16885189629751860752908729 12663892222313895564681547)
            ·
              refine ⟨18995838333470843347022321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12663892222313895564681547 18995838333470843347022321)
              ·
                refine ⟨14246878750103132510266741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18995838333470843347022321 14246878750103132510266741)
                ·
                  refine ⟨1335644882822168672837507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14246878750103132510266741 1335644882822168672837507)
                  ·
                    refine ⟨2003467324233253009256261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1335644882822168672837507 2003467324233253009256261)
                    ·
                      refine ⟨375650123293734939235549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2003467324233253009256261 375650123293734939235549)
                      ·
                        rfl

theorem cell23_731576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_731576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731576 prefixEnd_731576 := by exact prefixLift 731576
  have htrace : WordTrace (prefixWord ++ tailWord_731576) baseStart_731576 baseEnd_731576 := by
    simpa [prefixWord, tailWord_731576, baseEnd_731576] using wordTrace_append hprefix tailTrace_731576
  have hstable : (prefixWord ++ tailWord_731576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731576).length < 2 ^ (prefixWord ++ tailWord_731576).sum := by decide
  have hdescent : baseEnd_731576 < baseStart_731576 := by decide
  rcases family_descends (prefixWord ++ tailWord_731576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731580 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 4, 3, 2]
def baseStart_731580 : Nat := 118140960795 + 731580 * 2 ^ 59
def prefixEnd_731580 : Nat := 4983230072969 + 3 ^ 40 * 731580 * 2
def baseEnd_731580 : Nat := 375652177216352923585531

theorem tailTrace_731580 : CollatzResearch.WordTrace tailWord_731580 prefixEnd_731580 375652177216352923585531 := by
  unfold tailWord_731580
  simp only [CollatzResearch.WordTrace]
  refine ⟨13341457344809039380908097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17788609793078719174544129 13341457344809039380908097)
  ·
    refine ⟨10006093008606779535681073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13341457344809039380908097 10006093008606779535681073)
    ·
      refine ⟨7504569756455084651760805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10006093008606779535681073 7504569756455084651760805)
      ·
        refine ⟨1407106829335328372205151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7504569756455084651760805 1407106829335328372205151)
        ·
          refine ⟨2110660244002992558307727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407106829335328372205151 2110660244002992558307727)
          ·
            refine ⟨3165990366004488837461591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110660244002992558307727 3165990366004488837461591)
            ·
              refine ⟨4748985549006733256192387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3165990366004488837461591 4748985549006733256192387)
              ·
                refine ⟨7123478323510099884288581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4748985549006733256192387 7123478323510099884288581)
                ·
                  refine ⟨1335652185658143728304109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7123478323510099884288581 1335652185658143728304109)
                  ·
                    refine ⟨500869569621803898114041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1335652185658143728304109 500869569621803898114041)
                    ·
                      refine ⟨375652177216352923585531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500869569621803898114041 375652177216352923585531)
                      ·
                        rfl

theorem cell23_731580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_731580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731580 prefixEnd_731580 := by exact prefixLift 731580
  have htrace : WordTrace (prefixWord ++ tailWord_731580) baseStart_731580 baseEnd_731580 := by
    simpa [prefixWord, tailWord_731580, baseEnd_731580] using wordTrace_append hprefix tailTrace_731580
  have hstable : (prefixWord ++ tailWord_731580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731580).length < 2 ^ (prefixWord ++ tailWord_731580).sum := by decide
  have hdescent : baseEnd_731580 < baseStart_731580 := by decide
  rcases family_descends (prefixWord ++ tailWord_731580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731610 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2]
def baseStart_731610 : Nat := 118140960795 + 731610 * 2 ^ 59
def prefixEnd_731610 : Nat := 4983230072969 + 3 ^ 40 * 731610 * 2
def baseEnd_731610 : Nat := 375667581635987806210393

theorem tailTrace_731610 : CollatzResearch.WordTrace tailWord_731610 prefixEnd_731610 375667581635987806210393 := by
  unfold tailWord_731610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6671002219877348471352071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17789339253006262590272189 6671002219877348471352071)
  ·
    refine ⟨10006503329816022707028107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6671002219877348471352071 10006503329816022707028107)
    ·
      refine ⟨15009754994724034060542161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10006503329816022707028107 15009754994724034060542161)
      ·
        refine ⟨11257316246043025545406621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15009754994724034060542161 11257316246043025545406621)
        ·
          refine ⟨4221493592266134579527483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11257316246043025545406621 4221493592266134579527483)
          ·
            refine ⟨6332240388399201869291225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221493592266134579527483 6332240388399201869291225)
            ·
              refine ⟨4749180291299401401968419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6332240388399201869291225 4749180291299401401968419)
              ·
                refine ⟨7123770436949102102952629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4749180291299401401968419 7123770436949102102952629)
                ·
                  refine ⟨667853478463978322151809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7123770436949102102952629 667853478463978322151809)
                  ·
                    refine ⟨500890108847983741613857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 667853478463978322151809 500890108847983741613857)
                    ·
                      refine ⟨375667581635987806210393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500890108847983741613857 375667581635987806210393)
                      ·
                        rfl

theorem cell23_731610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_731610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731610 prefixEnd_731610 := by exact prefixLift 731610
  have htrace : WordTrace (prefixWord ++ tailWord_731610) baseStart_731610 baseEnd_731610 := by
    simpa [prefixWord, tailWord_731610, baseEnd_731610] using wordTrace_append hprefix tailTrace_731610
  have hstable : (prefixWord ++ tailWord_731610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731610).length < 2 ^ (prefixWord ++ tailWord_731610).sum := by decide
  have hdescent : baseEnd_731610 < baseStart_731610 := by decide
  rcases family_descends (prefixWord ++ tailWord_731610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731623 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_731623 : Nat := 118140960795 + 731623 * 2 ^ 59
def prefixEnd_731623 : Nat := 4983230072969 + 3 ^ 40 * 731623 * 2
def baseEnd_731623 : Nat := 375674256884496255347833

theorem tailTrace_731623 : CollatzResearch.WordTrace tailWord_731623 prefixEnd_731623 375674256884496255347833 := by
  unfold tailWord_731623
  simp only [CollatzResearch.WordTrace]
  refine ⟨26684483028462297105631523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17789655352308198070421015 26684483028462297105631523)
  ·
    refine ⟨40026724542693445658447285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26684483028462297105631523 40026724542693445658447285)
    ·
      refine ⟨3752505425877510530479433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40026724542693445658447285 3752505425877510530479433)
      ·
        refine ⟨2814379069408132897859575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3752505425877510530479433 2814379069408132897859575)
        ·
          refine ⟨4221568604112199346789363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2814379069408132897859575 4221568604112199346789363)
          ·
            refine ⟨6332352906168299020184045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221568604112199346789363 6332352906168299020184045)
            ·
              refine ⟨2374632339813112132569017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6332352906168299020184045 2374632339813112132569017)
              ·
                refine ⟨1780974254859834099426763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2374632339813112132569017 1780974254859834099426763)
                ·
                  refine ⟨2671461382289751149140145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780974254859834099426763 2671461382289751149140145)
                  ·
                    refine ⟨2003596036717313361855109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2671461382289751149140145 2003596036717313361855109)
                    ·
                      refine ⟨375674256884496255347833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2003596036717313361855109 375674256884496255347833)
                      ·
                        rfl

theorem cell23_731623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_731623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731623 prefixEnd_731623 := by exact prefixLift 731623
  have htrace : WordTrace (prefixWord ++ tailWord_731623) baseStart_731623 baseEnd_731623 := by
    simpa [prefixWord, tailWord_731623, baseEnd_731623] using wordTrace_append hprefix tailTrace_731623
  have hstable : (prefixWord ++ tailWord_731623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731623).length < 2 ^ (prefixWord ++ tailWord_731623).sum := by decide
  have hdescent : baseEnd_731623 < baseStart_731623 := by decide
  rcases family_descends (prefixWord ++ tailWord_731623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731627 : List Nat := [1, 1, 1, 1, 2, 3, 4, 5, 1, 2, 2]
def baseStart_731627 : Nat := 118140960795 + 731627 * 2 ^ 59
def prefixEnd_731627 : Nat := 4983230072969 + 3 ^ 40 * 731627 * 2
def baseEnd_731627 : Nat := 375676310807114239697815

theorem tailTrace_731627 : CollatzResearch.WordTrace tailWord_731627 prefixEnd_731627 375676310807114239697815 := by
  unfold tailWord_731627
  simp only [CollatzResearch.WordTrace]
  refine ⟨26684628920447805788777135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17789752613631870525851423 26684628920447805788777135)
  ·
    refine ⟨40026943380671708683165703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26684628920447805788777135 40026943380671708683165703)
    ·
      refine ⟨60040415071007563024748555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40026943380671708683165703 60040415071007563024748555)
      ·
        refine ⟨90060622606511344537122833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60040415071007563024748555 90060622606511344537122833)
        ·
          refine ⟨67545466954883508402842125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90060622606511344537122833 67545466954883508402842125)
          ·
            refine ⟨25329550108081315651065797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67545466954883508402842125 25329550108081315651065797)
            ·
              refine ⟨4749290645265246684574837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25329550108081315651065797 4749290645265246684574837)
              ·
                refine ⟨445245997993616876678891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4749290645265246684574837 445245997993616876678891)
                ·
                  refine ⟨667868996990425315018337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445245997993616876678891 667868996990425315018337)
                  ·
                    refine ⟨500901747742818986263753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 667868996990425315018337 500901747742818986263753)
                    ·
                      refine ⟨375676310807114239697815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500901747742818986263753 375676310807114239697815)
                      ·
                        rfl

theorem cell23_731627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 2, 2].length) (baseStart_731627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731627 prefixEnd_731627 := by exact prefixLift 731627
  have htrace : WordTrace (prefixWord ++ tailWord_731627) baseStart_731627 baseEnd_731627 := by
    simpa [prefixWord, tailWord_731627, baseEnd_731627] using wordTrace_append hprefix tailTrace_731627
  have hstable : (prefixWord ++ tailWord_731627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731627).length < 2 ^ (prefixWord ++ tailWord_731627).sum := by decide
  have hdescent : baseEnd_731627 < baseStart_731627 := by decide
  rcases family_descends (prefixWord ++ tailWord_731627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731630 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_731630 : Nat := 118140960795 + 731630 * 2 ^ 59
def prefixEnd_731630 : Nat := 4983230072969 + 3 ^ 40 * 731630 * 2
def baseEnd_731630 : Nat := 375677851249077727960301

theorem tailTrace_731630 : CollatzResearch.WordTrace tailWord_731630 prefixEnd_731630 375677851249077727960301 := by
  unfold tailWord_731630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3335592292429617162642043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17789825559624624867424229 3335592292429617162642043)
  ·
    refine ⟨5003388438644425743963065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3335592292429617162642043 5003388438644425743963065)
    ·
      refine ⟨3752541328983319307972299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5003388438644425743963065 3752541328983319307972299)
      ·
        refine ⟨5628811993474978961958449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3752541328983319307972299 5628811993474978961958449)
        ·
          refine ⟨4221608995106234221468837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5628811993474978961958449 4221608995106234221468837)
          ·
            refine ⟨791551686582418916525407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4221608995106234221468837 791551686582418916525407)
            ·
              refine ⟨1187327529873628374788111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791551686582418916525407 1187327529873628374788111)
              ·
                refine ⟨1780991294810442562182167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187327529873628374788111 1780991294810442562182167)
                ·
                  refine ⟨2671486942215663843273251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780991294810442562182167 2671486942215663843273251)
                  ·
                    refine ⟨4007230413323495764909877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2671486942215663843273251 4007230413323495764909877)
                    ·
                      refine ⟨375677851249077727960301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4007230413323495764909877 375677851249077727960301)
                      ·
                        rfl

theorem cell23_731630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_731630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731630 prefixEnd_731630 := by exact prefixLift 731630
  have htrace : WordTrace (prefixWord ++ tailWord_731630) baseStart_731630 baseEnd_731630 := by
    simpa [prefixWord, tailWord_731630, baseEnd_731630] using wordTrace_append hprefix tailTrace_731630
  have hstable : (prefixWord ++ tailWord_731630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731630).length < 2 ^ (prefixWord ++ tailWord_731630).sum := by decide
  have hdescent : baseEnd_731630 < baseStart_731630 := by decide
  rcases family_descends (prefixWord ++ tailWord_731630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731654 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_731654 : Nat := 118140960795 + 731654 * 2 ^ 59
def prefixEnd_731654 : Nat := 4983230072969 + 3 ^ 40 * 731654 * 2
def baseEnd_731654 : Nat := 125230058261595211353397

theorem tailTrace_731654 : CollatzResearch.WordTrace tailWord_731654 prefixEnd_731654 125230058261595211353397 := by
  unfold tailWord_731654
  simp only [CollatzResearch.WordTrace]
  refine ⟨833925427854687168750313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17790409127566659600006677 833925427854687168750313)
  ·
    refine ⟨625444070891015376562735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 833925427854687168750313 625444070891015376562735)
    ·
      refine ⟨938166106336523064844103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 625444070891015376562735 938166106336523064844103)
      ·
        refine ⟨1407249159504784597266155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 938166106336523064844103 1407249159504784597266155)
        ·
          refine ⟨2110873739257176895899233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407249159504784597266155 2110873739257176895899233)
          ·
            refine ⟨1583155304442882671924425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2110873739257176895899233 1583155304442882671924425)
            ·
              refine ⟨1187366478332162003943319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1583155304442882671924425 1187366478332162003943319)
              ·
                refine ⟨1781049717498243005914979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187366478332162003943319 1781049717498243005914979)
                ·
                  refine ⟨2671574576247364508872469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781049717498243005914979 2671574576247364508872469)
                  ·
                    refine ⟨125230058261595211353397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2671574576247364508872469 125230058261595211353397)
                    ·
                      rfl

theorem cell23_731654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_731654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731654 prefixEnd_731654 := by exact prefixLift 731654
  have htrace : WordTrace (prefixWord ++ tailWord_731654) baseStart_731654 baseEnd_731654 := by
    simpa [prefixWord, tailWord_731654, baseEnd_731654] using wordTrace_append hprefix tailTrace_731654
  have hstable : (prefixWord ++ tailWord_731654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731654).length < 2 ^ (prefixWord ++ tailWord_731654).sum := by decide
  have hdescent : baseEnd_731654 < baseStart_731654 := by decide
  rcases family_descends (prefixWord ++ tailWord_731654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731656 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_731656 : Nat := 118140960795 + 731656 * 2 ^ 59
def prefixEnd_731656 : Nat := 4983230072969 + 3 ^ 40 * 731656 * 2
def baseEnd_731656 : Nat := 375691201746094626235181

theorem tailTrace_731656 : CollatzResearch.WordTrace tailWord_731656 prefixEnd_731656 375691201746094626235181 := by
  unfold tailWord_731656
  simp only [CollatzResearch.WordTrace]
  refine ⟨13342843318671371870791411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17790457758228495827721881 13342843318671371870791411)
  ·
    refine ⟨20014264978007057806187117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13342843318671371870791411 20014264978007057806187117)
    ·
      refine ⟨7505349366752646677320169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20014264978007057806187117 7505349366752646677320169)
      ·
        refine ⟨5629012025064485007990127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7505349366752646677320169 5629012025064485007990127)
        ·
          refine ⟨8443518037596727511985191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5629012025064485007990127 8443518037596727511985191)
          ·
            refine ⟨12665277056395091267977787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8443518037596727511985191 12665277056395091267977787)
            ·
              refine ⟨18997915584592636901966681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12665277056395091267977787 18997915584592636901966681)
              ·
                refine ⟨14248436688444477676475011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18997915584592636901966681 14248436688444477676475011)
                ·
                  refine ⟨21372655032666716514712517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14248436688444477676475011 21372655032666716514712517)
                  ·
                    refine ⟨4007372818625009346508597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21372655032666716514712517 4007372818625009346508597)
                    ·
                      refine ⟨375691201746094626235181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4007372818625009346508597 375691201746094626235181)
                      ·
                        rfl

theorem cell23_731656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_731656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731656 prefixEnd_731656 := by exact prefixLift 731656
  have htrace : WordTrace (prefixWord ++ tailWord_731656) baseStart_731656 baseEnd_731656 := by
    simpa [prefixWord, tailWord_731656, baseEnd_731656] using wordTrace_append hprefix tailTrace_731656
  have hstable : (prefixWord ++ tailWord_731656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731656).length < 2 ^ (prefixWord ++ tailWord_731656).sum := by decide
  have hdescent : baseEnd_731656 < baseStart_731656 := by decide
  rcases family_descends (prefixWord ++ tailWord_731656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731660 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 1, 3, 3]
def baseStart_731660 : Nat := 118140960795 + 731660 * 2 ^ 59
def prefixEnd_731660 : Nat := 4983230072969 + 3 ^ 40 * 731660 * 2
def baseEnd_731660 : Nat := 375693255668712610585163

theorem tailTrace_731660 : CollatzResearch.WordTrace tailWord_731660 prefixEnd_731660 375693255668712610585163 := by
  unfold tailWord_731660
  simp only [CollatzResearch.WordTrace]
  refine ⟨13342916264664126212364217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17790555019552168283152289 13342916264664126212364217)
  ·
    refine ⟨10007187198498094659273163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13342916264664126212364217 10007187198498094659273163)
    ·
      refine ⟨15010780797747141988909745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10007187198498094659273163 15010780797747141988909745)
      ·
        refine ⟨11258085598310356491682309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15010780797747141988909745 11258085598310356491682309)
        ·
          refine ⟨2110891049683191842190433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11258085598310356491682309 2110891049683191842190433)
          ·
            refine ⟨1583168287262393881642825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2110891049683191842190433 1583168287262393881642825)
            ·
              refine ⟨1187376215446795411232119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1583168287262393881642825 1187376215446795411232119)
              ·
                refine ⟨1781064323170193116848179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187376215446795411232119 1781064323170193116848179)
                ·
                  refine ⟨2671596484755289675272269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781064323170193116848179 2671596484755289675272269)
                  ·
                    refine ⟨1001848681783233628227101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2671596484755289675272269 1001848681783233628227101)
                    ·
                      refine ⟨375693255668712610585163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1001848681783233628227101 375693255668712610585163)
                      ·
                        rfl

theorem cell23_731660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_731660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731660 prefixEnd_731660 := by exact prefixLift 731660
  have htrace : WordTrace (prefixWord ++ tailWord_731660) baseStart_731660 baseEnd_731660 := by
    simpa [prefixWord, tailWord_731660, baseEnd_731660] using wordTrace_append hprefix tailTrace_731660
  have hstable : (prefixWord ++ tailWord_731660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731660).length < 2 ^ (prefixWord ++ tailWord_731660).sum := by decide
  have hdescent : baseEnd_731660 < baseStart_731660 := by decide
  rcases family_descends (prefixWord ++ tailWord_731660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731661 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_731661 : Nat := 118140960795 + 731661 * 2 ^ 59
def prefixEnd_731661 : Nat := 4983230072969 + 3 ^ 40 * 731661 * 2
def baseEnd_731661 : Nat := 375693769149367106672659

theorem tailTrace_731661 : CollatzResearch.WordTrace tailWord_731661 prefixEnd_731661 375693769149367106672659 := by
  unfold tailWord_731661
  simp only [CollatzResearch.WordTrace]
  refine ⟨26685869002324629595514837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17790579334883086397009891 26685869002324629595514837)
  ·
    refine ⟨625450054741983506144879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 26685869002324629595514837 625450054741983506144879)
    ·
      refine ⟨938175082112975259217319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 625450054741983506144879 938175082112975259217319)
      ·
        refine ⟨1407262623169462888825979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 938175082112975259217319 1407262623169462888825979)
        ·
          refine ⟨2110893934754194333238969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407262623169462888825979 2110893934754194333238969)
          ·
            refine ⟨1583170451065645749929227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2110893934754194333238969 1583170451065645749929227)
            ·
              refine ⟨2374755676598468624893841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583170451065645749929227 2374755676598468624893841)
              ·
                refine ⟨1781066757448851468670381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2374755676598468624893841 1781066757448851468670381)
                ·
                  refine ⟨667900034043319300751393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1781066757448851468670381 667900034043319300751393)
                  ·
                    refine ⟨500925025532489475563545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 667900034043319300751393 500925025532489475563545)
                    ·
                      refine ⟨375693769149367106672659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500925025532489475563545 375693769149367106672659)
                      ·
                        rfl

theorem cell23_731661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_731661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731661 prefixEnd_731661 := by exact prefixLift 731661
  have htrace : WordTrace (prefixWord ++ tailWord_731661) baseStart_731661 baseEnd_731661 := by
    simpa [prefixWord, tailWord_731661, baseEnd_731661] using wordTrace_append hprefix tailTrace_731661
  have hstable : (prefixWord ++ tailWord_731661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731661).length < 2 ^ (prefixWord ++ tailWord_731661).sum := by decide
  have hdescent : baseEnd_731661 < baseStart_731661 := by decide
  rcases family_descends (prefixWord ++ tailWord_731661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731717 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 1, 4, 2]
def baseStart_731717 : Nat := 118140960795 + 731717 * 2 ^ 59
def prefixEnd_731717 : Nat := 4983230072969 + 3 ^ 40 * 731717 * 2
def baseEnd_731717 : Nat := 375722524066018887572401

theorem tailTrace_731717 : CollatzResearch.WordTrace tailWord_731717 prefixEnd_731717 375722524066018887572401 := by
  unfold tailWord_731717
  simp only [CollatzResearch.WordTrace]
  refine ⟨26687911490121751159553405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17791940993414500773035603 26687911490121751159553405)
  ·
    refine ⟨10007966808795656684832527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26687911490121751159553405 10007966808795656684832527)
    ·
      refine ⟨15011950213193485027248791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10007966808795656684832527 15011950213193485027248791)
      ·
        refine ⟨22517925319790227540873187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15011950213193485027248791 22517925319790227540873187)
        ·
          refine ⟨33776887979685341311309781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22517925319790227540873187 33776887979685341311309781)
          ·
            refine ⟨791645812023875186983823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 33776887979685341311309781 791645812023875186983823)
            ·
              refine ⟨1187468718035812780475735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791645812023875186983823 1187468718035812780475735)
              ·
                refine ⟨1781203077053719170713603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187468718035812780475735 1781203077053719170713603)
                ·
                  refine ⟨2671804615580578756070405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781203077053719170713603 2671804615580578756070405)
                  ·
                    refine ⟨500963365421358516763201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2671804615580578756070405 500963365421358516763201)
                    ·
                      refine ⟨375722524066018887572401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 500963365421358516763201 375722524066018887572401)
                      ·
                        rfl

theorem cell23_731717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 4, 2].length) (baseStart_731717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731717 prefixEnd_731717 := by exact prefixLift 731717
  have htrace : WordTrace (prefixWord ++ tailWord_731717) baseStart_731717 baseEnd_731717 := by
    simpa [prefixWord, tailWord_731717, baseEnd_731717] using wordTrace_append hprefix tailTrace_731717
  have hstable : (prefixWord ++ tailWord_731717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731717).length < 2 ^ (prefixWord ++ tailWord_731717).sum := by decide
  have hdescent : baseEnd_731717 < baseStart_731717 := by decide
  rcases family_descends (prefixWord ++ tailWord_731717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731733 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_731733 : Nat := 118140960795 + 731733 * 2 ^ 59
def prefixEnd_731733 : Nat := 4983230072969 + 3 ^ 40 * 731733 * 2
def baseEnd_731733 : Nat := 375730739756490824972327

theorem tailTrace_731733 : CollatzResearch.WordTrace tailWord_731733 prefixEnd_731733 375730739756490824972327 := by
  unfold tailWord_731733
  simp only [CollatzResearch.WordTrace]
  refine ⟨26688495058063785892135853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17792330038709190594757235 26688495058063785892135853)
  ·
    refine ⟨10008185646773919709550945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26688495058063785892135853 10008185646773919709550945)
    ·
      refine ⟨7506139235080439782163209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10008185646773919709550945 7506139235080439782163209)
      ·
        refine ⟨5629604426310329836622407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7506139235080439782163209 5629604426310329836622407)
        ·
          refine ⟨8444406639465494754933611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5629604426310329836622407 8444406639465494754933611)
          ·
            refine ⟨12666609959198242132400417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8444406639465494754933611 12666609959198242132400417)
            ·
              refine ⟨9499957469398681599300313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12666609959198242132400417 9499957469398681599300313)
              ·
                refine ⟨7124968102049011199475235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9499957469398681599300313 7124968102049011199475235)
                ·
                  refine ⟨10687452153073516799212853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7124968102049011199475235 10687452153073516799212853)
                  ·
                    refine ⟨1001948639350642199926205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10687452153073516799212853 1001948639350642199926205)
                    ·
                      refine ⟨375730739756490824972327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1001948639350642199926205 375730739756490824972327)
                      ·
                        rfl

theorem cell23_731733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_731733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731733 prefixEnd_731733 := by exact prefixLift 731733
  have htrace : WordTrace (prefixWord ++ tailWord_731733) baseStart_731733 baseEnd_731733 := by
    simpa [prefixWord, tailWord_731733, baseEnd_731733] using wordTrace_append hprefix tailTrace_731733
  have hstable : (prefixWord ++ tailWord_731733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731733).length < 2 ^ (prefixWord ++ tailWord_731733).sum := by decide
  have hdescent : baseEnd_731733 < baseStart_731733 := by decide
  rcases family_descends (prefixWord ++ tailWord_731733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731793 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 3]
def baseStart_731793 : Nat := 118140960795 + 731793 * 2 ^ 59
def prefixEnd_731793 : Nat := 4983230072969 + 3 ^ 40 * 731793 * 2
def baseEnd_731793 : Nat := 375761548595760590222051

theorem tailTrace_731793 : CollatzResearch.WordTrace tailWord_731793 prefixEnd_731793 375761548595760590222051 := by
  unfold tailWord_731793
  simp only [CollatzResearch.WordTrace]
  refine ⟨26690683437846416139320033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17793788958564277426213355 26690683437846416139320033)
  ·
    refine ⟨20018012578384812104490025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26690683437846416139320033 20018012578384812104490025)
    ·
      refine ⟨15013509433788609078367519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20018012578384812104490025 15013509433788609078367519)
      ·
        refine ⟨22520264150682913617551279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15013509433788609078367519 22520264150682913617551279)
        ·
          refine ⟨33780396226024370426326919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22520264150682913617551279 33780396226024370426326919)
          ·
            refine ⟨50670594339036555639490379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33780396226024370426326919 50670594339036555639490379)
            ·
              refine ⟨76005891508554833459235569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50670594339036555639490379 76005891508554833459235569)
              ·
                refine ⟨57004418631416125094426677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76005891508554833459235569 57004418631416125094426677)
                ·
                  refine ⟨5344164246695261727602501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57004418631416125094426677 5344164246695261727602501)
                  ·
                    refine ⟨1002030796255361573925469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5344164246695261727602501 1002030796255361573925469)
                    ·
                      refine ⟨375761548595760590222051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1002030796255361573925469 375761548595760590222051)
                      ·
                        rfl

theorem cell23_731793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_731793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731793 prefixEnd_731793 := by exact prefixLift 731793
  have htrace : WordTrace (prefixWord ++ tailWord_731793) baseStart_731793 baseEnd_731793 := by
    simpa [prefixWord, tailWord_731793, baseEnd_731793] using wordTrace_append hprefix tailTrace_731793
  have hstable : (prefixWord ++ tailWord_731793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731793).length < 2 ^ (prefixWord ++ tailWord_731793).sum := by decide
  have hdescent : baseEnd_731793 < baseStart_731793 := by decide
  rcases family_descends (prefixWord ++ tailWord_731793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731841 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_731841 : Nat := 118140960795 + 731841 * 2 ^ 59
def prefixEnd_731841 : Nat := 4983230072969 + 3 ^ 40 * 731841 * 2
def baseEnd_731841 : Nat := 375786195667176402421831

theorem tailTrace_731841 : CollatzResearch.WordTrace tailWord_731841 prefixEnd_731841 375786195667176402421831 := by
  unfold tailWord_731841
  simp only [CollatzResearch.WordTrace]
  refine ⟨26692434141672520337067377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17794956094448346891378251 26692434141672520337067377)
  ·
    refine ⟨20019325606254390252800533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26692434141672520337067377 20019325606254390252800533)
    ·
      refine ⟨938405887793174543100025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20019325606254390252800533 938405887793174543100025)
      ·
        refine ⟨703804415844880907325019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 938405887793174543100025 703804415844880907325019)
        ·
          refine ⟨1055706623767321360987529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703804415844880907325019 1055706623767321360987529)
          ·
            refine ⟨791779967825491020740647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1055706623767321360987529 791779967825491020740647)
            ·
              refine ⟨1187669951738236531110971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791779967825491020740647 1187669951738236531110971)
              ·
                refine ⟨1781504927607354796666457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187669951738236531110971 1781504927607354796666457)
                ·
                  refine ⟨1336128695705516097499843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1781504927607354796666457 1336128695705516097499843)
                  ·
                    refine ⟨2004193043558274146249765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1336128695705516097499843 2004193043558274146249765)
                    ·
                      refine ⟨375786195667176402421831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2004193043558274146249765 375786195667176402421831)
                      ·
                        rfl

theorem cell23_731841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_731841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731841 prefixEnd_731841 := by exact prefixLift 731841
  have htrace : WordTrace (prefixWord ++ tailWord_731841) baseStart_731841 baseEnd_731841 := by
    simpa [prefixWord, tailWord_731841, baseEnd_731841] using wordTrace_append hprefix tailTrace_731841
  have hstable : (prefixWord ++ tailWord_731841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731841).length < 2 ^ (prefixWord ++ tailWord_731841).sum := by decide
  have hdescent : baseEnd_731841 < baseStart_731841 := by decide
  rcases family_descends (prefixWord ++ tailWord_731841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731844 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_731844 : Nat := 118140960795 + 731844 * 2 ^ 59
def prefixEnd_731844 : Nat := 4983230072969 + 3 ^ 40 * 731844 * 2
def baseEnd_731844 : Nat := 375787736109139890684317

theorem tailTrace_731844 : CollatzResearch.WordTrace tailWord_731844 prefixEnd_731844 375787736109139890684317 := by
  unfold tailWord_731844
  simp only [CollatzResearch.WordTrace]
  refine ⟨13346271780330825924713293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17795029040441101232951057 13346271780330825924713293)
  ·
    refine ⟨5004851917624059721767485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13346271780330825924713293 5004851917624059721767485)
    ·
      refine ⟨1876819469109022395662807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5004851917624059721767485 1876819469109022395662807)
      ·
        refine ⟨2815229203663533593494211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876819469109022395662807 2815229203663533593494211)
        ·
          refine ⟨4222843805495300390241317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815229203663533593494211 4222843805495300390241317)
          ·
            refine ⟨791783213530368823170247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4222843805495300390241317 791783213530368823170247)
            ·
              refine ⟨1187674820295553234755371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791783213530368823170247 1187674820295553234755371)
              ·
                refine ⟨1781512230443329852133057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187674820295553234755371 1781512230443329852133057)
                ·
                  refine ⟨1336134172832497389099793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1781512230443329852133057 1336134172832497389099793)
                  ·
                    refine ⟨1002100629624373041824845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1336134172832497389099793 1002100629624373041824845)
                    ·
                      refine ⟨375787736109139890684317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1002100629624373041824845 375787736109139890684317)
                      ·
                        rfl

theorem cell23_731844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_731844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_731844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_731844 prefixEnd_731844 := by exact prefixLift 731844
  have htrace : WordTrace (prefixWord ++ tailWord_731844) baseStart_731844 baseEnd_731844 := by
    simpa [prefixWord, tailWord_731844, baseEnd_731844] using wordTrace_append hprefix tailTrace_731844
  have hstable : (prefixWord ++ tailWord_731844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731844).length < 2 ^ (prefixWord ++ tailWord_731844).sum := by decide
  have hdescent : baseEnd_731844 < baseStart_731844 := by decide
  rcases family_descends (prefixWord ++ tailWord_731844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732004 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 1, 4, 2]
def baseStart_732004 : Nat := 118140960795 + 732004 * 2 ^ 59
def prefixEnd_732004 : Nat := 4983230072969 + 3 ^ 40 * 732004 * 2
def baseEnd_732004 : Nat := 375869893013859264683581

theorem tailTrace_732004 : CollatzResearch.WordTrace tailWord_732004 prefixEnd_732004 375869893013859264683581 := by
  unfold tailWord_732004
  simp only [CollatzResearch.WordTrace]
  refine ⟨13349189620040999587625533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17798919493387999450167377 13349189620040999587625533)
  ·
    refine ⟨5005946107515374845359575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13349189620040999587625533 5005946107515374845359575)
    ·
      refine ⟨7508919161273062268039363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5005946107515374845359575 7508919161273062268039363)
      ·
        refine ⟨11263378741909593402059045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7508919161273062268039363 11263378741909593402059045)
        ·
          refine ⟨2111883514108048762886071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11263378741909593402059045 2111883514108048762886071)
          ·
            refine ⟨3167825271162073144329107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111883514108048762886071 3167825271162073144329107)
            ·
              refine ⟨4751737906743109716493661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167825271162073144329107 4751737906743109716493661)
              ·
                refine ⟨1781901715028666143685123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4751737906743109716493661 1781901715028666143685123)
                ·
                  refine ⟨2672852572542999215527685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781901715028666143685123 2672852572542999215527685)
                  ·
                    refine ⟨501159857351812352911441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2672852572542999215527685 501159857351812352911441)
                    ·
                      refine ⟨375869893013859264683581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 501159857351812352911441 375869893013859264683581)
                      ·
                        rfl

theorem cell23_732004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_732004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732004 prefixEnd_732004 := by exact prefixLift 732004
  have htrace : WordTrace (prefixWord ++ tailWord_732004) baseStart_732004 baseEnd_732004 := by
    simpa [prefixWord, tailWord_732004, baseEnd_732004] using wordTrace_append hprefix tailTrace_732004
  have hstable : (prefixWord ++ tailWord_732004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732004).length < 2 ^ (prefixWord ++ tailWord_732004).sum := by decide
  have hdescent : baseEnd_732004 < baseStart_732004 := by decide
  rcases family_descends (prefixWord ++ tailWord_732004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732027 : List Nat := [1, 1, 1, 1, 1, 5, 3, 5, 5]
def baseStart_732027 : Nat := 118140960795 + 732027 * 2 ^ 59
def prefixEnd_732027 : Nat := 4983230072969 + 3 ^ 40 * 732027 * 2
def baseEnd_732027 : Nat := 41764633674323630521775

theorem tailTrace_732027 : CollatzResearch.WordTrace tailWord_732027 prefixEnd_732027 41764633674323630521775 := by
  unfold tailWord_732027
  simp only [CollatzResearch.WordTrace]
  refine ⟨26699218118998674103338335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17799478745999116068892223 26699218118998674103338335)
  ·
    refine ⟨40048827178498011155007503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26699218118998674103338335 40048827178498011155007503)
    ·
      refine ⟨60073240767747016732511255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40048827178498011155007503 60073240767747016732511255)
      ·
        refine ⟨90109861151620525098766883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60073240767747016732511255 90109861151620525098766883)
        ·
          refine ⟨135164791727430787648150325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90109861151620525098766883 135164791727430787648150325)
          ·
            refine ⟨12671699224446636342014093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135164791727430787648150325 12671699224446636342014093)
            ·
              refine ⟨4751887209167488628255285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12671699224446636342014093 4751887209167488628255285)
              ·
                refine ⟨445489425859452058898933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4751887209167488628255285 445489425859452058898933)
                ·
                  refine ⟨41764633674323630521775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 445489425859452058898933 41764633674323630521775)
                  ·
                    rfl

theorem cell23_732027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 5].length) (baseStart_732027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732027 prefixEnd_732027 := by exact prefixLift 732027
  have htrace : WordTrace (prefixWord ++ tailWord_732027) baseStart_732027 baseEnd_732027 := by
    simpa [prefixWord, tailWord_732027, baseEnd_732027] using wordTrace_append hprefix tailTrace_732027
  have hstable : (prefixWord ++ tailWord_732027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732027).length < 2 ^ (prefixWord ++ tailWord_732027).sum := by decide
  have hdescent : baseEnd_732027 < baseStart_732027 := by decide
  rcases family_descends (prefixWord ++ tailWord_732027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732037 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 2, 3, 3]
def baseStart_732037 : Nat := 118140960795 + 732037 * 2 ^ 59
def prefixEnd_732037 : Nat := 4983230072969 + 3 ^ 40 * 732037 * 2
def baseEnd_732037 : Nat := 375886837875457635570929

theorem tailTrace_732037 : CollatzResearch.WordTrace tailWord_732037 prefixEnd_732037 375886837875457635570929 := by
  unfold tailWord_732037
  simp only [CollatzResearch.WordTrace]
  refine ⟨26699582848962445811202365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17799721899308297207468243 26699582848962445811202365)
  ·
    refine ⟨10012343568360917179200887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26699582848962445811202365 10012343568360917179200887)
    ·
      refine ⟨15018515352541375768801331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10012343568360917179200887 15018515352541375768801331)
      ·
        refine ⟨22527773028812063653201997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15018515352541375768801331 22527773028812063653201997)
        ·
          refine ⟨8447914885804523869950749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22527773028812063653201997 8447914885804523869950749)
          ·
            refine ⟨3167968082176696451231531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8447914885804523869950749 3167968082176696451231531)
            ·
              refine ⟨4751952123265044676847297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167968082176696451231531 4751952123265044676847297)
              ·
                refine ⟨3563964092448783507635473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4751952123265044676847297 3563964092448783507635473)
                ·
                  refine ⟨2672973069336587630726605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3563964092448783507635473 2672973069336587630726605)
                  ·
                    refine ⟨1002364901001220361522477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672973069336587630726605 1002364901001220361522477)
                    ·
                      refine ⟨375886837875457635570929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1002364901001220361522477 375886837875457635570929)
                      ·
                        rfl

theorem cell23_732037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_732037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732037 prefixEnd_732037 := by exact prefixLift 732037
  have htrace : WordTrace (prefixWord ++ tailWord_732037) baseStart_732037 baseEnd_732037 := by
    simpa [prefixWord, tailWord_732037, baseEnd_732037] using wordTrace_append hprefix tailTrace_732037
  have hstable : (prefixWord ++ tailWord_732037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732037).length < 2 ^ (prefixWord ++ tailWord_732037).sum := by decide
  have hdescent : baseEnd_732037 < baseStart_732037 := by decide
  rcases family_descends (prefixWord ++ tailWord_732037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732087 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 5, 4]
def baseStart_732087 : Nat := 118140960795 + 732087 * 2 ^ 59
def prefixEnd_732087 : Nat := 4983230072969 + 3 ^ 40 * 732087 * 2
def baseEnd_732087 : Nat := 125304170636060813315233

theorem tailTrace_732087 : CollatzResearch.WordTrace tailWord_732087 prefixEnd_732087 125304170636060813315233 := by
  unfold tailWord_732087
  simp only [CollatzResearch.WordTrace]
  refine ⟨26701406498781304350522515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17800937665854202900348343 26701406498781304350522515)
  ·
    refine ⟨40052109748171956525783773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26701406498781304350522515 40052109748171956525783773)
    ·
      refine ⟨15019541155564483697168915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40052109748171956525783773 15019541155564483697168915)
      ·
        refine ⟨22529311733346725545753373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15019541155564483697168915 22529311733346725545753373)
        ·
          refine ⟨8448491900005022079657515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22529311733346725545753373 8448491900005022079657515)
          ·
            refine ⟨12672737850007533119486273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8448491900005022079657515 12672737850007533119486273)
            ·
              refine ⟨9504553387505649839614705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12672737850007533119486273 9504553387505649839614705)
              ·
                refine ⟨7128415040629237379711029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9504553387505649839614705 7128415040629237379711029)
                ·
                  refine ⟨668288910058991004347909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7128415040629237379711029 668288910058991004347909)
                  ·
                    refine ⟨125304170636060813315233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 668288910058991004347909 125304170636060813315233)
                    ·
                      rfl

theorem cell23_732087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_732087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732087 prefixEnd_732087 := by exact prefixLift 732087
  have htrace : WordTrace (prefixWord ++ tailWord_732087) baseStart_732087 baseEnd_732087 := by
    simpa [prefixWord, tailWord_732087, baseEnd_732087] using wordTrace_append hprefix tailTrace_732087
  have hstable : (prefixWord ++ tailWord_732087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732087).length < 2 ^ (prefixWord ++ tailWord_732087).sum := by decide
  have hdescent : baseEnd_732087 < baseStart_732087 := by decide
  rcases family_descends (prefixWord ++ tailWord_732087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732094 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_732094 : Nat := 118140960795 + 732094 * 2 ^ 59
def prefixEnd_732094 : Nat := 4983230072969 + 3 ^ 40 * 732094 * 2
def baseEnd_732094 : Nat := 375916106272763912558167

theorem tailTrace_732094 : CollatzResearch.WordTrace tailWord_732094 prefixEnd_732094 375916106272763912558167 := by
  unfold tailWord_732094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3337707726219493068253417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17801107873170629697351557 3337707726219493068253417)
  ·
    refine ⟨2503280794664619801190063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3337707726219493068253417 2503280794664619801190063)
    ·
      refine ⟨3754921191996929701785095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2503280794664619801190063 3754921191996929701785095)
      ·
        refine ⟨5632381787995394552677643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3754921191996929701785095 5632381787995394552677643)
        ·
          refine ⟨8448572681993091829016465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5632381787995394552677643 8448572681993091829016465)
          ·
            refine ⟨6336429511494818871762349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8448572681993091829016465 6336429511494818871762349)
            ·
              refine ⟨2376161066810557076910881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6336429511494818871762349 2376161066810557076910881)
              ·
                refine ⟨1782120800107917807683161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376161066810557076910881 1782120800107917807683161)
                ·
                  refine ⟨1336590600080938355762371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1782120800107917807683161 1336590600080938355762371)
                  ·
                    refine ⟨2004885900121407533643557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1336590600080938355762371 2004885900121407533643557)
                    ·
                      refine ⟨375916106272763912558167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2004885900121407533643557 375916106272763912558167)
                      ·
                        rfl

theorem cell23_732094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_732094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732094 prefixEnd_732094 := by exact prefixLift 732094
  have htrace : WordTrace (prefixWord ++ tailWord_732094) baseStart_732094 baseEnd_732094 := by
    simpa [prefixWord, tailWord_732094, baseEnd_732094] using wordTrace_append hprefix tailTrace_732094
  have hstable : (prefixWord ++ tailWord_732094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732094).length < 2 ^ (prefixWord ++ tailWord_732094).sum := by decide
  have hdescent : baseEnd_732094 < baseStart_732094 := by decide
  rcases family_descends (prefixWord ++ tailWord_732094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732184 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_732184 : Nat := 118140960795 + 732184 * 2 ^ 59
def prefixEnd_732184 : Nat := 4983230072969 + 3 ^ 40 * 732184 * 2
def baseEnd_732184 : Nat := 375962319531668560432753

theorem tailTrace_732184 : CollatzResearch.WordTrace tailWord_732184 prefixEnd_732184 375962319531668560432753 := by
  unfold tailWord_732184
  simp only [CollatzResearch.WordTrace]
  refine ⟨13352472189714944958401803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17803296252953259944535737 13352472189714944958401803)
  ·
    refine ⟨20028708284572417437602705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13352472189714944958401803 20028708284572417437602705)
    ·
      refine ⟨15021531213429313078202029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20028708284572417437602705 15021531213429313078202029)
      ·
        refine ⟨5633074205035992404325761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15021531213429313078202029 5633074205035992404325761)
        ·
          refine ⟨4224805653776994303244321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5633074205035992404325761 4224805653776994303244321)
          ·
            refine ⟨3168604240332745727433241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4224805653776994303244321 3168604240332745727433241)
            ·
              refine ⟨2376453180249559295574931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168604240332745727433241 2376453180249559295574931)
              ·
                refine ⟨3564679770374338943362397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376453180249559295574931 3564679770374338943362397)
                ·
                  refine ⟨1336754913890377103760899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3564679770374338943362397 1336754913890377103760899)
                  ·
                    refine ⟨2005132370835565655641349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1336754913890377103760899 2005132370835565655641349)
                    ·
                      refine ⟨375962319531668560432753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2005132370835565655641349 375962319531668560432753)
                      ·
                        rfl

theorem cell23_732184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_732184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732184 prefixEnd_732184 := by exact prefixLift 732184
  have htrace : WordTrace (prefixWord ++ tailWord_732184) baseStart_732184 baseEnd_732184 := by
    simpa [prefixWord, tailWord_732184, baseEnd_732184] using wordTrace_append hprefix tailTrace_732184
  have hstable : (prefixWord ++ tailWord_732184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732184).length < 2 ^ (prefixWord ++ tailWord_732184).sum := by decide
  have hdescent : baseEnd_732184 < baseStart_732184 := by decide
  rcases family_descends (prefixWord ++ tailWord_732184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732194 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_732194 : Nat := 118140960795 + 732194 * 2 ^ 59
def prefixEnd_732194 : Nat := 4983230072969 + 3 ^ 40 * 732194 * 2
def baseEnd_732194 : Nat := 125322484779404507102569

theorem tailTrace_732194 : CollatzResearch.WordTrace tailWord_732194 prefixEnd_732194 125322484779404507102569 := by
  unfold tailWord_732194
  simp only [CollatzResearch.WordTrace]
  refine ⟨6676327277348415406166909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17803539406262441083111757 6676327277348415406166909)
  ·
    refine ⟨2503622729005655777312591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6676327277348415406166909 2503622729005655777312591)
    ·
      refine ⟨3755434093508483665968887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2503622729005655777312591 3755434093508483665968887)
      ·
        refine ⟨5633151140262725498953331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3755434093508483665968887 5633151140262725498953331)
        ·
          refine ⟨8449726710394088248429997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5633151140262725498953331 8449726710394088248429997)
          ·
            refine ⟨3168647516397783093161249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8449726710394088248429997 3168647516397783093161249)
            ·
              refine ⟨2376485637298337319870937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168647516397783093161249 2376485637298337319870937)
              ·
                refine ⟨1782364227973752989903203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376485637298337319870937 1782364227973752989903203)
                ·
                  refine ⟨2673546341960629484854805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782364227973752989903203 2673546341960629484854805)
                  ·
                    refine ⟨125322484779404507102569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2673546341960629484854805 125322484779404507102569)
                    ·
                      rfl

theorem cell23_732194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_732194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732194 prefixEnd_732194 := by exact prefixLift 732194
  have htrace : WordTrace (prefixWord ++ tailWord_732194) baseStart_732194 baseEnd_732194 := by
    simpa [prefixWord, tailWord_732194, baseEnd_732194] using wordTrace_append hprefix tailTrace_732194
  have hstable : (prefixWord ++ tailWord_732194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732194).length < 2 ^ (prefixWord ++ tailWord_732194).sum := by decide
  have hdescent : baseEnd_732194 < baseStart_732194 := by decide
  rcases family_descends (prefixWord ++ tailWord_732194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732231 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_732231 : Nat := 118140960795 + 732231 * 2 ^ 59
def prefixEnd_732231 : Nat := 4983230072969 + 3 ^ 40 * 732231 * 2
def baseEnd_732231 : Nat := 375986453122429876545037

theorem tailTrace_732231 : CollatzResearch.WordTrace tailWord_732231 prefixEnd_732231 375986453122429876545037 := by
  unfold tailWord_732231
  simp only [CollatzResearch.WordTrace]
  refine ⟨26706658610259616943764547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17804439073506411295843031 26706658610259616943764547)
  ·
    refine ⟨40059987915389425415646821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26706658610259616943764547 40059987915389425415646821)
    ·
      refine ⟨7511247734135517265433779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40059987915389425415646821 7511247734135517265433779)
      ·
        refine ⟨11266871601203275898150669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7511247734135517265433779 11266871601203275898150669)
        ·
          refine ⟨4225076850451228461806501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11266871601203275898150669 4225076850451228461806501)
          ·
            refine ⟨792201909459605336588719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4225076850451228461806501 792201909459605336588719)
            ·
              refine ⟨1188302864189408004883079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792201909459605336588719 1188302864189408004883079)
              ·
                refine ⟨1782454296284112007324619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188302864189408004883079 1782454296284112007324619)
                ·
                  refine ⟨2673681444426168010986929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782454296284112007324619 2673681444426168010986929)
                  ·
                    refine ⟨2005261083319626008240197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2673681444426168010986929 2005261083319626008240197)
                    ·
                      refine ⟨375986453122429876545037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2005261083319626008240197 375986453122429876545037)
                      ·
                        rfl

theorem cell23_732231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_732231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732231 prefixEnd_732231 := by exact prefixLift 732231
  have htrace : WordTrace (prefixWord ++ tailWord_732231) baseStart_732231 baseEnd_732231 := by
    simpa [prefixWord, tailWord_732231, baseEnd_732231] using wordTrace_append hprefix tailTrace_732231
  have hstable : (prefixWord ++ tailWord_732231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732231).length < 2 ^ (prefixWord ++ tailWord_732231).sum := by decide
  have hdescent : baseEnd_732231 < baseStart_732231 := by decide
  rcases family_descends (prefixWord ++ tailWord_732231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732246 : List Nat := [5, 2, 2, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_732246 : Nat := 118140960795 + 732246 * 2 ^ 59
def prefixEnd_732246 : Nat := 4983230072969 + 3 ^ 40 * 732246 * 2
def baseEnd_732246 : Nat := 375994155332247317857469

theorem tailTrace_732246 : CollatzResearch.WordTrace tailWord_732246 prefixEnd_732246 375994155332247317857469 := by
  unfold tailWord_732246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1669200356575329656597537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17804803803470183003707061 1669200356575329656597537)
  ·
    refine ⟨1251900267431497242448153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1669200356575329656597537 1251900267431497242448153)
    ·
      refine ⟨938925200573622931836115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1251900267431497242448153 938925200573622931836115)
      ·
        refine ⟨1408387800860434397754173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 938925200573622931836115 1408387800860434397754173)
        ·
          refine ⟨528145425322662899157815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1408387800860434397754173 528145425322662899157815)
          ·
            refine ⟨792218137983994348736723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528145425322662899157815 792218137983994348736723)
            ·
              refine ⟨1188327206975991523105085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792218137983994348736723 1188327206975991523105085)
              ·
                refine ⟨445622702615996821164407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1188327206975991523105085 445622702615996821164407)
                ·
                  refine ⟨668434053923995231746611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445622702615996821164407 668434053923995231746611)
                  ·
                    refine ⟨1002651080885992847619917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 668434053923995231746611 1002651080885992847619917)
                    ·
                      refine ⟨375994155332247317857469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1002651080885992847619917 375994155332247317857469)
                      ·
                        rfl

theorem cell23_732246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_732246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732246 prefixEnd_732246 := by exact prefixLift 732246
  have htrace : WordTrace (prefixWord ++ tailWord_732246) baseStart_732246 baseEnd_732246 := by
    simpa [prefixWord, tailWord_732246, baseEnd_732246] using wordTrace_append hprefix tailTrace_732246
  have hstable : (prefixWord ++ tailWord_732246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732246).length < 2 ^ (prefixWord ++ tailWord_732246).sum := by decide
  have hdescent : baseEnd_732246 < baseStart_732246 := by decide
  rcases family_descends (prefixWord ++ tailWord_732246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732274 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_732274 : Nat := 118140960795 + 732274 * 2 ^ 59
def prefixEnd_732274 : Nat := 4983230072969 + 3 ^ 40 * 732274 * 2
def baseEnd_732274 : Nat := 376008532790573208307339

theorem tailTrace_732274 : CollatzResearch.WordTrace tailWord_732274 prefixEnd_732274 376008532790573208307339 := by
  unfold tailWord_732274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6677056737275958821894969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17805484632735890191719917 6677056737275958821894969)
  ·
    refine ⟨5007792552956969116421227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6677056737275958821894969 5007792552956969116421227)
    ·
      refine ⟨7511688829435453674631841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5007792552956969116421227 7511688829435453674631841)
      ·
        refine ⟨5633766622076590255973881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7511688829435453674631841 5633766622076590255973881)
        ·
          refine ⟨4225324966557442691980411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5633766622076590255973881 4225324966557442691980411)
          ·
            refine ⟨6337987449836164037970617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4225324966557442691980411 6337987449836164037970617)
            ·
              refine ⟨4753490587377123028477963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6337987449836164037970617 4753490587377123028477963)
              ·
                refine ⟨7130235881065684542716945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753490587377123028477963 7130235881065684542716945)
                ·
                  refine ⟨5347676910799263407037709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7130235881065684542716945 5347676910799263407037709)
                  ·
                    refine ⟨2005378841549723777639141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5347676910799263407037709 2005378841549723777639141)
                    ·
                      refine ⟨376008532790573208307339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2005378841549723777639141 376008532790573208307339)
                      ·
                        rfl

theorem cell23_732274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_732274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732274 prefixEnd_732274 := by exact prefixLift 732274
  have htrace : WordTrace (prefixWord ++ tailWord_732274) baseStart_732274 baseEnd_732274 := by
    simpa [prefixWord, tailWord_732274, baseEnd_732274] using wordTrace_append hprefix tailTrace_732274
  have hstable : (prefixWord ++ tailWord_732274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732274).length < 2 ^ (prefixWord ++ tailWord_732274).sum := by decide
  have hdescent : baseEnd_732274 < baseStart_732274 := by decide
  rcases family_descends (prefixWord ++ tailWord_732274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732278 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_732278 : Nat := 118140960795 + 732278 * 2 ^ 59
def prefixEnd_732278 : Nat := 4983230072969 + 3 ^ 40 * 732278 * 2
def baseEnd_732278 : Nat := 376010586713191192657321

theorem tailTrace_732278 : CollatzResearch.WordTrace tailWord_732278 prefixEnd_732278 376010586713191192657321 := by
  unfold tailWord_732278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1669273302568083998170343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17805581894059562647150325 1669273302568083998170343)
  ·
    refine ⟨2503909953852125997255515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1669273302568083998170343 2503909953852125997255515)
    ·
      refine ⟨3755864930778188995883273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2503909953852125997255515 3755864930778188995883273)
      ·
        refine ⟨2816898698083641746912455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3755864930778188995883273 2816898698083641746912455)
        ·
          refine ⟨4225348047125462620368683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2816898698083641746912455 4225348047125462620368683)
          ·
            refine ⟨6338022070688193930553025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4225348047125462620368683 6338022070688193930553025)
            ·
              refine ⟨4753516553016145447914769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6338022070688193930553025 4753516553016145447914769)
              ·
                refine ⟨3565137414762109085936077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4753516553016145447914769 3565137414762109085936077)
                ·
                  refine ⟨1336926530535790907226029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3565137414762109085936077 1336926530535790907226029)
                  ·
                    refine ⟨501347448950921590209761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1336926530535790907226029 501347448950921590209761)
                    ·
                      refine ⟨376010586713191192657321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 501347448950921590209761 376010586713191192657321)
                      ·
                        rfl

theorem cell23_732278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_732278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732278 prefixEnd_732278 := by exact prefixLift 732278
  have htrace : WordTrace (prefixWord ++ tailWord_732278) baseStart_732278 baseEnd_732278 := by
    simpa [prefixWord, tailWord_732278, baseEnd_732278] using wordTrace_append hprefix tailTrace_732278
  have hstable : (prefixWord ++ tailWord_732278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732278).length < 2 ^ (prefixWord ++ tailWord_732278).sum := by decide
  have hdescent : baseEnd_732278 < baseStart_732278 := by decide
  rcases family_descends (prefixWord ++ tailWord_732278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732287 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_732287 : Nat := 118140960795 + 732287 * 2 ^ 59
def prefixEnd_732287 : Nat := 4983230072969 + 3 ^ 40 * 732287 * 2
def baseEnd_732287 : Nat := 376015208039081657444779

theorem tailTrace_732287 : CollatzResearch.WordTrace tailWord_732287 prefixEnd_732287 376015208039081657444779 := by
  unfold tailWord_732287
  simp only [CollatzResearch.WordTrace]
  refine ⟨26708701098056738507803115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17805800732037825671868743 26708701098056738507803115)
  ·
    refine ⟨40063051647085107761704673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26708701098056738507803115 40063051647085107761704673)
    ·
      refine ⟨30047288735313830821278505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40063051647085107761704673 30047288735313830821278505)
      ·
        refine ⟨22535466551485373115958879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30047288735313830821278505 22535466551485373115958879)
        ·
          refine ⟨33803199827228059673938319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22535466551485373115958879 33803199827228059673938319)
          ·
            refine ⟨50704799740842089510907479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33803199827228059673938319 50704799740842089510907479)
            ·
              refine ⟨76057199611263134266361219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50704799740842089510907479 76057199611263134266361219)
              ·
                refine ⟨114085799416894701399541829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76057199611263134266361219 114085799416894701399541829)
                ·
                  refine ⟨21391087390667756512414093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114085799416894701399541829 21391087390667756512414093)
                  ·
                    refine ⟨8021657771500408692155285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21391087390667756512414093 8021657771500408692155285)
                    ·
                      refine ⟨376015208039081657444779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8021657771500408692155285 376015208039081657444779)
                      ·
                        rfl

theorem cell23_732287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_732287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732287 prefixEnd_732287 := by exact prefixLift 732287
  have htrace : WordTrace (prefixWord ++ tailWord_732287) baseStart_732287 baseEnd_732287 := by
    simpa [prefixWord, tailWord_732287, baseEnd_732287] using wordTrace_append hprefix tailTrace_732287
  have hstable : (prefixWord ++ tailWord_732287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732287).length < 2 ^ (prefixWord ++ tailWord_732287).sum := by decide
  have hdescent : baseEnd_732287 < baseStart_732287 := by decide
  rcases family_descends (prefixWord ++ tailWord_732287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732291 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 1, 4, 2]
def baseStart_732291 : Nat := 118140960795 + 732291 * 2 ^ 59
def prefixEnd_732291 : Nat := 4983230072969 + 3 ^ 40 * 732291 * 2
def baseEnd_732291 : Nat := 376017261961699641794761

theorem tailTrace_732291 : CollatzResearch.WordTrace tailWord_732291 prefixEnd_732291 376017261961699641794761 := by
  unfold tailWord_732291
  simp only [CollatzResearch.WordTrace]
  refine ⟨26708846990042247190948727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17805897993361498127299151 26708846990042247190948727)
  ·
    refine ⟨40063270485063370786423091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26708846990042247190948727 40063270485063370786423091)
    ·
      refine ⟨60094905727595056179634637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40063270485063370786423091 60094905727595056179634637)
      ·
        refine ⟨22535589647848146067362989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60094905727595056179634637 22535589647848146067362989)
        ·
          refine ⟨8450846117943054775261121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22535589647848146067362989 8450846117943054775261121)
          ·
            refine ⟨6338134588457291081445841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8450846117943054775261121 6338134588457291081445841)
            ·
              refine ⟨4753600941342968311084381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6338134588457291081445841 4753600941342968311084381)
              ·
                refine ⟨1782600353003613116656643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4753600941342968311084381 1782600353003613116656643)
                ·
                  refine ⟨2673900529505419674984965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782600353003613116656643 2673900529505419674984965)
                  ·
                    refine ⟨501356349282266189059681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2673900529505419674984965 501356349282266189059681)
                    ·
                      refine ⟨376017261961699641794761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 501356349282266189059681 376017261961699641794761)
                      ·
                        rfl

theorem cell23_732291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 4, 2].length) (baseStart_732291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732291 prefixEnd_732291 := by exact prefixLift 732291
  have htrace : WordTrace (prefixWord ++ tailWord_732291) baseStart_732291 baseEnd_732291 := by
    simpa [prefixWord, tailWord_732291, baseEnd_732291] using wordTrace_append hprefix tailTrace_732291
  have hstable : (prefixWord ++ tailWord_732291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732291).length < 2 ^ (prefixWord ++ tailWord_732291).sum := by decide
  have hdescent : baseEnd_732291 < baseStart_732291 := by decide
  rcases family_descends (prefixWord ++ tailWord_732291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732325 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 2, 2, 2]
def baseStart_732325 : Nat := 118140960795 + 732325 * 2 ^ 59
def prefixEnd_732325 : Nat := 4983230072969 + 3 ^ 40 * 732325 * 2
def baseEnd_732325 : Nat := 376034720303952508769605

theorem tailTrace_732325 : CollatzResearch.WordTrace tailWord_732325 prefixEnd_732325 376034720303952508769605 := by
  unfold tailWord_732325
  simp only [CollatzResearch.WordTrace]
  refine ⟨26710087071919070997686429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17806724714612713998457619 26710087071919070997686429)
  ·
    refine ⟨10016282651969651624132411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26710087071919070997686429 10016282651969651624132411)
    ·
      refine ⟨15024423977954477436198617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10016282651969651624132411 15024423977954477436198617)
      ·
        refine ⟨11268317983465858077148963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15024423977954477436198617 11268317983465858077148963)
        ·
          refine ⟨16902476975198787115723445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11268317983465858077148963 16902476975198787115723445)
          ·
            refine ⟨1584607216424886292099073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16902476975198787115723445 1584607216424886292099073)
            ·
              refine ⟨1188455412318664719074305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584607216424886292099073 1188455412318664719074305)
              ·
                refine ⟨891341559238998539305729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1188455412318664719074305 891341559238998539305729)
                ·
                  refine ⟨668506169429248904479297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 891341559238998539305729 668506169429248904479297)
                  ·
                    refine ⟨501379627071936678359473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 668506169429248904479297 501379627071936678359473)
                    ·
                      refine ⟨376034720303952508769605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 501379627071936678359473 376034720303952508769605)
                      ·
                        rfl

theorem cell23_732325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_732325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732325 prefixEnd_732325 := by exact prefixLift 732325
  have htrace : WordTrace (prefixWord ++ tailWord_732325) baseStart_732325 baseEnd_732325 := by
    simpa [prefixWord, tailWord_732325, baseEnd_732325] using wordTrace_append hprefix tailTrace_732325
  have hstable : (prefixWord ++ tailWord_732325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732325).length < 2 ^ (prefixWord ++ tailWord_732325).sum := by decide
  have hdescent : baseEnd_732325 < baseStart_732325 := by decide
  rcases family_descends (prefixWord ++ tailWord_732325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732398 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_732398 : Nat := 118140960795 + 732398 * 2 ^ 59
def prefixEnd_732398 : Nat := 4983230072969 + 3 ^ 40 * 732398 * 2
def baseEnd_732398 : Nat := 376072204391730723156769

theorem tailTrace_732398 : CollatzResearch.WordTrace tailWord_732398 prefixEnd_732398 376072204391730723156769 := by
  unfold tailWord_732398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3339093700081825558136731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17808499733769736310062565 3339093700081825558136731)
  ·
    refine ⟨5008640550122738337205097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3339093700081825558136731 5008640550122738337205097)
    ·
      refine ⟨3756480412592053752903823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5008640550122738337205097 3756480412592053752903823)
      ·
        refine ⟨5634720618888080629355735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3756480412592053752903823 5634720618888080629355735)
        ·
          refine ⟨8452080928332120944033603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5634720618888080629355735 8452080928332120944033603)
          ·
            refine ⟨12678121392498181416050405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8452080928332120944033603 12678121392498181416050405)
            ·
              refine ⟨2377147761093409015509451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12678121392498181416050405 2377147761093409015509451)
              ·
                refine ⟨3565721641640113523264177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377147761093409015509451 3565721641640113523264177)
                ·
                  refine ⟨2674291231230085142448133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3565721641640113523264177 2674291231230085142448133)
                  ·
                    refine ⟨501429605855640964209025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2674291231230085142448133 501429605855640964209025)
                    ·
                      refine ⟨376072204391730723156769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 501429605855640964209025 376072204391730723156769)
                      ·
                        rfl

theorem cell23_732398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_732398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732398 prefixEnd_732398 := by exact prefixLift 732398
  have htrace : WordTrace (prefixWord ++ tailWord_732398) baseStart_732398 baseEnd_732398 := by
    simpa [prefixWord, tailWord_732398, baseEnd_732398] using wordTrace_append hprefix tailTrace_732398
  have hstable : (prefixWord ++ tailWord_732398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732398).length < 2 ^ (prefixWord ++ tailWord_732398).sum := by decide
  have hdescent : baseEnd_732398 < baseStart_732398 := by decide
  rcases family_descends (prefixWord ++ tailWord_732398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732441 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 2, 9, 2]
def baseStart_732441 : Nat := 118140960795 + 732441 * 2 ^ 59
def prefixEnd_732441 : Nat := 4983230072969 + 3 ^ 40 * 732441 * 2
def baseEnd_732441 : Nat := 376094284059874054919071

theorem tailTrace_732441 : CollatzResearch.WordTrace tailWord_732441 prefixEnd_732441 376094284059874054919071 := by
  unfold tailWord_732441
  simp only [CollatzResearch.WordTrace]
  refine ⟨26714317939498822808909177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17809545292999215205939451 26714317939498822808909177)
  ·
    refine ⟨20035738454624117106681883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26714317939498822808909177 20035738454624117106681883)
    ·
      refine ⟨30053607681936175660022825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20035738454624117106681883 30053607681936175660022825)
      ·
        refine ⟨22540205761452131745017119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30053607681936175660022825 22540205761452131745017119)
        ·
          refine ⟨33810308642178197617525679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22540205761452131745017119 33810308642178197617525679)
          ·
            refine ⟨50715462963267296426288519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33810308642178197617525679 50715462963267296426288519)
            ·
              refine ⟨76073194444900944639432779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50715462963267296426288519 76073194444900944639432779)
              ·
                refine ⟨114109791667351416959149169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76073194444900944639432779 114109791667351416959149169)
                ·
                  refine ⟨85582343750513562719361877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114109791667351416959149169 85582343750513562719361877)
                  ·
                    refine ⟨501459045413165406558761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 85582343750513562719361877 501459045413165406558761)
                    ·
                      refine ⟨376094284059874054919071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 501459045413165406558761 376094284059874054919071)
                      ·
                        rfl

theorem cell23_732441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 9, 2].length) (baseStart_732441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732441 prefixEnd_732441 := by exact prefixLift 732441
  have htrace : WordTrace (prefixWord ++ tailWord_732441) baseStart_732441 baseEnd_732441 := by
    simpa [prefixWord, tailWord_732441, baseEnd_732441] using wordTrace_append hprefix tailTrace_732441
  have hstable : (prefixWord ++ tailWord_732441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732441).length < 2 ^ (prefixWord ++ tailWord_732441).sum := by decide
  have hdescent : baseEnd_732441 < baseStart_732441 := by decide
  rcases family_descends (prefixWord ++ tailWord_732441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732442 : List Nat := [3, 1, 1, 3, 3, 2, 3, 2, 1, 4]
def baseStart_732442 : Nat := 118140960795 + 732442 * 2 ^ 59
def prefixEnd_732442 : Nat := 4983230072969 + 3 ^ 40 * 732442 * 2
def baseEnd_732442 : Nat := 125364932513509517002189

theorem tailTrace_732442 : CollatzResearch.WordTrace tailWord_732442 prefixEnd_732442 125364932513509517002189 := by
  unfold tailWord_732442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6678588603123799994923895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17809569608330133319797053 6678588603123799994923895)
  ·
    refine ⟨10017882904685699992385843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6678588603123799994923895 10017882904685699992385843)
    ·
      refine ⟨15026824357028549988578765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10017882904685699992385843 15026824357028549988578765)
      ·
        refine ⟨5635059133885706245717037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15026824357028549988578765 5635059133885706245717037)
        ·
          refine ⟨2113147175207139842143889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5635059133885706245717037 2113147175207139842143889)
          ·
            refine ⟨1584860381405354881607917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2113147175207139842143889 1584860381405354881607917)
            ·
              refine ⟨594322643027008080602969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1584860381405354881607917 594322643027008080602969)
              ·
                refine ⟨445741982270256060452227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594322643027008080602969 445741982270256060452227)
                ·
                  refine ⟨668612973405384090678341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445741982270256060452227 668612973405384090678341)
                  ·
                    refine ⟨125364932513509517002189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 668612973405384090678341 125364932513509517002189)
                    ·
                      rfl

theorem cell23_732442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_732442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732442 prefixEnd_732442 := by exact prefixLift 732442
  have htrace : WordTrace (prefixWord ++ tailWord_732442) baseStart_732442 baseEnd_732442 := by
    simpa [prefixWord, tailWord_732442, baseEnd_732442] using wordTrace_append hprefix tailTrace_732442
  have hstable : (prefixWord ++ tailWord_732442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732442).length < 2 ^ (prefixWord ++ tailWord_732442).sum := by decide
  have hdescent : baseEnd_732442 < baseStart_732442 := by decide
  rcases family_descends (prefixWord ++ tailWord_732442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732468 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_732468 : Nat := 118140960795 + 732468 * 2 ^ 59
def prefixEnd_732468 : Nat := 4983230072969 + 3 ^ 40 * 732468 * 2
def baseEnd_732468 : Nat := 125369382679181816427149

theorem tailTrace_732468 : CollatzResearch.WordTrace tailWord_732468 prefixEnd_732468 125369382679181816427149 := by
  unfold tailWord_732468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13357651355200503210071029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17810201806934004280094705 13357651355200503210071029)
  ·
    refine ⟨1252279814550047175944159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13357651355200503210071029 1252279814550047175944159)
    ·
      refine ⟨1878419721825070763916239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252279814550047175944159 1878419721825070763916239)
      ·
        refine ⟨2817629582737606145874359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1878419721825070763916239 2817629582737606145874359)
        ·
          refine ⟨4226444374106409218811539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2817629582737606145874359 4226444374106409218811539)
          ·
            refine ⟨6339666561159613828217309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4226444374106409218811539 6339666561159613828217309)
            ·
              refine ⟨2377374960434855185581491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6339666561159613828217309 2377374960434855185581491)
              ·
                refine ⟨3566062440652282778372237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377374960434855185581491 3566062440652282778372237)
                ·
                  refine ⟨1337273415244606041889589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3566062440652282778372237 1337273415244606041889589)
                  ·
                    refine ⟨125369382679181816427149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1337273415244606041889589 125369382679181816427149)
                    ·
                      rfl

theorem cell23_732468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_732468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732468 prefixEnd_732468 := by exact prefixLift 732468
  have htrace : WordTrace (prefixWord ++ tailWord_732468) baseStart_732468 baseEnd_732468 := by
    simpa [prefixWord, tailWord_732468, baseEnd_732468] using wordTrace_append hprefix tailTrace_732468
  have hstable : (prefixWord ++ tailWord_732468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732468).length < 2 ^ (prefixWord ++ tailWord_732468).sum := by decide
  have hdescent : baseEnd_732468 < baseStart_732468 := by decide
  rcases family_descends (prefixWord ++ tailWord_732468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732493 : List Nat := [1, 6, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_732493 : Nat := 118140960795 + 732493 * 2 ^ 59
def prefixEnd_732493 : Nat := 4983230072969 + 3 ^ 40 * 732493 * 2
def baseEnd_732493 : Nat := 125373661684635950489611

theorem tailTrace_732493 : CollatzResearch.WordTrace tailWord_732493 prefixEnd_732493 125373661684635950489611 := by
  unfold tailWord_732493
  simp only [CollatzResearch.WordTrace]
  refine ⟨26716214535310435689802133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17810809690206957126534755 26716214535310435689802133)
  ·
    refine ⟨1252322556342676672959475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26716214535310435689802133 1252322556342676672959475)
    ·
      refine ⟨1878483834514015009439213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252322556342676672959475 1878483834514015009439213)
      ·
        refine ⟨704431437942755628539705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1878483834514015009439213 704431437942755628539705)
        ·
          refine ⟨528323578457066721404779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704431437942755628539705 528323578457066721404779)
          ·
            refine ⟨792485367685600082107169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528323578457066721404779 792485367685600082107169)
            ·
              refine ⟨594364025764200061580377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792485367685600082107169 594364025764200061580377)
              ·
                refine ⟨445773019323150046185283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594364025764200061580377 445773019323150046185283)
                ·
                  refine ⟨668659528984725069277925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445773019323150046185283 668659528984725069277925)
                  ·
                    refine ⟨125373661684635950489611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 668659528984725069277925 125373661684635950489611)
                    ·
                      rfl

theorem cell23_732493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_732493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732493 prefixEnd_732493 := by exact prefixLift 732493
  have htrace : WordTrace (prefixWord ++ tailWord_732493) baseStart_732493 baseEnd_732493 := by
    simpa [prefixWord, tailWord_732493, baseEnd_732493] using wordTrace_append hprefix tailTrace_732493
  have hstable : (prefixWord ++ tailWord_732493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732493).length < 2 ^ (prefixWord ++ tailWord_732493).sum := by decide
  have hdescent : baseEnd_732493 < baseStart_732493 := by decide
  rcases family_descends (prefixWord ++ tailWord_732493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732526 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_732526 : Nat := 118140960795 + 732526 * 2 ^ 59
def prefixEnd_732526 : Nat := 4983230072969 + 3 ^ 40 * 732526 * 2
def baseEnd_732526 : Nat := 376137929915506222356181

theorem tailTrace_732526 : CollatzResearch.WordTrace tailWord_732526 prefixEnd_732526 376137929915506222356181 := by
  unfold tailWord_732526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3339677268023860290719179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17811612096127254883835621 3339677268023860290719179)
  ·
    refine ⟨5009515902035790436078769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3339677268023860290719179 5009515902035790436078769)
    ·
      refine ⟨3757136926526842827059077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5009515902035790436078769 3757136926526842827059077)
      ·
        refine ⟨704463173723783030073577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3757136926526842827059077 704463173723783030073577)
        ·
          refine ⟨528347380292837272555183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704463173723783030073577 528347380292837272555183)
          ·
            refine ⟨792521070439255908832775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528347380292837272555183 792521070439255908832775)
            ·
              refine ⟨1188781605658883863249163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792521070439255908832775 1188781605658883863249163)
              ·
                refine ⟨1783172408488325794873745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188781605658883863249163 1783172408488325794873745)
                ·
                  refine ⟨1337379306366244346155309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1783172408488325794873745 1337379306366244346155309)
                  ·
                    refine ⟨501517239887341629808241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1337379306366244346155309 501517239887341629808241)
                    ·
                      refine ⟨376137929915506222356181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 501517239887341629808241 376137929915506222356181)
                      ·
                        rfl

theorem cell23_732526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_732526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732526 prefixEnd_732526 := by exact prefixLift 732526
  have htrace : WordTrace (prefixWord ++ tailWord_732526) baseStart_732526 baseEnd_732526 := by
    simpa [prefixWord, tailWord_732526, baseEnd_732526] using wordTrace_append hprefix tailTrace_732526
  have hstable : (prefixWord ++ tailWord_732526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732526).length < 2 ^ (prefixWord ++ tailWord_732526).sum := by decide
  have hdescent : baseEnd_732526 < baseStart_732526 := by decide
  rcases family_descends (prefixWord ++ tailWord_732526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732538 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3]
def baseStart_732538 : Nat := 118140960795 + 732538 * 2 ^ 59
def prefixEnd_732538 : Nat := 4983230072969 + 3 ^ 40 * 732538 * 2
def baseEnd_732538 : Nat := 376144091683360175406125

theorem tailTrace_732538 : CollatzResearch.WordTrace tailWord_732538 prefixEnd_732538 376144091683360175406125 := by
  unfold tailWord_732538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6679463955036852093797567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17811903880098272250126845 6679463955036852093797567)
  ·
    refine ⟨10019195932555278140696351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6679463955036852093797567 10019195932555278140696351)
    ·
      refine ⟨15028793898832917211044527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10019195932555278140696351 15028793898832917211044527)
      ·
        refine ⟨22543190848249375816566791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15028793898832917211044527 22543190848249375816566791)
        ·
          refine ⟨33814786272374063724850187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22543190848249375816566791 33814786272374063724850187)
          ·
            refine ⟨50722179408561095587275281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33814786272374063724850187 50722179408561095587275281)
            ·
              refine ⟨38041634556420821690456461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50722179408561095587275281 38041634556420821690456461)
              ·
                refine ⟨14265612958657808133921173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38041634556420821690456461 14265612958657808133921173)
                ·
                  refine ⟨668700607437084756277555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14265612958657808133921173 668700607437084756277555)
                  ·
                    refine ⟨1003050911155627134416333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 668700607437084756277555 1003050911155627134416333)
                    ·
                      refine ⟨376144091683360175406125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1003050911155627134416333 376144091683360175406125)
                      ·
                        rfl

theorem cell23_732538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_732538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732538 prefixEnd_732538 := by exact prefixLift 732538
  have htrace : WordTrace (prefixWord ++ tailWord_732538) baseStart_732538 baseEnd_732538 := by
    simpa [prefixWord, tailWord_732538, baseEnd_732538] using wordTrace_append hprefix tailTrace_732538
  have hstable : (prefixWord ++ tailWord_732538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732538).length < 2 ^ (prefixWord ++ tailWord_732538).sum := by decide
  have hdescent : baseEnd_732538 < baseStart_732538 := by decide
  rcases family_descends (prefixWord ++ tailWord_732538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732591 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 4]
def baseStart_732591 : Nat := 118140960795 + 732591 * 2 ^ 59
def prefixEnd_732591 : Nat := 4983230072969 + 3 ^ 40 * 732591 * 2
def baseEnd_732591 : Nat := 376171306158048468043381

theorem tailTrace_732591 : CollatzResearch.WordTrace tailWord_732591 prefixEnd_732591 376171306158048468043381 := by
  unfold tailWord_732591
  simp only [CollatzResearch.WordTrace]
  refine ⟨26719788888955398426869627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17813192592636932284579751 26719788888955398426869627)
  ·
    refine ⟨40079683333433097640304441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26719788888955398426869627 40079683333433097640304441)
    ·
      refine ⟨30059762500074823230228331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40079683333433097640304441 30059762500074823230228331)
      ·
        refine ⟨45089643750112234845342497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30059762500074823230228331 45089643750112234845342497)
        ·
          refine ⟨33817232812584176134006873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45089643750112234845342497 33817232812584176134006873)
          ·
            refine ⟨25362924609438132100505155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33817232812584176134006873 25362924609438132100505155)
            ·
              refine ⟨38044386914157198150757733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25362924609438132100505155 38044386914157198150757733)
              ·
                refine ⟨7133322546404474653267075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38044386914157198150757733 7133322546404474653267075)
                ·
                  refine ⟨10699983819606711979900613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7133322546404474653267075 10699983819606711979900613)
                  ·
                    refine ⟨2006246966176258496231365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10699983819606711979900613 2006246966176258496231365)
                    ·
                      refine ⟨376171306158048468043381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2006246966176258496231365 376171306158048468043381)
                      ·
                        rfl

theorem cell23_732591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_732591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732591 prefixEnd_732591 := by exact prefixLift 732591
  have htrace : WordTrace (prefixWord ++ tailWord_732591) baseStart_732591 baseEnd_732591 := by
    simpa [prefixWord, tailWord_732591, baseEnd_732591] using wordTrace_append hprefix tailTrace_732591
  have hstable : (prefixWord ++ tailWord_732591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732591).length < 2 ^ (prefixWord ++ tailWord_732591).sum := by decide
  have hdescent : baseEnd_732591 < baseStart_732591 := by decide
  rcases family_descends (prefixWord ++ tailWord_732591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732618 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 7]
def baseStart_732618 : Nat := 118140960795 + 732618 * 2 ^ 59
def prefixEnd_732618 : Nat := 4983230072969 + 3 ^ 40 * 732618 * 2
def baseEnd_732618 : Nat := 41798352237302206933973

theorem tailTrace_732618 : CollatzResearch.WordTrace tailWord_732618 prefixEnd_732618 41798352237302206933973 := by
  unfold tailWord_732618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6680193414964395509525627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17813849106571721358735005 6680193414964395509525627)
  ·
    refine ⟨10020290122446593264288441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6680193414964395509525627 10020290122446593264288441)
    ·
      refine ⟨7515217591834944948216331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10020290122446593264288441 7515217591834944948216331)
      ·
        refine ⟨11272826387752417422324497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7515217591834944948216331 11272826387752417422324497)
        ·
          refine ⟨8454619790814313066743373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11272826387752417422324497 8454619790814313066743373)
          ·
            refine ⟨3170482421555367400028765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8454619790814313066743373 3170482421555367400028765)
            ·
              refine ⟨1188930908083262775010787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3170482421555367400028765 1188930908083262775010787)
              ·
                refine ⟨1783396362124894162516181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188930908083262775010787 1783396362124894162516181)
                ·
                  refine ⟨41798352237302206933973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1783396362124894162516181 41798352237302206933973)
                  ·
                    rfl

theorem cell23_732618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_732618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732618 prefixEnd_732618 := by exact prefixLift 732618
  have htrace : WordTrace (prefixWord ++ tailWord_732618) baseStart_732618 baseEnd_732618 := by
    simpa [prefixWord, tailWord_732618, baseEnd_732618] using wordTrace_append hprefix tailTrace_732618
  have hstable : (prefixWord ++ tailWord_732618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732618).length < 2 ^ (prefixWord ++ tailWord_732618).sum := by decide
  have hdescent : baseEnd_732618 < baseStart_732618 := by decide
  rcases family_descends (prefixWord ++ tailWord_732618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732631 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 3, 7]
def baseStart_732631 : Nat := 118140960795 + 732631 * 2 ^ 59
def prefixEnd_732631 : Nat := 4983230072969 + 3 ^ 40 * 732631 * 2
def baseEnd_732631 : Nat := 125397281794742770514399

theorem tailTrace_732631 : CollatzResearch.WordTrace tailWord_732631 prefixEnd_732631 125397281794742770514399 := by
  unfold tailWord_732631
  simp only [CollatzResearch.WordTrace]
  refine ⟨26721247808810485258325747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17814165205873656838883831 26721247808810485258325747)
  ·
    refine ⟨40081871713215727887488621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26721247808810485258325747 40081871713215727887488621)
    ·
      refine ⟨15030701892455897957808233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40081871713215727887488621 15030701892455897957808233)
      ·
        refine ⟨11273026419341923468356175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15030701892455897957808233 11273026419341923468356175)
        ·
          refine ⟨16909539629012885202534263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11273026419341923468356175 16909539629012885202534263)
          ·
            refine ⟨25364309443519327803801395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16909539629012885202534263 25364309443519327803801395)
            ·
              refine ⟨38046464165278991705702093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25364309443519327803801395 38046464165278991705702093)
              ·
                refine ⟨14267424061979621889638285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38046464165278991705702093 14267424061979621889638285)
                ·
                  refine ⟨5350284023242358208614357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14267424061979621889638285 5350284023242358208614357)
                  ·
                    refine ⟨125397281794742770514399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5350284023242358208614357 125397281794742770514399)
                    ·
                      rfl

theorem cell23_732631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_732631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732631 prefixEnd_732631 := by exact prefixLift 732631
  have htrace : WordTrace (prefixWord ++ tailWord_732631) baseStart_732631 baseEnd_732631 := by
    simpa [prefixWord, tailWord_732631, baseEnd_732631] using wordTrace_append hprefix tailTrace_732631
  have hstable : (prefixWord ++ tailWord_732631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732631).length < 2 ^ (prefixWord ++ tailWord_732631).sum := by decide
  have hdescent : baseEnd_732631 < baseStart_732631 := by decide
  rcases family_descends (prefixWord ++ tailWord_732631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732705 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_732705 : Nat := 118140960795 + 732705 * 2 ^ 59
def prefixEnd_732705 : Nat := 4983230072969 + 3 ^ 40 * 732705 * 2
def baseEnd_732705 : Nat := 376229842952661022017857

theorem tailTrace_732705 : CollatzResearch.WordTrace tailWord_732705 prefixEnd_732705 376229842952661022017857 := by
  unfold tailWord_732705
  simp only [CollatzResearch.WordTrace]
  refine ⟨26723946810542395896519569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17815964540361597264346379 26723946810542395896519569)
  ·
    refine ⟨20042960107906796922389677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26723946810542395896519569 20042960107906796922389677)
    ·
      refine ⟨7516110040465048845896129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20042960107906796922389677 7516110040465048845896129)
      ·
        refine ⟨5637082530348786634422097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7516110040465048845896129 5637082530348786634422097)
        ·
          refine ⟨4227811897761589975816573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5637082530348786634422097 4227811897761589975816573)
          ·
            refine ⟨1585429461660596240931215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4227811897761589975816573 1585429461660596240931215)
            ·
              refine ⟨2378144192490894361396823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585429461660596240931215 2378144192490894361396823)
              ·
                refine ⟨3567216288736341542095235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378144192490894361396823 3567216288736341542095235)
                ·
                  refine ⟨5350824433104512313142853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567216288736341542095235 5350824433104512313142853)
                  ·
                    refine ⟨1003279581207096058714285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5350824433104512313142853 1003279581207096058714285)
                    ·
                      refine ⟨376229842952661022017857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1003279581207096058714285 376229842952661022017857)
                      ·
                        rfl

theorem cell23_732705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_732705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732705 prefixEnd_732705 := by exact prefixLift 732705
  have htrace : WordTrace (prefixWord ++ tailWord_732705) baseStart_732705 baseEnd_732705 := by
    simpa [prefixWord, tailWord_732705, baseEnd_732705] using wordTrace_append hprefix tailTrace_732705
  have hstable : (prefixWord ++ tailWord_732705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732705).length < 2 ^ (prefixWord ++ tailWord_732705).sum := by decide
  have hdescent : baseEnd_732705 < baseStart_732705 := by decide
  rcases family_descends (prefixWord ++ tailWord_732705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732725 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 6]
def baseStart_732725 : Nat := 118140960795 + 732725 * 2 ^ 59
def prefixEnd_732725 : Nat := 4983230072969 + 3 ^ 40 * 732725 * 2
def baseEnd_732725 : Nat := 41804456951750104863085

theorem tailTrace_732725 : CollatzResearch.WordTrace tailWord_732725 prefixEnd_732725 41804456951750104863085 := by
  unfold tailWord_732725
  simp only [CollatzResearch.WordTrace]
  refine ⟨26724676270469939312247629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17816450846979959541498419 26724676270469939312247629)
  ·
    refine ⟨10021753601426227242092861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26724676270469939312247629 10021753601426227242092861)
    ·
      refine ⟨3758157600534835215784823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10021753601426227242092861 3758157600534835215784823)
      ·
        refine ⟨5637236400802252823677235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3758157600534835215784823 5637236400802252823677235)
        ·
          refine ⟨8455854601203379235515853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5637236400802252823677235 8455854601203379235515853)
          ·
            refine ⟨3170945475451267213318445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8455854601203379235515853 3170945475451267213318445)
            ·
              refine ⟨1189104553294225204994417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3170945475451267213318445 1189104553294225204994417)
              ·
                refine ⟨891828414970668903745813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1189104553294225204994417 891828414970668903745813)
                ·
                  refine ⟨41804456951750104863085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 891828414970668903745813 41804456951750104863085)
                  ·
                    rfl

theorem cell23_732725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_732725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732725 prefixEnd_732725 := by exact prefixLift 732725
  have htrace : WordTrace (prefixWord ++ tailWord_732725) baseStart_732725 baseEnd_732725 := by
    simpa [prefixWord, tailWord_732725, baseEnd_732725] using wordTrace_append hprefix tailTrace_732725
  have hstable : (prefixWord ++ tailWord_732725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732725).length < 2 ^ (prefixWord ++ tailWord_732725).sum := by decide
  have hdescent : baseEnd_732725 < baseStart_732725 := by decide
  rcases family_descends (prefixWord ++ tailWord_732725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732728 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_732728 : Nat := 118140960795 + 732728 * 2 ^ 59
def prefixEnd_732728 : Nat := 4983230072969 + 3 ^ 40 * 732728 * 2
def baseEnd_732728 : Nat := 376241653007714432030251

theorem tailTrace_732728 : CollatzResearch.WordTrace tailWord_732728 prefixEnd_732728 376241653007714432030251 := by
  unfold tailWord_732728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13362392844729535412303419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17816523792972713883071225 13362392844729535412303419)
  ·
    refine ⟨20043589267094303118455129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13362392844729535412303419 20043589267094303118455129)
    ·
      refine ⟨15032691950320727338841347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20043589267094303118455129 15032691950320727338841347)
      ·
        refine ⟨22549037925481091008262021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15032691950320727338841347 22549037925481091008262021)
        ·
          refine ⟨4227944611027704564049129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22549037925481091008262021 4227944611027704564049129)
          ·
            refine ⟨3170958458270778423036847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4227944611027704564049129 3170958458270778423036847)
            ·
              refine ⟨4756437687406167634555271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3170958458270778423036847 4756437687406167634555271)
              ·
                refine ⟨7134656531109251451832907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4756437687406167634555271 7134656531109251451832907)
                ·
                  refine ⟨10701984796663877177749361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7134656531109251451832907 10701984796663877177749361)
                  ·
                    refine ⟨8026488597497907883312021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10701984796663877177749361 8026488597497907883312021)
                    ·
                      refine ⟨376241653007714432030251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8026488597497907883312021 376241653007714432030251)
                      ·
                        rfl

theorem cell23_732728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_732728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732728 prefixEnd_732728 := by exact prefixLift 732728
  have htrace : WordTrace (prefixWord ++ tailWord_732728) baseStart_732728 baseEnd_732728 := by
    simpa [prefixWord, tailWord_732728, baseEnd_732728] using wordTrace_append hprefix tailTrace_732728
  have hstable : (prefixWord ++ tailWord_732728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732728).length < 2 ^ (prefixWord ++ tailWord_732728).sum := by decide
  have hdescent : baseEnd_732728 < baseStart_732728 := by decide
  rcases family_descends (prefixWord ++ tailWord_732728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732768 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 3, 6]
def baseStart_732768 : Nat := 118140960795 + 732768 * 2 ^ 59
def prefixEnd_732768 : Nat := 4983230072969 + 3 ^ 40 * 732768 * 2
def baseEnd_732768 : Nat := 125420730744631425176689

theorem tailTrace_732768 : CollatzResearch.WordTrace tailWord_732768 prefixEnd_732768 125420730744631425176689 := by
  unfold tailWord_732768
  simp only [CollatzResearch.WordTrace]
  refine ⟨13363122304657078828031479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17817496406209438437375305 13363122304657078828031479)
  ·
    refine ⟨20044683456985618242047219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13363122304657078828031479 20044683456985618242047219)
    ·
      refine ⟨30067025185478427363070829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20044683456985618242047219 30067025185478427363070829)
      ·
        refine ⟨11275134444554410261151561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30067025185478427363070829 11275134444554410261151561)
        ·
          refine ⟨8456350833415807695863671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11275134444554410261151561 8456350833415807695863671)
          ·
            refine ⟨12684526250123711543795507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8456350833415807695863671 12684526250123711543795507)
            ·
              refine ⟨19026789375185567315693261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12684526250123711543795507 19026789375185567315693261)
              ·
                refine ⟨7135046015694587743384973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19026789375185567315693261 7135046015694587743384973)
                ·
                  refine ⟨2675642255885470403769365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7135046015694587743384973 2675642255885470403769365)
                  ·
                    refine ⟨125420730744631425176689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2675642255885470403769365 125420730744631425176689)
                    ·
                      rfl

theorem cell23_732768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_732768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732768 prefixEnd_732768 := by exact prefixLift 732768
  have htrace : WordTrace (prefixWord ++ tailWord_732768) baseStart_732768 baseEnd_732768 := by
    simpa [prefixWord, tailWord_732768, baseEnd_732768] using wordTrace_append hprefix tailTrace_732768
  have hstable : (prefixWord ++ tailWord_732768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732768).length < 2 ^ (prefixWord ++ tailWord_732768).sum := by decide
  have hdescent : baseEnd_732768 < baseStart_732768 := by decide
  rcases family_descends (prefixWord ++ tailWord_732768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732795 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 3]
def baseStart_732795 : Nat := 118140960795 + 732795 * 2 ^ 59
def prefixEnd_732795 : Nat := 4983230072969 + 3 ^ 40 * 732795 * 2
def baseEnd_732795 : Nat := 376276056211565669892443

theorem tailTrace_732795 : CollatzResearch.WordTrace tailWord_732795 prefixEnd_732795 376276056211565669892443 := by
  unfold tailWord_732795
  simp only [CollatzResearch.WordTrace]
  refine ⟨26727229380216341267295839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17818152920144227511530559 26727229380216341267295839)
  ·
    refine ⟨40090844070324511900943759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26727229380216341267295839 40090844070324511900943759)
    ·
      refine ⟨60136266105486767851415639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40090844070324511900943759 60136266105486767851415639)
      ·
        refine ⟨90204399158230151777123459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60136266105486767851415639 90204399158230151777123459)
        ·
          refine ⟨135306598737345227665685189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90204399158230151777123459 135306598737345227665685189)
          ·
            refine ⟨25369987263252230187315973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135306598737345227665685189 25369987263252230187315973)
            ·
              refine ⟨4756872611859793160121745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25369987263252230187315973 4756872611859793160121745)
              ·
                refine ⟨3567654458894844870091309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4756872611859793160121745 3567654458894844870091309)
                ·
                  refine ⟨1337870422085566826284241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3567654458894844870091309 1337870422085566826284241)
                  ·
                    refine ⟨1003402816564175119713181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1337870422085566826284241 1003402816564175119713181)
                    ·
                      refine ⟨376276056211565669892443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1003402816564175119713181 376276056211565669892443)
                      ·
                        rfl

theorem cell23_732795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 3].length) (baseStart_732795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732795 prefixEnd_732795 := by exact prefixLift 732795
  have htrace : WordTrace (prefixWord ++ tailWord_732795) baseStart_732795 baseEnd_732795 := by
    simpa [prefixWord, tailWord_732795, baseEnd_732795] using wordTrace_append hprefix tailTrace_732795
  have hstable : (prefixWord ++ tailWord_732795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732795).length < 2 ^ (prefixWord ++ tailWord_732795).sum := by decide
  have hdescent : baseEnd_732795 < baseStart_732795 := by decide
  rcases family_descends (prefixWord ++ tailWord_732795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732805 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_732805 : Nat := 118140960795 + 732805 * 2 ^ 59
def prefixEnd_732805 : Nat := 4983230072969 + 3 ^ 40 * 732805 * 2
def baseEnd_732805 : Nat := 376281191018110630767397

theorem tailTrace_732805 : CollatzResearch.WordTrace tailWord_732805 prefixEnd_732805 376281191018110630767397 := by
  unfold tailWord_732805
  simp only [CollatzResearch.WordTrace]
  refine ⟨26727594110180112975159869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17818396073453408650106579 26727594110180112975159869)
  ·
    refine ⟨10022847791317542365684951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26727594110180112975159869 10022847791317542365684951)
    ·
      refine ⟨15034271686976313548527427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10022847791317542365684951 15034271686976313548527427)
      ·
        refine ⟨22551407530464470322791141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15034271686976313548527427 22551407530464470322791141)
        ·
          refine ⟨4228388911962088185523339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22551407530464470322791141 4228388911962088185523339)
          ·
            refine ⟨6342583367943132278285009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4228388911962088185523339 6342583367943132278285009)
            ·
              refine ⟨4756937525957349208713757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6342583367943132278285009 4756937525957349208713757)
              ·
                refine ⟨1783851572234005953267659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4756937525957349208713757 1783851572234005953267659)
                ·
                  refine ⟨2675777358351008929901489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783851572234005953267659 2675777358351008929901489)
                  ·
                    refine ⟨2006833018763256697426117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2675777358351008929901489 2006833018763256697426117)
                    ·
                      refine ⟨376281191018110630767397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2006833018763256697426117 376281191018110630767397)
                      ·
                        rfl

theorem cell23_732805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_732805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732805 prefixEnd_732805 := by exact prefixLift 732805
  have htrace : WordTrace (prefixWord ++ tailWord_732805) baseStart_732805 baseEnd_732805 := by
    simpa [prefixWord, tailWord_732805, baseEnd_732805] using wordTrace_append hprefix tailTrace_732805
  have hstable : (prefixWord ++ tailWord_732805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732805).length < 2 ^ (prefixWord ++ tailWord_732805).sum := by decide
  have hdescent : baseEnd_732805 < baseStart_732805 := by decide
  rcases family_descends (prefixWord ++ tailWord_732805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732845 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_732845 : Nat := 118140960795 + 732845 * 2 ^ 59
def prefixEnd_732845 : Nat := 4983230072969 + 3 ^ 40 * 732845 * 2
def baseEnd_732845 : Nat := 125433910081430158089071

theorem tailTrace_732845 : CollatzResearch.WordTrace tailWord_732845 prefixEnd_732845 125433910081430158089071 := by
  unfold tailWord_732845
  simp only [CollatzResearch.WordTrace]
  refine ⟨26729053030035199806615989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17819368686690133204410659 26729053030035199806615989)
  ·
    refine ⟨2505848721565799981870249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26729053030035199806615989 2505848721565799981870249)
    ·
      refine ⟨1879386541174349986402687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2505848721565799981870249 1879386541174349986402687)
      ·
        refine ⟨2819079811761524979604031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1879386541174349986402687 2819079811761524979604031)
        ·
          refine ⟨4228619717642287469406047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2819079811761524979604031 4228619717642287469406047)
          ·
            refine ⟨6342929576463431204109071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4228619717642287469406047 6342929576463431204109071)
            ·
              refine ⟨9514394364695146806163607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6342929576463431204109071 9514394364695146806163607)
              ·
                refine ⟨14271591547042720209245411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9514394364695146806163607 14271591547042720209245411)
                ·
                  refine ⟨21407387320564080313868117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14271591547042720209245411 21407387320564080313868117)
                  ·
                    refine ⟨125433910081430158089071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 21407387320564080313868117 125433910081430158089071)
                    ·
                      rfl

theorem cell23_732845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_732845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732845 prefixEnd_732845 := by exact prefixLift 732845
  have htrace : WordTrace (prefixWord ++ tailWord_732845) baseStart_732845 baseEnd_732845 := by
    simpa [prefixWord, tailWord_732845, baseEnd_732845] using wordTrace_append hprefix tailTrace_732845
  have hstable : (prefixWord ++ tailWord_732845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732845).length < 2 ^ (prefixWord ++ tailWord_732845).sum := by decide
  have hdescent : baseEnd_732845 < baseStart_732845 := by decide
  rcases family_descends (prefixWord ++ tailWord_732845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732895 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 4]
def baseStart_732895 : Nat := 118140960795 + 732895 * 2 ^ 59
def prefixEnd_732895 : Nat := 4983230072969 + 3 ^ 40 * 732895 * 2
def baseEnd_732895 : Nat := 376327404277015278641983

theorem tailTrace_732895 : CollatzResearch.WordTrace tailWord_732895 prefixEnd_732895 376327404277015278641983 := by
  unfold tailWord_732895
  simp only [CollatzResearch.WordTrace]
  refine ⟨26730876679854058345936139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17820584453236038897290759 26730876679854058345936139)
  ·
    refine ⟨40096315019781087518904209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26730876679854058345936139 40096315019781087518904209)
    ·
      refine ⟨30072236264835815639178157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40096315019781087518904209 30072236264835815639178157)
      ·
        refine ⟨11277088599313430864691809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30072236264835815639178157 11277088599313430864691809)
        ·
          refine ⟨8457816449485073148518857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11277088599313430864691809 8457816449485073148518857)
          ·
            refine ⟨6343362337113804861389143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8457816449485073148518857 6343362337113804861389143)
            ·
              refine ⟨9515043505670707292083715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6343362337113804861389143 9515043505670707292083715)
              ·
                refine ⟨14272565258506060938125573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9515043505670707292083715 14272565258506060938125573)
                ·
                  refine ⟨2676105985969886425898545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14272565258506060938125573 2676105985969886425898545)
                  ·
                    refine ⟨2007079489477414819423909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2676105985969886425898545 2007079489477414819423909)
                    ·
                      refine ⟨376327404277015278641983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2007079489477414819423909 376327404277015278641983)
                      ·
                        rfl

theorem cell23_732895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_732895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732895 prefixEnd_732895 := by exact prefixLift 732895
  have htrace : WordTrace (prefixWord ++ tailWord_732895) baseStart_732895 baseEnd_732895 := by
    simpa [prefixWord, tailWord_732895, baseEnd_732895] using wordTrace_append hprefix tailTrace_732895
  have hstable : (prefixWord ++ tailWord_732895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732895).length < 2 ^ (prefixWord ++ tailWord_732895).sum := by decide
  have hdescent : baseEnd_732895 < baseStart_732895 := by decide
  rcases family_descends (prefixWord ++ tailWord_732895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732945 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_732945 : Nat := 118140960795 + 732945 * 2 ^ 59
def prefixEnd_732945 : Nat := 4983230072969 + 3 ^ 40 * 732945 * 2
def baseEnd_732945 : Nat := 376353078309740083016753

theorem tailTrace_732945 : CollatzResearch.WordTrace tailWord_732945 prefixEnd_732945 376353078309740083016753 := by
  unfold tailWord_732945
  simp only [CollatzResearch.WordTrace]
  refine ⟨26732700329672916885256289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17821800219781944590170859 26732700329672916885256289)
  ·
    refine ⟨20049525247254687663942217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26732700329672916885256289 20049525247254687663942217)
    ·
      refine ⟨15037143935441015747956663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20049525247254687663942217 15037143935441015747956663)
      ·
        refine ⟨22555715903161523621934995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15037143935441015747956663 22555715903161523621934995)
        ·
          refine ⟨33833573854742285432902493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22555715903161523621934995 33833573854742285432902493)
          ·
            refine ⟨12687590195528357037338435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33833573854742285432902493 12687590195528357037338435)
            ·
              refine ⟨19031385293292535556007653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12687590195528357037338435 19031385293292535556007653)
              ·
                refine ⟨3568384742492350416751435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19031385293292535556007653 3568384742492350416751435)
                ·
                  refine ⟨5352577113738525625127153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3568384742492350416751435 5352577113738525625127153)
                  ·
                    refine ⟨4014432835303894218845365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5352577113738525625127153 4014432835303894218845365)
                    ·
                      refine ⟨376353078309740083016753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4014432835303894218845365 376353078309740083016753)
                      ·
                        rfl

theorem cell23_732945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_732945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732945 prefixEnd_732945 := by exact prefixLift 732945
  have htrace : WordTrace (prefixWord ++ tailWord_732945) baseStart_732945 baseEnd_732945 := by
    simpa [prefixWord, tailWord_732945, baseEnd_732945] using wordTrace_append hprefix tailTrace_732945
  have hstable : (prefixWord ++ tailWord_732945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732945).length < 2 ^ (prefixWord ++ tailWord_732945).sum := by decide
  have hdescent : baseEnd_732945 < baseStart_732945 := by decide
  rcases family_descends (prefixWord ++ tailWord_732945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732962 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_732962 : Nat := 118140960795 + 732962 * 2 ^ 59
def prefixEnd_732962 : Nat := 4983230072969 + 3 ^ 40 * 732962 * 2
def baseEnd_732962 : Nat := 376361807480866516504175

theorem tailTrace_732962 : CollatzResearch.WordTrace tailWord_732962 prefixEnd_732962 376361807480866516504175 := by
  unfold tailWord_732962
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683330092652832197156285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17822213580407552525750093 6683330092652832197156285)
  ·
    refine ⟨2506248784744812073933607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6683330092652832197156285 2506248784744812073933607)
    ·
      refine ⟨3759373177117218110900411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2506248784744812073933607 3759373177117218110900411)
      ·
        refine ⟨5639059765675827166350617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3759373177117218110900411 5639059765675827166350617)
        ·
          refine ⟨4229294824256870374762963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5639059765675827166350617 4229294824256870374762963)
          ·
            refine ⟨6343942236385305562144445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4229294824256870374762963 6343942236385305562144445)
            ·
              refine ⟨2378978338644489585804167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6343942236385305562144445 2378978338644489585804167)
              ·
                refine ⟨3568467507966734378706251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378978338644489585804167 3568467507966734378706251)
                ·
                  refine ⟨5352701261950101568059377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3568467507966734378706251 5352701261950101568059377)
                  ·
                    refine ⟨4014525946462576176044533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5352701261950101568059377 4014525946462576176044533)
                    ·
                      refine ⟨376361807480866516504175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4014525946462576176044533 376361807480866516504175)
                      ·
                        rfl

theorem cell23_732962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_732962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732962 prefixEnd_732962 := by exact prefixLift 732962
  have htrace : WordTrace (prefixWord ++ tailWord_732962) baseStart_732962 baseEnd_732962 := by
    simpa [prefixWord, tailWord_732962, baseEnd_732962] using wordTrace_append hprefix tailTrace_732962
  have hstable : (prefixWord ++ tailWord_732962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732962).length < 2 ^ (prefixWord ++ tailWord_732962).sum := by decide
  have hdescent : baseEnd_732962 < baseStart_732962 := by decide
  rcases family_descends (prefixWord ++ tailWord_732962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732989 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_732989 : Nat := 118140960795 + 732989 * 2 ^ 59
def prefixEnd_732989 : Nat := 4983230072969 + 3 ^ 40 * 732989 * 2
def baseEnd_732989 : Nat := 376375671458537910866551

theorem tailTrace_732989 : CollatzResearch.WordTrace tailWord_732989 prefixEnd_732989 376375671458537910866551 := by
  unfold tailWord_732989
  simp only [CollatzResearch.WordTrace]
  refine ⟨26734305141513512399858021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17822870094342341599905347 26734305141513512399858021)
  ·
    refine ⟨5012682214033783574973379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26734305141513512399858021 5012682214033783574973379)
    ·
      refine ⟨7519023321050675362460069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5012682214033783574973379 7519023321050675362460069)
      ·
        refine ⟨1409816872697001630461263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7519023321050675362460069 1409816872697001630461263)
        ·
          refine ⟨2114725309045502445691895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409816872697001630461263 2114725309045502445691895)
          ·
            refine ⟨3172087963568253668537843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2114725309045502445691895 3172087963568253668537843)
            ·
              refine ⟨4758131945352380502806765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3172087963568253668537843 4758131945352380502806765)
              ·
                refine ⟨1784299479507142688552537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4758131945352380502806765 1784299479507142688552537)
                ·
                  refine ⟨1338224609630357016414403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1784299479507142688552537 1338224609630357016414403)
                  ·
                    refine ⟨2007336914445535524621605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1338224609630357016414403 2007336914445535524621605)
                    ·
                      refine ⟨376375671458537910866551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2007336914445535524621605 376375671458537910866551)
                      ·
                        rfl

theorem cell23_732989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_732989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_732989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_732989 prefixEnd_732989 := by exact prefixLift 732989
  have htrace : WordTrace (prefixWord ++ tailWord_732989) baseStart_732989 baseEnd_732989 := by
    simpa [prefixWord, tailWord_732989, baseEnd_732989] using wordTrace_append hprefix tailTrace_732989
  have hstable : (prefixWord ++ tailWord_732989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732989).length < 2 ^ (prefixWord ++ tailWord_732989).sum := by decide
  have hdescent : baseEnd_732989 < baseStart_732989 := by decide
  rcases family_descends (prefixWord ++ tailWord_732989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733009 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 2, 2, 3]
def baseStart_733009 : Nat := 118140960795 + 733009 * 2 ^ 59
def prefixEnd_733009 : Nat := 4983230072969 + 3 ^ 40 * 733009 * 2
def baseEnd_733009 : Nat := 376385941071627832616459

theorem tailTrace_733009 : CollatzResearch.WordTrace tailWord_733009 prefixEnd_733009 376385941071627832616459 := by
  unfold tailWord_733009
  simp only [CollatzResearch.WordTrace]
  refine ⟨26735034601441055815586081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17823356400960703877057387 26735034601441055815586081)
  ·
    refine ⟨20051275951080791861689561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26735034601441055815586081 20051275951080791861689561)
    ·
      refine ⟨15038456963310593896267171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20051275951080791861689561 15038456963310593896267171)
      ·
        refine ⟨22557685444965890844400757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15038456963310593896267171 22557685444965890844400757)
        ·
          refine ⟨2114783010465552266662571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22557685444965890844400757 2114783010465552266662571)
          ·
            refine ⟨3172174515698328399993857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2114783010465552266662571 3172174515698328399993857)
            ·
              refine ⟨2379130886773746299995393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3172174515698328399993857 2379130886773746299995393)
              ·
                refine ⟨1784348165080309724996545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2379130886773746299995393 1784348165080309724996545)
                ·
                  refine ⟨1338261123810232293747409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1784348165080309724996545 1338261123810232293747409)
                  ·
                    refine ⟨1003695842857674220310557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1338261123810232293747409 1003695842857674220310557)
                    ·
                      refine ⟨376385941071627832616459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1003695842857674220310557 376385941071627832616459)
                      ·
                        rfl

theorem cell23_733009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_733009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733009 prefixEnd_733009 := by exact prefixLift 733009
  have htrace : WordTrace (prefixWord ++ tailWord_733009) baseStart_733009 baseEnd_733009 := by
    simpa [prefixWord, tailWord_733009, baseEnd_733009] using wordTrace_append hprefix tailTrace_733009
  have hstable : (prefixWord ++ tailWord_733009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733009).length < 2 ^ (prefixWord ++ tailWord_733009).sum := by decide
  have hdescent : baseEnd_733009 < baseStart_733009 := by decide
  rcases family_descends (prefixWord ++ tailWord_733009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733035 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 7]
def baseStart_733035 : Nat := 118140960795 + 733035 * 2 ^ 59
def prefixEnd_733035 : Nat := 4983230072969 + 3 ^ 40 * 733035 * 2
def baseEnd_733035 : Nat := 376399291568644730891339

theorem tailTrace_733035 : CollatzResearch.WordTrace tailWord_733035 prefixEnd_733035 376399291568644730891339 := by
  unfold tailWord_733035
  simp only [CollatzResearch.WordTrace]
  refine ⟨26735982899346862256032559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17823988599564574837355039 26735982899346862256032559)
  ·
    refine ⟨40103974349020293384048839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26735982899346862256032559 40103974349020293384048839)
    ·
      refine ⟨60155961523530440076073259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40103974349020293384048839 60155961523530440076073259)
      ·
        refine ⟨90233942285295660114109889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60155961523530440076073259 90233942285295660114109889)
        ·
          refine ⟨67675456713971745085582417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90233942285295660114109889 67675456713971745085582417)
          ·
            refine ⟨50756592535478808814186813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67675456713971745085582417 50756592535478808814186813)
            ·
              refine ⟨19033722200804553305320055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50756592535478808814186813 19033722200804553305320055)
              ·
                refine ⟨28550583301206829957980083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19033722200804553305320055 28550583301206829957980083)
                ·
                  refine ⟨42825874951810244936970125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28550583301206829957980083 42825874951810244936970125)
                  ·
                    refine ⟨16059703106928841851363797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42825874951810244936970125 16059703106928841851363797)
                    ·
                      refine ⟨376399291568644730891339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16059703106928841851363797 376399291568644730891339)
                      ·
                        rfl

theorem cell23_733035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_733035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733035 prefixEnd_733035 := by exact prefixLift 733035
  have htrace : WordTrace (prefixWord ++ tailWord_733035) baseStart_733035 baseEnd_733035 := by
    simpa [prefixWord, tailWord_733035, baseEnd_733035] using wordTrace_append hprefix tailTrace_733035
  have hstable : (prefixWord ++ tailWord_733035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733035).length < 2 ^ (prefixWord ++ tailWord_733035).sum := by decide
  have hdescent : baseEnd_733035 < baseStart_733035 := by decide
  rcases family_descends (prefixWord ++ tailWord_733035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733049 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 1, 5, 2]
def baseStart_733049 : Nat := 118140960795 + 733049 * 2 ^ 59
def prefixEnd_733049 : Nat := 4983230072969 + 3 ^ 40 * 733049 * 2
def baseEnd_733049 : Nat := 376406480297807676116275

theorem tailTrace_733049 : CollatzResearch.WordTrace tailWord_733049 prefixEnd_733049 376406480297807676116275 := by
  unfold tailWord_733049
  simp only [CollatzResearch.WordTrace]
  refine ⟨26736493521296142647042201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17824329014197428431361467 26736493521296142647042201)
  ·
    refine ⟨20052370140972106985281651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26736493521296142647042201 20052370140972106985281651)
    ·
      refine ⟨30078555211458160477922477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20052370140972106985281651 30078555211458160477922477)
      ·
        refine ⟨11279458204296810179220929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30078555211458160477922477 11279458204296810179220929)
        ·
          refine ⟨8459593653222607634415697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11279458204296810179220929 8459593653222607634415697)
          ·
            refine ⟨6344695239916955725811773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8459593653222607634415697 6344695239916955725811773)
            ·
              refine ⟨2379260714968858397179415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6344695239916955725811773 2379260714968858397179415)
              ·
                refine ⟨3568891072453287595769123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379260714968858397179415 3568891072453287595769123)
                ·
                  refine ⟨5353336608679931393653685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3568891072453287595769123 5353336608679931393653685)
                  ·
                    refine ⟨501875307063743568155033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5353336608679931393653685 501875307063743568155033)
                    ·
                      refine ⟨376406480297807676116275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 501875307063743568155033 376406480297807676116275)
                      ·
                        rfl

theorem cell23_733049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_733049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733049 prefixEnd_733049 := by exact prefixLift 733049
  have htrace : WordTrace (prefixWord ++ tailWord_733049) baseStart_733049 baseEnd_733049 := by
    simpa [prefixWord, tailWord_733049, baseEnd_733049] using wordTrace_append hprefix tailTrace_733049
  have hstable : (prefixWord ++ tailWord_733049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733049).length < 2 ^ (prefixWord ++ tailWord_733049).sum := by decide
  have hdescent : baseEnd_733049 < baseStart_733049 := by decide
  rcases family_descends (prefixWord ++ tailWord_733049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733059 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 1, 5]
def baseStart_733059 : Nat := 118140960795 + 733059 * 2 ^ 59
def prefixEnd_733059 : Nat := 4983230072969 + 3 ^ 40 * 733059 * 2
def baseEnd_733059 : Nat := 125470538368117545663743

theorem tailTrace_733059 : CollatzResearch.WordTrace tailWord_733059 prefixEnd_733059 125470538368117545663743 := by
  unfold tailWord_733059
  simp only [CollatzResearch.WordTrace]
  refine ⟨26736858251259914354906231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17824572167506609569937487 26736858251259914354906231)
  ·
    refine ⟨40105287376889871532359347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26736858251259914354906231 40105287376889871532359347)
    ·
      refine ⟨60157931065334807298539021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40105287376889871532359347 60157931065334807298539021)
      ·
        refine ⟨22559224149500552736952133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60157931065334807298539021 22559224149500552736952133)
        ·
          refine ⟨4229854528031353638178525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22559224149500552736952133 4229854528031353638178525)
          ·
            refine ⟨1586195448011757614316947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4229854528031353638178525 1586195448011757614316947)
            ·
              refine ⟨2379293172017636421475421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586195448011757614316947 2379293172017636421475421)
              ·
                refine ⟨892234939506613658053283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2379293172017636421475421 892234939506613658053283)
                ·
                  refine ⟨1338352409259920487079925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892234939506613658053283 1338352409259920487079925)
                  ·
                    refine ⟨125470538368117545663743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1338352409259920487079925 125470538368117545663743)
                    ·
                      rfl

theorem cell23_733059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 5].length) (baseStart_733059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733059 prefixEnd_733059 := by exact prefixLift 733059
  have htrace : WordTrace (prefixWord ++ tailWord_733059) baseStart_733059 baseEnd_733059 := by
    simpa [prefixWord, tailWord_733059, baseEnd_733059] using wordTrace_append hprefix tailTrace_733059
  have hstable : (prefixWord ++ tailWord_733059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733059).length < 2 ^ (prefixWord ++ tailWord_733059).sum := by decide
  have hdescent : baseEnd_733059 < baseStart_733059 := by decide
  rcases family_descends (prefixWord ++ tailWord_733059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733156 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 3, 3, 2]
def baseStart_733156 : Nat := 118140960795 + 733156 * 2 ^ 59
def prefixEnd_733156 : Nat := 4983230072969 + 3 ^ 40 * 733156 * 2
def baseEnd_733156 : Nat := 376461422727838757478283

theorem tailTrace_733156 : CollatzResearch.WordTrace tailWord_733156 prefixEnd_733156 376461422727838757478283 := by
  unfold tailWord_733156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13370198065954249960593661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17826930754605666614124881 13370198065954249960593661)
  ·
    refine ⟨5013824274732843735222623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13370198065954249960593661 5013824274732843735222623)
    ·
      refine ⟨7520736412099265602833935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5013824274732843735222623 7520736412099265602833935)
      ·
        refine ⟨11281104618148898404250903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7520736412099265602833935 11281104618148898404250903)
        ·
          refine ⟨16921656927223347606376355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11281104618148898404250903 16921656927223347606376355)
          ·
            refine ⟨25382485390835021409564533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16921656927223347606376355 25382485390835021409564533)
            ·
              refine ⟨2379608005390783257146675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25382485390835021409564533 2379608005390783257146675)
              ·
                refine ⟨3569412008086174885720013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379608005390783257146675 3569412008086174885720013)
                ·
                  refine ⟨1338529503032315582145005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3569412008086174885720013 1338529503032315582145005)
                  ·
                    refine ⟨501948563637118343304377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1338529503032315582145005 501948563637118343304377)
                    ·
                      refine ⟨376461422727838757478283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 501948563637118343304377 376461422727838757478283)
                      ·
                        rfl

theorem cell23_733156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_733156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733156 prefixEnd_733156 := by exact prefixLift 733156
  have htrace : WordTrace (prefixWord ++ tailWord_733156) baseStart_733156 baseEnd_733156 := by
    simpa [prefixWord, tailWord_733156, baseEnd_733156] using wordTrace_append hprefix tailTrace_733156
  have hstable : (prefixWord ++ tailWord_733156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733156).length < 2 ^ (prefixWord ++ tailWord_733156).sum := by decide
  have hdescent : baseEnd_733156 < baseStart_733156 := by decide
  rcases family_descends (prefixWord ++ tailWord_733156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733189 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 2, 4, 3]
def baseStart_733189 : Nat := 118140960795 + 733189 * 2 ^ 59
def prefixEnd_733189 : Nat := 4983230072969 + 3 ^ 40 * 733189 * 2
def baseEnd_733189 : Nat := 376478367589437128365631

theorem tailTrace_733189 : CollatzResearch.WordTrace tailWord_733189 prefixEnd_733189 376478367589437128365631 := by
  unfold tailWord_733189
  simp only [CollatzResearch.WordTrace]
  refine ⟨26741599740788946557138621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17827733160525964371425747 26741599740788946557138621)
  ·
    refine ⟨10028099902795854958926983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26741599740788946557138621 10028099902795854958926983)
    ·
      refine ⟨15042149854193782438390475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10028099902795854958926983 15042149854193782438390475)
      ·
        refine ⟨22563224781290673657585713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15042149854193782438390475 22563224781290673657585713)
        ·
          refine ⟨16922418585968005243189285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22563224781290673657585713 16922418585968005243189285)
          ·
            refine ⟨3172953484869000983097991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16922418585968005243189285 3172953484869000983097991)
            ·
              refine ⟨4759430227303501474646987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3172953484869000983097991 4759430227303501474646987)
              ·
                refine ⟨7139145340955252211970481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759430227303501474646987 7139145340955252211970481)
                ·
                  refine ⟨5354359005716439158977861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7139145340955252211970481 5354359005716439158977861)
                  ·
                    refine ⟨1003942313571832342308349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354359005716439158977861 1003942313571832342308349)
                    ·
                      refine ⟨376478367589437128365631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1003942313571832342308349 376478367589437128365631)
                      ·
                        rfl

theorem cell23_733189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_733189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733189 prefixEnd_733189 := by exact prefixLift 733189
  have htrace : WordTrace (prefixWord ++ tailWord_733189) baseStart_733189 baseEnd_733189 := by
    simpa [prefixWord, tailWord_733189, baseEnd_733189] using wordTrace_append hprefix tailTrace_733189
  have hstable : (prefixWord ++ tailWord_733189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733189).length < 2 ^ (prefixWord ++ tailWord_733189).sum := by decide
  have hdescent : baseEnd_733189 < baseStart_733189 := by decide
  rcases family_descends (prefixWord ++ tailWord_733189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733197 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_733197 : Nat := 118140960795 + 733197 * 2 ^ 59
def prefixEnd_733197 : Nat := 4983230072969 + 3 ^ 40 * 733197 * 2
def baseEnd_733197 : Nat := 376482475434673097065595

theorem tailTrace_733197 : CollatzResearch.WordTrace tailWord_733197 prefixEnd_733197 376482475434673097065595 := by
  unfold tailWord_733197
  simp only [CollatzResearch.WordTrace]
  refine ⟨26741891524759963923429845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17827927683173309282286563 26741891524759963923429845)
  ·
    refine ⟨626763082611561654455387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 26741891524759963923429845 626763082611561654455387)
    ·
      refine ⟨940144623917342481683081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626763082611561654455387 940144623917342481683081)
      ·
        refine ⟨705108467938006861262311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 940144623917342481683081 705108467938006861262311)
        ·
          refine ⟨1057662701907010291893467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705108467938006861262311 1057662701907010291893467)
          ·
            refine ⟨1586494052860515437840201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057662701907010291893467 1586494052860515437840201)
            ·
              refine ⟨1189870539645386578380151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586494052860515437840201 1189870539645386578380151)
              ·
                refine ⟨1784805809468079867570227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189870539645386578380151 1784805809468079867570227)
                ·
                  refine ⟨2677208714202119801355341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784805809468079867570227 2677208714202119801355341)
                  ·
                    refine ⟨1003953267825794925508253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677208714202119801355341 1003953267825794925508253)
                    ·
                      refine ⟨376482475434673097065595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1003953267825794925508253 376482475434673097065595)
                      ·
                        rfl

theorem cell23_733197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_733197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733197 prefixEnd_733197 := by exact prefixLift 733197
  have htrace : WordTrace (prefixWord ++ tailWord_733197) baseStart_733197 baseEnd_733197 := by
    simpa [prefixWord, tailWord_733197, baseEnd_733197] using wordTrace_append hprefix tailTrace_733197
  have hstable : (prefixWord ++ tailWord_733197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733197).length < 2 ^ (prefixWord ++ tailWord_733197).sum := by decide
  have hdescent : baseEnd_733197 < baseStart_733197 := by decide
  rcases family_descends (prefixWord ++ tailWord_733197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733203 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 2, 2, 2]
def baseStart_733203 : Nat := 118140960795 + 733203 * 2 ^ 59
def prefixEnd_733203 : Nat := 4983230072969 + 3 ^ 40 * 733203 * 2
def baseEnd_733203 : Nat := 376485556318600073590567

theorem tailTrace_733203 : CollatzResearch.WordTrace tailWord_733203 prefixEnd_733203 376485556318600073590567 := by
  unfold tailWord_733203
  simp only [CollatzResearch.WordTrace]
  refine ⟨26742110362738226948148263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17828073575158817965432175 26742110362738226948148263)
  ·
    refine ⟨40113165544107340422222395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26742110362738226948148263 40113165544107340422222395)
    ·
      refine ⟨60169748316161010633333593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40113165544107340422222395 60169748316161010633333593)
      ·
        refine ⟨45127311237120757975000195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60169748316161010633333593 45127311237120757975000195)
        ·
          refine ⟨67690966855681136962500293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45127311237120757975000195 67690966855681136962500293)
          ·
            refine ⟨12692056285440213180468805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67690966855681136962500293 12692056285440213180468805)
            ·
              refine ⟨2379760553520039971337901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12692056285440213180468805 2379760553520039971337901)
              ·
                refine ⟨892410207570014989251713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2379760553520039971337901 892410207570014989251713)
                ·
                  refine ⟨669307655677511241938785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 892410207570014989251713 669307655677511241938785)
                  ·
                    refine ⟨501980741758133431454089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 669307655677511241938785 501980741758133431454089)
                    ·
                      refine ⟨376485556318600073590567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 501980741758133431454089 376485556318600073590567)
                      ·
                        rfl

theorem cell23_733203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 2, 2].length) (baseStart_733203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733203 prefixEnd_733203 := by exact prefixLift 733203
  have htrace : WordTrace (prefixWord ++ tailWord_733203) baseStart_733203 baseEnd_733203 := by
    simpa [prefixWord, tailWord_733203, baseEnd_733203] using wordTrace_append hprefix tailTrace_733203
  have hstable : (prefixWord ++ tailWord_733203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733203).length < 2 ^ (prefixWord ++ tailWord_733203).sum := by decide
  have hdescent : baseEnd_733203 < baseStart_733203 := by decide
  rcases family_descends (prefixWord ++ tailWord_733203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733219 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 3]
def baseStart_733219 : Nat := 118140960795 + 733219 * 2 ^ 59
def prefixEnd_733219 : Nat := 4983230072969 + 3 ^ 40 * 733219 * 2
def baseEnd_733219 : Nat := 376493772009072010990493

theorem tailTrace_733219 : CollatzResearch.WordTrace tailWord_733219 prefixEnd_733219 376493772009072010990493 := by
  unfold tailWord_733219
  simp only [CollatzResearch.WordTrace]
  refine ⟨26742693930680261680730711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17828462620453507787153807 26742693930680261680730711)
  ·
    refine ⟨40114040896020392521096067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26742693930680261680730711 40114040896020392521096067)
    ·
      refine ⟨60171061344030588781644101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40114040896020392521096067 60171061344030588781644101)
      ·
        refine ⟨11282074002005735396558269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60171061344030588781644101 11282074002005735396558269)
        ·
          refine ⟨4230777750752150773709351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11282074002005735396558269 4230777750752150773709351)
          ·
            refine ⟨6346166626128226160564027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230777750752150773709351 6346166626128226160564027)
            ·
              refine ⟨9519249939192339240846041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6346166626128226160564027 9519249939192339240846041)
              ·
                refine ⟨7139437454394254430634531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9519249939192339240846041 7139437454394254430634531)
                ·
                  refine ⟨10709156181591381645951797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7139437454394254430634531 10709156181591381645951797)
                  ·
                    refine ⟨1003983392024192029307981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10709156181591381645951797 1003983392024192029307981)
                    ·
                      refine ⟨376493772009072010990493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1003983392024192029307981 376493772009072010990493)
                      ·
                        rfl

theorem cell23_733219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_733219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733219 prefixEnd_733219 := by exact prefixLift 733219
  have htrace : WordTrace (prefixWord ++ tailWord_733219) baseStart_733219 baseEnd_733219 := by
    simpa [prefixWord, tailWord_733219, baseEnd_733219] using wordTrace_append hprefix tailTrace_733219
  have hstable : (prefixWord ++ tailWord_733219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733219).length < 2 ^ (prefixWord ++ tailWord_733219).sum := by decide
  have hdescent : baseEnd_733219 < baseStart_733219 := by decide
  rcases family_descends (prefixWord ++ tailWord_733219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733224 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_733224 : Nat := 118140960795 + 733224 * 2 ^ 59
def prefixEnd_733224 : Nat := 4983230072969 + 3 ^ 40 * 733224 * 2
def baseEnd_733224 : Nat := 376496339412344491427971

theorem tailTrace_733224 : CollatzResearch.WordTrace tailWord_733224 prefixEnd_733224 376496339412344491427971 := by
  unfold tailWord_733224
  simp only [CollatzResearch.WordTrace]
  refine ⟨13371438147831073767331363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17828584197108098356441817 13371438147831073767331363)
  ·
    refine ⟨20057157221746610650997045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13371438147831073767331363 20057157221746610650997045)
    ·
      refine ⟨1880358489538744748530973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20057157221746610650997045 1880358489538744748530973)
      ·
        refine ⟨705134433577029280699115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1880358489538744748530973 705134433577029280699115)
        ·
          refine ⟨1057701650365543921048673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705134433577029280699115 1057701650365543921048673)
          ·
            refine ⟨793276237774157940786505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057701650365543921048673 793276237774157940786505)
            ·
              refine ⟨594957178330618455589879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793276237774157940786505 594957178330618455589879)
              ·
                refine ⟨892435767495927683384819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594957178330618455589879 892435767495927683384819)
                ·
                  refine ⟨1338653651243891525077229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892435767495927683384819 1338653651243891525077229)
                  ·
                    refine ⟨501995119216459321903961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1338653651243891525077229 501995119216459321903961)
                    ·
                      refine ⟨376496339412344491427971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 501995119216459321903961 376496339412344491427971)
                      ·
                        rfl

theorem cell23_733224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_733224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733224 prefixEnd_733224 := by exact prefixLift 733224
  have htrace : WordTrace (prefixWord ++ tailWord_733224) baseStart_733224 baseEnd_733224 := by
    simpa [prefixWord, tailWord_733224, baseEnd_733224] using wordTrace_append hprefix tailTrace_733224
  have hstable : (prefixWord ++ tailWord_733224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733224).length < 2 ^ (prefixWord ++ tailWord_733224).sum := by decide
  have hdescent : baseEnd_733224 < baseStart_733224 := by decide
  rcases family_descends (prefixWord ++ tailWord_733224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733239 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 2, 5]
def baseStart_733239 : Nat := 118140960795 + 733239 * 2 ^ 59
def prefixEnd_733239 : Nat := 4983230072969 + 3 ^ 40 * 733239 * 2
def baseEnd_733239 : Nat := 125501347207387310913467

theorem tailTrace_733239 : CollatzResearch.WordTrace tailWord_733239 prefixEnd_733239 125501347207387310913467 := by
  unfold tailWord_733239
  simp only [CollatzResearch.WordTrace]
  refine ⟨26743423390607805096458771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17828948927071870064305847 26743423390607805096458771)
  ·
    refine ⟨40115135085911707644688157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26743423390607805096458771 40115135085911707644688157)
    ·
      refine ⟨15043175657216890366758059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40115135085911707644688157 15043175657216890366758059)
      ·
        refine ⟨22564763485825335550137089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15043175657216890366758059 22564763485825335550137089)
        ·
          refine ⟨16923572614369001662602817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22564763485825335550137089 16923572614369001662602817)
          ·
            refine ⟨12692679460776751246952113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16923572614369001662602817 12692679460776751246952113)
            ·
              refine ⟨9519509595582563435214085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12692679460776751246952113 9519509595582563435214085)
              ·
                refine ⟨1784908049171730644102641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9519509595582563435214085 1784908049171730644102641)
                ·
                  refine ⟨1338681036878797983076981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1784908049171730644102641 1338681036878797983076981)
                  ·
                    refine ⟨125501347207387310913467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1338681036878797983076981 125501347207387310913467)
                    ·
                      rfl

theorem cell23_733239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_733239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733239 prefixEnd_733239 := by exact prefixLift 733239
  have htrace : WordTrace (prefixWord ++ tailWord_733239) baseStart_733239 baseEnd_733239 := by
    simpa [prefixWord, tailWord_733239, baseEnd_733239] using wordTrace_append hprefix tailTrace_733239
  have hstable : (prefixWord ++ tailWord_733239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733239).length < 2 ^ (prefixWord ++ tailWord_733239).sum := by decide
  have hdescent : baseEnd_733239 < baseStart_733239 := by decide
  rcases family_descends (prefixWord ++ tailWord_733239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733254 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_733254 : Nat := 118140960795 + 733254 * 2 ^ 59
def prefixEnd_733254 : Nat := 4983230072969 + 3 ^ 40 * 733254 * 2
def baseEnd_733254 : Nat := 376511743831979374052833

theorem tailTrace_733254 : CollatzResearch.WordTrace tailWord_733254 prefixEnd_733254 376511743831979374052833 := by
  unfold tailWord_733254
  simp only [CollatzResearch.WordTrace]
  refine ⟨835749077673545708070463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17829313657035641772169877 835749077673545708070463)
  ·
    refine ⟨1253623616510318562105695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 835749077673545708070463 1253623616510318562105695)
    ·
      refine ⟨1880435424765477843158543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253623616510318562105695 1880435424765477843158543)
      ·
        refine ⟨2820653137148216764737815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880435424765477843158543 2820653137148216764737815)
        ·
          refine ⟨4230979705722325147106723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820653137148216764737815 4230979705722325147106723)
          ·
            refine ⟨6346469558583487720660085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230979705722325147106723 6346469558583487720660085)
            ·
              refine ⟨594981521117201973811883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6346469558583487720660085 594981521117201973811883)
              ·
                refine ⟨892472281675802960717825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594981521117201973811883 892472281675802960717825)
                ·
                  refine ⟨669354211256852220538369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 892472281675802960717825 669354211256852220538369)
                  ·
                    refine ⟨502015658442639165403777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 669354211256852220538369 502015658442639165403777)
                    ·
                      refine ⟨376511743831979374052833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502015658442639165403777 376511743831979374052833)
                      ·
                        rfl

theorem cell23_733254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_733254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733254 prefixEnd_733254 := by exact prefixLift 733254
  have htrace : WordTrace (prefixWord ++ tailWord_733254) baseStart_733254 baseEnd_733254 := by
    simpa [prefixWord, tailWord_733254, baseEnd_733254] using wordTrace_append hprefix tailTrace_733254
  have hstable : (prefixWord ++ tailWord_733254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733254).length < 2 ^ (prefixWord ++ tailWord_733254).sum := by decide
  have hdescent : baseEnd_733254 < baseStart_733254 := by decide
  rcases family_descends (prefixWord ++ tailWord_733254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733259 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 4]
def baseStart_733259 : Nat := 118140960795 + 733259 * 2 ^ 59
def prefixEnd_733259 : Nat := 4983230072969 + 3 ^ 40 * 733259 * 2
def baseEnd_733259 : Nat := 376514311235251854490309

theorem tailTrace_733259 : CollatzResearch.WordTrace tailWord_733259 prefixEnd_733259 376514311235251854490309 := by
  unfold tailWord_733259
  simp only [CollatzResearch.WordTrace]
  refine ⟨26744152850535348512186831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17829435233690232341457887 26744152850535348512186831)
  ·
    refine ⟨40116229275803022768280247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26744152850535348512186831 40116229275803022768280247)
    ·
      refine ⟨60174343913704534152420371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40116229275803022768280247 60174343913704534152420371)
      ·
        refine ⟨90261515870556801228630557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60174343913704534152420371 90261515870556801228630557)
        ·
          refine ⟨33848068451458800460736459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90261515870556801228630557 33848068451458800460736459)
          ·
            refine ⟨50772102677188200691104689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33848068451458800460736459 50772102677188200691104689)
            ·
              refine ⟨38079077007891150518328517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50772102677188200691104689 38079077007891150518328517)
              ·
                refine ⟨7139826938979590722186597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38079077007891150518328517 7139826938979590722186597)
                ·
                  refine ⟨1338717551058673260409987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7139826938979590722186597 1338717551058673260409987)
                  ·
                    refine ⟨2008076326588009890614981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1338717551058673260409987 2008076326588009890614981)
                    ·
                      refine ⟨376514311235251854490309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2008076326588009890614981 376514311235251854490309)
                      ·
                        rfl

theorem cell23_733259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 4].length) (baseStart_733259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733259 prefixEnd_733259 := by exact prefixLift 733259
  have htrace : WordTrace (prefixWord ++ tailWord_733259) baseStart_733259 baseEnd_733259 := by
    simpa [prefixWord, tailWord_733259, baseEnd_733259] using wordTrace_append hprefix tailTrace_733259
  have hstable : (prefixWord ++ tailWord_733259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733259).length < 2 ^ (prefixWord ++ tailWord_733259).sum := by decide
  have hdescent : baseEnd_733259 < baseStart_733259 := by decide
  rcases family_descends (prefixWord ++ tailWord_733259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733276 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_733276 : Nat := 118140960795 + 733276 * 2 ^ 59
def prefixEnd_733276 : Nat := 4983230072969 + 3 ^ 40 * 733276 * 2
def baseEnd_733276 : Nat := 376523040406378287977731

theorem tailTrace_733276 : CollatzResearch.WordTrace tailWord_733276 prefixEnd_733276 376523040406378287977731 := by
  unfold tailWord_733276
  simp only [CollatzResearch.WordTrace]
  refine ⟨13372386445736880207777841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17829848594315840277037121 13372386445736880207777841)
  ·
    refine ⟨10029289834302660155833381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13372386445736880207777841 10029289834302660155833381)
    ·
      refine ⟨1880491843931748779218759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10029289834302660155833381 1880491843931748779218759)
      ·
        refine ⟨2820737765897623168828139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880491843931748779218759 2820737765897623168828139)
        ·
          refine ⟨4231106648846434753242209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820737765897623168828139 4231106648846434753242209)
          ·
            refine ⟨3173329986634826064931657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4231106648846434753242209 3173329986634826064931657)
            ·
              refine ⟨2379997489976119548698743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3173329986634826064931657 2379997489976119548698743)
              ·
                refine ⟨3569996234964179323048115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379997489976119548698743 3569996234964179323048115)
                ·
                  refine ⟨5354994352446268984572173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569996234964179323048115 5354994352446268984572173)
                  ·
                    refine ⟨2008122882167350869214565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5354994352446268984572173 2008122882167350869214565)
                    ·
                      refine ⟨376523040406378287977731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2008122882167350869214565 376523040406378287977731)
                      ·
                        rfl

theorem cell23_733276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_733276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733276 prefixEnd_733276 := by exact prefixLift 733276
  have htrace : WordTrace (prefixWord ++ tailWord_733276) baseStart_733276 baseEnd_733276 := by
    simpa [prefixWord, tailWord_733276, baseEnd_733276] using wordTrace_append hprefix tailTrace_733276
  have hstable : (prefixWord ++ tailWord_733276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733276).length < 2 ^ (prefixWord ++ tailWord_733276).sum := by decide
  have hdescent : baseEnd_733276 < baseStart_733276 := by decide
  rcases family_descends (prefixWord ++ tailWord_733276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733296 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 3]
def baseStart_733296 : Nat := 118140960795 + 733296 * 2 ^ 59
def prefixEnd_733296 : Nat := 4983230072969 + 3 ^ 40 * 733296 * 2
def baseEnd_733296 : Nat := 376533310019468209727639

theorem tailTrace_733296 : CollatzResearch.WordTrace tailWord_733296 prefixEnd_733296 376533310019468209727639 := by
  unfold tailWord_733296
  simp only [CollatzResearch.WordTrace]
  refine ⟨13372751175700651915641871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17830334900934202554189161 13372751175700651915641871)
  ·
    refine ⟨20059126763550977873462807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13372751175700651915641871 20059126763550977873462807)
    ·
      refine ⟨30088690145326466810194211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20059126763550977873462807 30088690145326466810194211)
      ·
        refine ⟨45133035217989700215291317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30088690145326466810194211 45133035217989700215291317)
        ·
          refine ⟨4231222051686534395183561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45133035217989700215291317 4231222051686534395183561)
          ·
            refine ⟨3173416538764900796387671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4231222051686534395183561 3173416538764900796387671)
            ·
              refine ⟨4760124808147351194581507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173416538764900796387671 4760124808147351194581507)
              ·
                refine ⟨7140187212221026791872261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4760124808147351194581507 7140187212221026791872261)
                ·
                  refine ⟨1338785102291442523476049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7140187212221026791872261 1338785102291442523476049)
                  ·
                    refine ⟨1004088826718581892607037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1338785102291442523476049 1004088826718581892607037)
                    ·
                      refine ⟨376533310019468209727639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1004088826718581892607037 376533310019468209727639)
                      ·
                        rfl

theorem cell23_733296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 3].length) (baseStart_733296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733296 prefixEnd_733296 := by exact prefixLift 733296
  have htrace : WordTrace (prefixWord ++ tailWord_733296) baseStart_733296 baseEnd_733296 := by
    simpa [prefixWord, tailWord_733296, baseEnd_733296] using wordTrace_append hprefix tailTrace_733296
  have hstable : (prefixWord ++ tailWord_733296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733296).length < 2 ^ (prefixWord ++ tailWord_733296).sum := by decide
  have hdescent : baseEnd_733296 < baseStart_733296 := by decide
  rcases family_descends (prefixWord ++ tailWord_733296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733303 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 3, 4]
def baseStart_733303 : Nat := 118140960795 + 733303 * 2 ^ 59
def prefixEnd_733303 : Nat := 4983230072969 + 3 ^ 40 * 733303 * 2
def baseEnd_733303 : Nat := 125512301461349894113369

theorem tailTrace_733303 : CollatzResearch.WordTrace tailWord_733303 prefixEnd_733303 125512301461349894113369 := by
  unfold tailWord_733303
  simp only [CollatzResearch.WordTrace]
  refine ⟨26745757662375944026788563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17830505108250629351192375 26745757662375944026788563)
  ·
    refine ⟨40118636493563916040182845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26745757662375944026788563 40118636493563916040182845)
    ·
      refine ⟨15044488685086468515068567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40118636493563916040182845 15044488685086468515068567)
      ·
        refine ⟨22566733027629702772602851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15044488685086468515068567 22566733027629702772602851)
        ·
          refine ⟨33850099541444554158904277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22566733027629702772602851 33850099541444554158904277)
          ·
            refine ⟨793361708002606738099319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 33850099541444554158904277 793361708002606738099319)
            ·
              refine ⟨1190042562003910107148979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793361708002606738099319 1190042562003910107148979)
              ·
                refine ⟨1785063843005865160723469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190042562003910107148979 1785063843005865160723469)
                ·
                  refine ⟨669398941127199435271301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1785063843005865160723469 669398941127199435271301)
                  ·
                    refine ⟨125512301461349894113369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 669398941127199435271301 125512301461349894113369)
                    ·
                      rfl

theorem cell23_733303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_733303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733303 prefixEnd_733303 := by exact prefixLift 733303
  have htrace : WordTrace (prefixWord ++ tailWord_733303) baseStart_733303 baseEnd_733303 := by
    simpa [prefixWord, tailWord_733303, baseEnd_733303] using wordTrace_append hprefix tailTrace_733303
  have hstable : (prefixWord ++ tailWord_733303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733303).length < 2 ^ (prefixWord ++ tailWord_733303).sum := by decide
  have hdescent : baseEnd_733303 < baseStart_733303 := by decide
  rcases family_descends (prefixWord ++ tailWord_733303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733316 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 6]
def baseStart_733316 : Nat := 118140960795 + 733316 * 2 ^ 59
def prefixEnd_733316 : Nat := 4983230072969 + 3 ^ 40 * 733316 * 2
def baseEnd_733316 : Nat := 41838175514728681275283

theorem tailTrace_733316 : CollatzResearch.WordTrace tailWord_733316 prefixEnd_733316 41838175514728681275283 := by
  unfold tailWord_733316
  simp only [CollatzResearch.WordTrace]
  refine ⟨13373115905664423623505901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17830821207552564831341201 13373115905664423623505901)
  ·
    refine ⟨5014918464624158858814713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13373115905664423623505901 5014918464624158858814713)
    ·
      refine ⟨3761188848468119144111035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5014918464624158858814713 3761188848468119144111035)
      ·
        refine ⟨5641783272702178716166553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761188848468119144111035 5641783272702178716166553)
        ·
          refine ⟨4231337454526634037124915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5641783272702178716166553 4231337454526634037124915)
          ·
            refine ⟨6347006181789951055687373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231337454526634037124915 6347006181789951055687373)
            ·
              refine ⟨2380127318171231645882765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6347006181789951055687373 2380127318171231645882765)
              ·
                refine ⟨892547744314211867206037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2380127318171231645882765 892547744314211867206037)
                ·
                  refine ⟨41838175514728681275283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 892547744314211867206037 41838175514728681275283)
                  ·
                    rfl

theorem cell23_733316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_733316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733316 prefixEnd_733316 := by exact prefixLift 733316
  have htrace : WordTrace (prefixWord ++ tailWord_733316) baseStart_733316 baseEnd_733316 := by
    simpa [prefixWord, tailWord_733316, baseEnd_733316] using wordTrace_append hprefix tailTrace_733316
  have hstable : (prefixWord ++ tailWord_733316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733316).length < 2 ^ (prefixWord ++ tailWord_733316).sum := by decide
  have hdescent : baseEnd_733316 < baseStart_733316 := by decide
  rcases family_descends (prefixWord ++ tailWord_733316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733319 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_733319 : Nat := 118140960795 + 733319 * 2 ^ 59
def prefixEnd_733319 : Nat := 4983230072969 + 3 ^ 40 * 733319 * 2
def baseEnd_733319 : Nat := 376545120074521619740033

theorem tailTrace_733319 : CollatzResearch.WordTrace tailWord_733319 prefixEnd_733319 376545120074521619740033 := by
  unfold tailWord_733319
  simp only [CollatzResearch.WordTrace]
  refine ⟨26746341230317978759371011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17830894153545319172914007 26746341230317978759371011)
  ·
    refine ⟨40119511845476968139056517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26746341230317978759371011 40119511845476968139056517)
    ·
      refine ⟨7522408471026931526073097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40119511845476968139056517 7522408471026931526073097)
      ·
        refine ⟨5641806353270198644554823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7522408471026931526073097 5641806353270198644554823)
        ·
          refine ⟨8462709529905297966832235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5641806353270198644554823 8462709529905297966832235)
          ·
            refine ⟨12694064294857946950248353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8462709529905297966832235 12694064294857946950248353)
            ·
              refine ⟨9520548221143460212686265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12694064294857946950248353 9520548221143460212686265)
              ·
                refine ⟨7140411165857595159514699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9520548221143460212686265 7140411165857595159514699)
                ·
                  refine ⟨10710616748786392739272049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7140411165857595159514699 10710616748786392739272049)
                  ·
                    refine ⟨8032962561589794554454037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10710616748786392739272049 8032962561589794554454037)
                    ·
                      refine ⟨376545120074521619740033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8032962561589794554454037 376545120074521619740033)
                      ·
                        rfl

theorem cell23_733319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_733319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733319 prefixEnd_733319 := by exact prefixLift 733319
  have htrace : WordTrace (prefixWord ++ tailWord_733319) baseStart_733319 baseEnd_733319 := by
    simpa [prefixWord, tailWord_733319, baseEnd_733319] using wordTrace_append hprefix tailTrace_733319
  have hstable : (prefixWord ++ tailWord_733319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733319).length < 2 ^ (prefixWord ++ tailWord_733319).sum := by decide
  have hdescent : baseEnd_733319 < baseStart_733319 := by decide
  rcases family_descends (prefixWord ++ tailWord_733319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733359 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 5, 6]
def baseStart_733359 : Nat := 118140960795 + 733359 * 2 ^ 59
def prefixEnd_733359 : Nat := 4983230072969 + 3 ^ 40 * 733359 * 2
def baseEnd_733359 : Nat := 125521886433567154413283

theorem tailTrace_733359 : CollatzResearch.WordTrace tailWord_733359 prefixEnd_733359 125521886433567154413283 := by
  unfold tailWord_733359
  simp only [CollatzResearch.WordTrace]
  refine ⟨26747800150173065590827131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17831866766782043727218087 26747800150173065590827131)
  ·
    refine ⟨40121700225259598386240697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26747800150173065590827131 40121700225259598386240697)
    ·
      refine ⟨30091275168944698789680523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40121700225259598386240697 30091275168944698789680523)
      ·
        refine ⟨45136912753417048184520785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30091275168944698789680523 45136912753417048184520785)
        ·
          refine ⟨33852684565062786138390589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45136912753417048184520785 33852684565062786138390589)
          ·
            refine ⟨12694756711898544801896471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33852684565062786138390589 12694756711898544801896471)
            ·
              refine ⟨19042135067847817202844707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12694756711898544801896471 19042135067847817202844707)
              ·
                refine ⟨28563202601771725804267061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19042135067847817202844707 28563202601771725804267061)
                ·
                  refine ⟨2677800243916099294150037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28563202601771725804267061 2677800243916099294150037)
                  ·
                    refine ⟨125521886433567154413283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2677800243916099294150037 125521886433567154413283)
                    ·
                      rfl

theorem cell23_733359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_733359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733359 prefixEnd_733359 := by exact prefixLift 733359
  have htrace : WordTrace (prefixWord ++ tailWord_733359) baseStart_733359 baseEnd_733359 := by
    simpa [prefixWord, tailWord_733359, baseEnd_733359] using wordTrace_append hprefix tailTrace_733359
  have hstable : (prefixWord ++ tailWord_733359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733359).length < 2 ^ (prefixWord ++ tailWord_733359).sum := by decide
  have hdescent : baseEnd_733359 < baseStart_733359 := by decide
  rcases family_descends (prefixWord ++ tailWord_733359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733376 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 1, 6]
def baseStart_733376 : Nat := 118140960795 + 733376 * 2 ^ 59
def prefixEnd_733376 : Nat := 4983230072969 + 3 ^ 40 * 733376 * 2
def baseEnd_733376 : Nat := 125524796157275965575757

theorem tailTrace_733376 : CollatzResearch.WordTrace tailWord_733376 prefixEnd_733376 125524796157275965575757 := by
  unfold tailWord_733376
  simp only [CollatzResearch.WordTrace]
  refine ⟨13374210095555738747097991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17832280127407651662797321 13374210095555738747097991)
  ·
    refine ⟨20061315143333608120646987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13374210095555738747097991 20061315143333608120646987)
    ·
      refine ⟨30091972715000412180970481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20061315143333608120646987 30091972715000412180970481)
      ·
        refine ⟨22568979536250309135727861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30091972715000412180970481 22568979536250309135727861)
        ·
          refine ⟨2115841831523466481474487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22568979536250309135727861 2115841831523466481474487)
          ·
            refine ⟨3173762747285199722211731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115841831523466481474487 3173762747285199722211731)
            ·
              refine ⟨4760644120927799583317597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173762747285199722211731 4760644120927799583317597)
              ·
                refine ⟨1785241545347924843744099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4760644120927799583317597 1785241545347924843744099)
                ·
                  refine ⟨2677862318021887265616149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785241545347924843744099 2677862318021887265616149)
                  ·
                    refine ⟨125524796157275965575757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2677862318021887265616149 125524796157275965575757)
                    ·
                      rfl

theorem cell23_733376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_733376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733376 prefixEnd_733376 := by exact prefixLift 733376
  have htrace : WordTrace (prefixWord ++ tailWord_733376) baseStart_733376 baseEnd_733376 := by
    simpa [prefixWord, tailWord_733376, baseEnd_733376] using wordTrace_append hprefix tailTrace_733376
  have hstable : (prefixWord ++ tailWord_733376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733376).length < 2 ^ (prefixWord ++ tailWord_733376).sum := by decide
  have hdescent : baseEnd_733376 < baseStart_733376 := by decide
  rcases family_descends (prefixWord ++ tailWord_733376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733377 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_733377 : Nat := 118140960795 + 733377 * 2 ^ 59
def prefixEnd_733377 : Nat := 4983230072969 + 3 ^ 40 * 733377 * 2
def baseEnd_733377 : Nat := 376574901952482392814767

theorem tailTrace_733377 : CollatzResearch.WordTrace tailWord_733377 prefixEnd_733377 376574901952482392814767 := by
  unfold tailWord_733377
  simp only [CollatzResearch.WordTrace]
  refine ⟨26748456664107854664982385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17832304442738569776654923 26748456664107854664982385)
  ·
    refine ⟨20061342498080890998736789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26748456664107854664982385 20061342498080890998736789)
    ·
      refine ⟨940375429597541765565787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20061342498080890998736789 940375429597541765565787)
      ·
        refine ⟨1410563144396312648348681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940375429597541765565787 1410563144396312648348681)
        ·
          refine ⟨1057922358297234486261511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1410563144396312648348681 1057922358297234486261511)
          ·
            refine ⟨1586883537445851729392267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057922358297234486261511 1586883537445851729392267)
            ·
              refine ⟨2380325306168777594088401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586883537445851729392267 2380325306168777594088401)
              ·
                refine ⟨1785243979626583195566301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2380325306168777594088401 1785243979626583195566301)
                ·
                  refine ⟨669466492359968698337363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1785243979626583195566301 669466492359968698337363)
                  ·
                    refine ⟨1004199738539953047506045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 669466492359968698337363 1004199738539953047506045)
                    ·
                      refine ⟨376574901952482392814767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1004199738539953047506045 376574901952482392814767)
                      ·
                        rfl

theorem cell23_733377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_733377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733377 prefixEnd_733377 := by exact prefixLift 733377
  have htrace : WordTrace (prefixWord ++ tailWord_733377) baseStart_733377 baseEnd_733377 := by
    simpa [prefixWord, tailWord_733377, baseEnd_733377] using wordTrace_append hprefix tailTrace_733377
  have hstable : (prefixWord ++ tailWord_733377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733377).length < 2 ^ (prefixWord ++ tailWord_733377).sum := by decide
  have hdescent : baseEnd_733377 < baseStart_733377 := by decide
  rcases family_descends (prefixWord ++ tailWord_733377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733379 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 6]
def baseStart_733379 : Nat := 118140960795 + 733379 * 2 ^ 59
def prefixEnd_733379 : Nat := 4983230072969 + 3 ^ 40 * 733379 * 2
def baseEnd_733379 : Nat := 376575928913791384989757

theorem tailTrace_733379 : CollatzResearch.WordTrace tailWord_733379 prefixEnd_733379 376575928913791384989757 := by
  unfold tailWord_733379
  simp only [CollatzResearch.WordTrace]
  refine ⟨26748529610100609006555191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17832353073400406004370127 26748529610100609006555191)
  ·
    refine ⟨40122794415150913509832787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26748529610100609006555191 40122794415150913509832787)
    ·
      refine ⟨60184191622726370264749181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40122794415150913509832787 60184191622726370264749181)
      ·
        refine ⟨22569071858522388849280943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60184191622726370264749181 22569071858522388849280943)
        ·
          refine ⟨33853607787783583273921415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22569071858522388849280943 33853607787783583273921415)
          ·
            refine ⟨50780411681675374910882123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33853607787783583273921415 50780411681675374910882123)
            ·
              refine ⟨76170617522513062366323185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50780411681675374910882123 76170617522513062366323185)
              ·
                refine ⟨57127963141884796774742389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76170617522513062366323185 57127963141884796774742389)
                ·
                  refine ⟨5355746544551699697632099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57127963141884796774742389 5355746544551699697632099)
                  ·
                    refine ⟨8033619816827549546448149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5355746544551699697632099 8033619816827549546448149)
                    ·
                      refine ⟨376575928913791384989757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8033619816827549546448149 376575928913791384989757)
                      ·
                        rfl

theorem cell23_733379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_733379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733379 prefixEnd_733379 := by exact prefixLift 733379
  have htrace : WordTrace (prefixWord ++ tailWord_733379) baseStart_733379 baseEnd_733379 := by
    simpa [prefixWord, tailWord_733379, baseEnd_733379] using wordTrace_append hprefix tailTrace_733379
  have hstable : (prefixWord ++ tailWord_733379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733379).length < 2 ^ (prefixWord ++ tailWord_733379).sum := by decide
  have hdescent : baseEnd_733379 < baseStart_733379 := by decide
  rcases family_descends (prefixWord ++ tailWord_733379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733397 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 1, 5]
def baseStart_733397 : Nat := 118140960795 + 733397 * 2 ^ 59
def prefixEnd_733397 : Nat := 4983230072969 + 3 ^ 40 * 733397 * 2
def baseEnd_733397 : Nat := 125528390521857438188225

theorem tailTrace_733397 : CollatzResearch.WordTrace tailWord_733397 prefixEnd_733397 125528390521857438188225 := by
  unfold tailWord_733397
  simp only [CollatzResearch.WordTrace]
  refine ⟨26749186124035398080710445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17832790749356932053806963 26749186124035398080710445)
  ·
    refine ⟨10030944796513274280266417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26749186124035398080710445 10030944796513274280266417)
    ·
      refine ⟨7523208597384955710199813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10030944796513274280266417 7523208597384955710199813)
      ·
        refine ⟨1410601612009679195662465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7523208597384955710199813 1410601612009679195662465)
        ·
          refine ⟨1057951209007259396746849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1410601612009679195662465 1057951209007259396746849)
          ·
            refine ⟨793463406755444547560137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057951209007259396746849 793463406755444547560137)
            ·
              refine ⟨595097555066583410670103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793463406755444547560137 595097555066583410670103)
              ·
                refine ⟨892646332599875116005155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595097555066583410670103 892646332599875116005155)
                ·
                  refine ⟨1338969498899812674007733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892646332599875116005155 1338969498899812674007733)
                  ·
                    refine ⟨125528390521857438188225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1338969498899812674007733 125528390521857438188225)
                    ·
                      rfl

theorem cell23_733397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_733397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733397 prefixEnd_733397 := by exact prefixLift 733397
  have htrace : WordTrace (prefixWord ++ tailWord_733397) baseStart_733397 baseEnd_733397 := by
    simpa [prefixWord, tailWord_733397, baseEnd_733397] using wordTrace_append hprefix tailTrace_733397
  have hstable : (prefixWord ++ tailWord_733397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733397).length < 2 ^ (prefixWord ++ tailWord_733397).sum := by decide
  have hdescent : baseEnd_733397 < baseStart_733397 := by decide
  rcases family_descends (prefixWord ++ tailWord_733397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733400 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 1, 1, 4]
def baseStart_733400 : Nat := 118140960795 + 733400 * 2 ^ 59
def prefixEnd_733400 : Nat := 4983230072969 + 3 ^ 40 * 733400 * 2
def baseEnd_733400 : Nat := 376586712007535802827161

theorem tailTrace_733400 : CollatzResearch.WordTrace tailWord_733400 prefixEnd_733400 376586712007535802827161 := by
  unfold tailWord_733400
  simp only [CollatzResearch.WordTrace]
  refine ⟨13374647771512264796534827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17832863695349686395379769 13374647771512264796534827)
  ·
    refine ⟨20061971657268397194802241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13374647771512264796534827 20061971657268397194802241)
    ·
      refine ⟨15046478742951297896101681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20061971657268397194802241 15046478742951297896101681)
      ·
        refine ⟨11284859057213473422076261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15046478742951297896101681 11284859057213473422076261)
        ·
          refine ⟨2115911073227526266639299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11284859057213473422076261 2115911073227526266639299)
          ·
            refine ⟨3173866609841289399958949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115911073227526266639299 3173866609841289399958949)
            ·
              refine ⟨595099989345241762492303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3173866609841289399958949 595099989345241762492303)
              ·
                refine ⟨892649984017862643738455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595099989345241762492303 892649984017862643738455)
                ·
                  refine ⟨1338974976026793965607683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892649984017862643738455 1338974976026793965607683)
                  ·
                    refine ⟨2008462464040190948411525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1338974976026793965607683 2008462464040190948411525)
                    ·
                      refine ⟨376586712007535802827161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2008462464040190948411525 376586712007535802827161)
                      ·
                        rfl

theorem cell23_733400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_733400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733400 prefixEnd_733400 := by exact prefixLift 733400
  have htrace : WordTrace (prefixWord ++ tailWord_733400) baseStart_733400 baseEnd_733400 := by
    simpa [prefixWord, tailWord_733400, baseEnd_733400] using wordTrace_append hprefix tailTrace_733400
  have hstable : (prefixWord ++ tailWord_733400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733400).length < 2 ^ (prefixWord ++ tailWord_733400).sum := by decide
  have hdescent : baseEnd_733400 < baseStart_733400 := by decide
  rcases family_descends (prefixWord ++ tailWord_733400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733496 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 7]
def baseStart_733496 : Nat := 118140960795 + 733496 * 2 ^ 59
def prefixEnd_733496 : Nat := 4983230072969 + 3 ^ 40 * 733496 * 2
def baseEnd_733496 : Nat := 41848445127818603025191

theorem tailTrace_733496 : CollatzResearch.WordTrace tailWord_733496 prefixEnd_733496 41848445127818603025191 := by
  unfold tailWord_733496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13376398475338368994282171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17835197967117825325709561 13376398475338368994282171)
  ·
    refine ⟨20064597713007553491423257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13376398475338368994282171 20064597713007553491423257)
    ·
      refine ⟨15048448284755665118567443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20064597713007553491423257 15048448284755665118567443)
      ·
        refine ⟨22572672427133497677851165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15048448284755665118567443 22572672427133497677851165)
        ·
          refine ⟨8464752160175061629194187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22572672427133497677851165 8464752160175061629194187)
          ·
            refine ⟨12697128240262592443791281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8464752160175061629194187 12697128240262592443791281)
            ·
              refine ⟨9522846180196944332843461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12697128240262592443791281 9522846180196944332843461)
              ·
                refine ⟨1785533658786927062408149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9522846180196944332843461 1785533658786927062408149)
                ·
                  refine ⟨41848445127818603025191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1785533658786927062408149 41848445127818603025191)
                  ·
                    rfl

theorem cell23_733496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 7].length) (baseStart_733496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733496 prefixEnd_733496 := by exact prefixLift 733496
  have htrace : WordTrace (prefixWord ++ tailWord_733496) baseStart_733496 baseEnd_733496 := by
    simpa [prefixWord, tailWord_733496, baseEnd_733496] using wordTrace_append hprefix tailTrace_733496
  have hstable : (prefixWord ++ tailWord_733496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733496).length < 2 ^ (prefixWord ++ tailWord_733496).sum := by decide
  have hdescent : baseEnd_733496 < baseStart_733496 := by decide
  rcases family_descends (prefixWord ++ tailWord_733496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733513 : List Nat := [1, 2, 1, 1, 2, 3, 1, 7, 5]
def baseStart_733513 : Nat := 118140960795 + 733513 * 2 ^ 59
def prefixEnd_733513 : Nat := 4983230072969 + 3 ^ 40 * 733513 * 2
def baseEnd_733513 : Nat := 41849415035721540079349

theorem tailTrace_733513 : CollatzResearch.WordTrace tailWord_733513 prefixEnd_733513 41849415035721540079349 := by
  unfold tailWord_733513
  simp only [CollatzResearch.WordTrace]
  refine ⟨26753416991615149891933193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17835611327743433261288795 26753416991615149891933193)
  ·
    refine ⟨20065062743711362418949895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26753416991615149891933193 20065062743711362418949895)
    ·
      refine ⟨30097594115567043628424843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20065062743711362418949895 30097594115567043628424843)
      ·
        refine ⟨45146391173350565442637265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30097594115567043628424843 45146391173350565442637265)
        ·
          refine ⟨33859793380012924081977949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45146391173350565442637265 33859793380012924081977949)
          ·
            refine ⟨12697422517504846530741731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33859793380012924081977949 12697422517504846530741731)
            ·
              refine ⟨19046133776257269796112597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12697422517504846530741731 19046133776257269796112597)
              ·
                refine ⟨446393760381029760846389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19046133776257269796112597 446393760381029760846389)
                ·
                  refine ⟨41849415035721540079349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 446393760381029760846389 41849415035721540079349)
                  ·
                    rfl

theorem cell23_733513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 5].length) (baseStart_733513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733513 prefixEnd_733513 := by exact prefixLift 733513
  have htrace : WordTrace (prefixWord ++ tailWord_733513) baseStart_733513 baseEnd_733513 := by
    simpa [prefixWord, tailWord_733513, baseEnd_733513] using wordTrace_append hprefix tailTrace_733513
  have hstable : (prefixWord ++ tailWord_733513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733513).length < 2 ^ (prefixWord ++ tailWord_733513).sum := by decide
  have hdescent : baseEnd_733513 < baseStart_733513 := by decide
  rcases family_descends (prefixWord ++ tailWord_733513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733524 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_733524 : Nat := 118140960795 + 733524 * 2 ^ 59
def prefixEnd_733524 : Nat := 4983230072969 + 3 ^ 40 * 733524 * 2
def baseEnd_733524 : Nat := 376650383608693317676591

theorem tailTrace_733524 : CollatzResearch.WordTrace tailWord_733524 prefixEnd_733524 376650383608693317676591 := by
  unfold tailWord_733524
  simp only [CollatzResearch.WordTrace]
  refine ⟨13376909097287649385291813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17835878796383532513722417 13376909097287649385291813)
  ·
    refine ⟨2508170455741434259742215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13376909097287649385291813 2508170455741434259742215)
    ·
      refine ⟨3762255683612151389613323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2508170455741434259742215 3762255683612151389613323)
      ·
        refine ⟨5643383525418227084419985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3762255683612151389613323 5643383525418227084419985)
        ·
          refine ⟨4232537644063670313314989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5643383525418227084419985 4232537644063670313314989)
          ·
            refine ⟨1587201616523876367493121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4232537644063670313314989 1587201616523876367493121)
            ·
              refine ⟨1190401212392907275619841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587201616523876367493121 1190401212392907275619841)
              ·
                refine ⟨892800909294680456714881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190401212392907275619841 892800909294680456714881)
                ·
                  refine ⟨669600681971010342536161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 892800909294680456714881 669600681971010342536161)
                  ·
                    refine ⟨502200511478257756902121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 669600681971010342536161 502200511478257756902121)
                    ·
                      refine ⟨376650383608693317676591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502200511478257756902121 376650383608693317676591)
                      ·
                        rfl

theorem cell23_733524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_733524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733524 prefixEnd_733524 := by exact prefixLift 733524
  have htrace : WordTrace (prefixWord ++ tailWord_733524) baseStart_733524 baseEnd_733524 := by
    simpa [prefixWord, tailWord_733524, baseEnd_733524] using wordTrace_append hprefix tailTrace_733524
  have hstable : (prefixWord ++ tailWord_733524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733524).length < 2 ^ (prefixWord ++ tailWord_733524).sum := by decide
  have hdescent : baseEnd_733524 < baseStart_733524 := by decide
  rcases family_descends (prefixWord ++ tailWord_733524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733563 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 4]
def baseStart_733563 : Nat := 118140960795 + 733563 * 2 ^ 59
def prefixEnd_733563 : Nat := 4983230072969 + 3 ^ 40 * 733563 * 2
def baseEnd_733563 : Nat := 376670409354218665088911

theorem tailTrace_733563 : CollatzResearch.WordTrace tailWord_733563 prefixEnd_733563 376670409354218665088911 := by
  unfold tailWord_733563
  simp only [CollatzResearch.WordTrace]
  refine ⟨26755240641434008431253343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17836827094289338954168895 26755240641434008431253343)
  ·
    refine ⟨40132860962151012646880015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26755240641434008431253343 40132860962151012646880015)
    ·
      refine ⟨60199291443226518970320023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40132860962151012646880015 60199291443226518970320023)
      ·
        refine ⟨90298937164839778455480035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60199291443226518970320023 90298937164839778455480035)
        ·
          refine ⟨135448405747259667683220053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90298937164839778455480035 135448405747259667683220053)
          ·
            refine ⟨1587286004850699230662735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 135448405747259667683220053 1587286004850699230662735)
            ·
              refine ⟨2380929007276048845994103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587286004850699230662735 2380929007276048845994103)
              ·
                refine ⟨3571393510914073268991155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2380929007276048845994103 3571393510914073268991155)
                ·
                  refine ⟨5357090266371109903486733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571393510914073268991155 5357090266371109903486733)
                  ·
                    refine ⟨2008908849889166213807525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5357090266371109903486733 2008908849889166213807525)
                    ·
                      refine ⟨376670409354218665088911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2008908849889166213807525 376670409354218665088911)
                      ·
                        rfl

theorem cell23_733563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 4].length) (baseStart_733563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733563 prefixEnd_733563 := by exact prefixLift 733563
  have htrace : WordTrace (prefixWord ++ tailWord_733563) baseStart_733563 baseEnd_733563 := by
    simpa [prefixWord, tailWord_733563, baseEnd_733563] using wordTrace_append hprefix tailTrace_733563
  have hstable : (prefixWord ++ tailWord_733563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733563).length < 2 ^ (prefixWord ++ tailWord_733563).sum := by decide
  have hdescent : baseEnd_733563 < baseStart_733563 := by decide
  rcases family_descends (prefixWord ++ tailWord_733563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733573 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 7, 4]
def baseStart_733573 : Nat := 118140960795 + 733573 * 2 ^ 59
def prefixEnd_733573 : Nat := 4983230072969 + 3 ^ 40 * 733573 * 2
def baseEnd_733573 : Nat := 125558514720254541987955

theorem tailTrace_733573 : CollatzResearch.WordTrace tailWord_733573 prefixEnd_733573 125558514720254541987955 := by
  unfold tailWord_733573
  simp only [CollatzResearch.WordTrace]
  refine ⟨26755605371397780139117373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17837070247598520092744915 26755605371397780139117373)
  ·
    refine ⟨10033352014274167552169015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26755605371397780139117373 10033352014274167552169015)
    ·
      refine ⟨15050028021411251328253523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10033352014274167552169015 15050028021411251328253523)
      ·
        refine ⟨22575042032116876992380285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15050028021411251328253523 22575042032116876992380285)
        ·
          refine ⟨8465640762043828872142607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22575042032116876992380285 8465640762043828872142607)
          ·
            refine ⟨12698461143065743308213911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8465640762043828872142607 12698461143065743308213911)
            ·
              refine ⟨19047691714598614962320867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12698461143065743308213911 19047691714598614962320867)
              ·
                refine ⟨28571537571897922443481301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19047691714598614962320867 28571537571897922443481301)
                ·
                  refine ⟨669645411841357557269093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 28571537571897922443481301 669645411841357557269093)
                  ·
                    refine ⟨125558514720254541987955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 669645411841357557269093 125558514720254541987955)
                    ·
                      rfl

theorem cell23_733573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_733573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733573 prefixEnd_733573 := by exact prefixLift 733573
  have htrace : WordTrace (prefixWord ++ tailWord_733573) baseStart_733573 baseEnd_733573 := by
    simpa [prefixWord, tailWord_733573, baseEnd_733573] using wordTrace_append hprefix tailTrace_733573
  have hstable : (prefixWord ++ tailWord_733573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733573).length < 2 ^ (prefixWord ++ tailWord_733573).sum := by decide
  have hdescent : baseEnd_733573 < baseStart_733573 := by decide
  rcases family_descends (prefixWord ++ tailWord_733573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733580 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 2, 4, 2]
def baseStart_733580 : Nat := 118140960795 + 733580 * 2 ^ 59
def prefixEnd_733580 : Nat := 4983230072969 + 3 ^ 40 * 733580 * 2
def baseEnd_733580 : Nat := 376679138525345098576333

theorem tailTrace_733580 : CollatzResearch.WordTrace tailWord_733580 prefixEnd_733580 376679138525345098576333 := by
  unfold tailWord_733580
  simp only [CollatzResearch.WordTrace]
  refine ⟨13377930341186210167311097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17837240454914946889748129 13377930341186210167311097)
  ·
    refine ⟨10033447755889657625483323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13377930341186210167311097 10033447755889657625483323)
    ·
      refine ⟨15050171633834486438224985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10033447755889657625483323 15050171633834486438224985)
      ·
        refine ⟨11287628725375864828668739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15050171633834486438224985 11287628725375864828668739)
        ·
          refine ⟨16931443088063797243003109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11287628725375864828668739 16931443088063797243003109)
          ·
            refine ⟨3174645579011961983063083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16931443088063797243003109 3174645579011961983063083)
            ·
              refine ⟨4761968368517942974594625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174645579011961983063083 4761968368517942974594625)
              ·
                refine ⟨3571476276388457230945969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4761968368517942974594625 3571476276388457230945969)
                ·
                  refine ⟨2678607207291342923209477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3571476276388457230945969 2678607207291342923209477)
                  ·
                    refine ⟨502238851367126798101777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2678607207291342923209477 502238851367126798101777)
                    ·
                      refine ⟨376679138525345098576333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502238851367126798101777 376679138525345098576333)
                      ·
                        rfl

theorem cell23_733580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_733580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733580 prefixEnd_733580 := by exact prefixLift 733580
  have htrace : WordTrace (prefixWord ++ tailWord_733580) baseStart_733580 baseEnd_733580 := by
    simpa [prefixWord, tailWord_733580, baseEnd_733580] using wordTrace_append hprefix tailTrace_733580
  have hstable : (prefixWord ++ tailWord_733580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733580).length < 2 ^ (prefixWord ++ tailWord_733580).sum := by decide
  have hdescent : baseEnd_733580 < baseStart_733580 := by decide
  rcases family_descends (prefixWord ++ tailWord_733580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733674 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_733674 : Nat := 118140960795 + 733674 * 2 ^ 59
def prefixEnd_733674 : Nat := 4983230072969 + 3 ^ 40 * 733674 * 2
def baseEnd_733674 : Nat := 376727405706867730800901

theorem tailTrace_733674 : CollatzResearch.WordTrace tailWord_733674 prefixEnd_733674 376727405706867730800901 := by
  unfold tailWord_733674
  simp only [CollatzResearch.WordTrace]
  refine ⟨6689822286007968597136019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17839526096021249592362717 6689822286007968597136019)
  ·
    refine ⟨10034733429011952895704029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6689822286007968597136019 10034733429011952895704029)
    ·
      refine ⟨3763025035879482335889011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10034733429011952895704029 3763025035879482335889011)
      ·
        refine ⟨5644537553819223503833517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3763025035879482335889011 5644537553819223503833517)
        ·
          refine ⟨2116701582682208813937569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5644537553819223503833517 2116701582682208813937569)
          ·
            refine ⟨1587526187011656610453177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2116701582682208813937569 1587526187011656610453177)
            ·
              refine ⟨1190644640258742457839883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587526187011656610453177 1190644640258742457839883)
              ·
                refine ⟨1785966960388113686759825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190644640258742457839883 1785966960388113686759825)
                ·
                  refine ⟨1339475220291085265069869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1785966960388113686759825 1339475220291085265069869)
                  ·
                    refine ⟨502303207609156974401201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1339475220291085265069869 502303207609156974401201)
                    ·
                      refine ⟨376727405706867730800901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502303207609156974401201 376727405706867730800901)
                      ·
                        rfl

theorem cell23_733674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_733674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733674 prefixEnd_733674 := by exact prefixLift 733674
  have htrace : WordTrace (prefixWord ++ tailWord_733674) baseStart_733674 baseEnd_733674 := by
    simpa [prefixWord, tailWord_733674, baseEnd_733674] using wordTrace_append hprefix tailTrace_733674
  have hstable : (prefixWord ++ tailWord_733674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733674).length < 2 ^ (prefixWord ++ tailWord_733674).sum := by decide
  have hdescent : baseEnd_733674 < baseStart_733674 := by decide
  rcases family_descends (prefixWord ++ tailWord_733674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733697 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 2, 4]
def baseStart_733697 : Nat := 118140960795 + 733697 * 2 ^ 59
def prefixEnd_733697 : Nat := 4983230072969 + 3 ^ 40 * 733697 * 2
def baseEnd_733697 : Nat := 125579738587307046937765

theorem tailTrace_733697 : CollatzResearch.WordTrace tailWord_733697 prefixEnd_733697 125579738587307046937765 := by
  unfold tailWord_733697
  simp only [CollatzResearch.WordTrace]
  refine ⟨26760128022948549316631345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17840085348632366211087563 26760128022948549316631345)
  ·
    refine ⟨20070096017211411987473509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26760128022948549316631345 20070096017211411987473509)
    ·
      refine ⟨3763143003227139747651283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20070096017211411987473509 3763143003227139747651283)
      ·
        refine ⟨5644714504840709621476925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3763143003227139747651283 5644714504840709621476925)
        ·
          refine ⟨2116767939315266108053847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5644714504840709621476925 2116767939315266108053847)
          ·
            refine ⟨3175151908972899162080771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116767939315266108053847 3175151908972899162080771)
            ·
              refine ⟨4762727863459348743121157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175151908972899162080771 4762727863459348743121157)
              ·
                refine ⟨893011474398627889335217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4762727863459348743121157 893011474398627889335217)
                ·
                  refine ⟨669758605798970917001413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 893011474398627889335217 669758605798970917001413)
                  ·
                    refine ⟨125579738587307046937765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 669758605798970917001413 125579738587307046937765)
                    ·
                      rfl

theorem cell23_733697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_733697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733697 prefixEnd_733697 := by exact prefixLift 733697
  have htrace : WordTrace (prefixWord ++ tailWord_733697) baseStart_733697 baseEnd_733697 := by
    simpa [prefixWord, tailWord_733697, baseEnd_733697] using wordTrace_append hprefix tailTrace_733697
  have hstable : (prefixWord ++ tailWord_733697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733697).length < 2 ^ (prefixWord ++ tailWord_733697).sum := by decide
  have hdescent : baseEnd_733697 < baseStart_733697 := by decide
  rcases family_descends (prefixWord ++ tailWord_733697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733698 : List Nat := [3, 4, 1, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_733698 : Nat := 118140960795 + 733698 * 2 ^ 59
def prefixEnd_733698 : Nat := 4983230072969 + 3 ^ 40 * 733698 * 2
def baseEnd_733698 : Nat := 376739729242575636900791

theorem tailTrace_733698 : CollatzResearch.WordTrace tailWord_733698 prefixEnd_733698 376739729242575636900791 := by
  unfold tailWord_733698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6690041123986231621854437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17840109663963284324945165 6690041123986231621854437)
  ·
    refine ⟨1254382710747418429097707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6690041123986231621854437 1254382710747418429097707)
    ·
      refine ⟨1881574066121127643646561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1254382710747418429097707 1881574066121127643646561)
      ·
        refine ⟨1411180549590845732734921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1881574066121127643646561 1411180549590845732734921)
        ·
          refine ⟨1058385412193134299551191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1411180549590845732734921 1058385412193134299551191)
          ·
            refine ⟨1587578118289701449326787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058385412193134299551191 1587578118289701449326787)
            ·
              refine ⟨2381367177434552173990181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587578118289701449326787 2381367177434552173990181)
              ·
                refine ⟨446506345768978532623159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2381367177434552173990181 446506345768978532623159)
                ·
                  refine ⟨669759518653467798934739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446506345768978532623159 669759518653467798934739)
                  ·
                    refine ⟨1004639277980201698402109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 669759518653467798934739 1004639277980201698402109)
                    ·
                      refine ⟨376739729242575636900791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1004639277980201698402109 376739729242575636900791)
                      ·
                        rfl

theorem cell23_733698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_733698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733698 prefixEnd_733698 := by exact prefixLift 733698
  have htrace : WordTrace (prefixWord ++ tailWord_733698) baseStart_733698 baseEnd_733698 := by
    simpa [prefixWord, tailWord_733698, baseEnd_733698] using wordTrace_append hprefix tailTrace_733698
  have hstable : (prefixWord ++ tailWord_733698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733698).length < 2 ^ (prefixWord ++ tailWord_733698).sum := by decide
  have hdescent : baseEnd_733698 < baseStart_733698 := by decide
  rcases family_descends (prefixWord ++ tailWord_733698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733710 : List Nat := [4, 1, 1, 2, 3, 1, 3, 8]
def baseStart_733710 : Nat := 118140960795 + 733710 * 2 ^ 59
def prefixEnd_733710 : Nat := 4983230072969 + 3 ^ 40 * 733710 * 2
def baseEnd_733710 : Nat := 13953551518904799627805

theorem tailTrace_733710 : CollatzResearch.WordTrace tailWord_733710 prefixEnd_733710 13953551518904799627805 := by
  unfold tailWord_733710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3345075271487681567106823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17840401447934301691236389 3345075271487681567106823)
  ·
    refine ⟨5017612907231522350660235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3345075271487681567106823 5017612907231522350660235)
    ·
      refine ⟨7526419360847283525990353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5017612907231522350660235 7526419360847283525990353)
      ·
        refine ⟨5644814520635462644492765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7526419360847283525990353 5644814520635462644492765)
        ·
          refine ⟨2116805445238298491684787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5644814520635462644492765 2116805445238298491684787)
          ·
            refine ⟨3175208167857447737527181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116805445238298491684787 3175208167857447737527181)
            ·
              refine ⟨1190703062946542901572693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3175208167857447737527181 1190703062946542901572693)
              ·
                refine ⟨13953551518904799627805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1190703062946542901572693 13953551518904799627805)
                ·
                  rfl

theorem cell23_733710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_733710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733710 prefixEnd_733710 := by exact prefixLift 733710
  have htrace : WordTrace (prefixWord ++ tailWord_733710) baseStart_733710 baseEnd_733710 := by
    simpa [prefixWord, tailWord_733710, baseEnd_733710] using wordTrace_append hprefix tailTrace_733710
  have hstable : (prefixWord ++ tailWord_733710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733710).length < 2 ^ (prefixWord ++ tailWord_733710).sum := by decide
  have hdescent : baseEnd_733710 < baseStart_733710 := by decide
  rcases family_descends (prefixWord ++ tailWord_733710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733738 : List Nat := [3, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_733738 : Nat := 118140960795 + 733738 * 2 ^ 59
def prefixEnd_733738 : Nat := 4983230072969 + 3 ^ 40 * 733738 * 2
def baseEnd_733738 : Nat := 376760268468755480400607

theorem tailTrace_733738 : CollatzResearch.WordTrace tailWord_733738 prefixEnd_733738 376760268468755480400607 := by
  unfold tailWord_733738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6690405853950003329718467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17841082277200008879249245 6690405853950003329718467)
  ·
    refine ⟨10035608780925004994577701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6690405853950003329718467 10035608780925004994577701)
    ·
      refine ⟨1881676646423438436483319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10035608780925004994577701 1881676646423438436483319)
      ·
        refine ⟨2822514969635157654724979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881676646423438436483319 2822514969635157654724979)
        ·
          refine ⟨4233772454452736482087469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822514969635157654724979 4233772454452736482087469)
          ·
            refine ⟨1587664670419776180782801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4233772454452736482087469 1587664670419776180782801)
            ·
              refine ⟨1190748502814832135587101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587664670419776180782801 1190748502814832135587101)
              ·
                refine ⟨446530688555562050845163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1190748502814832135587101 446530688555562050845163)
                ·
                  refine ⟨669796032833343076267745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446530688555562050845163 669796032833343076267745)
                  ·
                    refine ⟨502347024625007307200809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 669796032833343076267745 502347024625007307200809)
                    ·
                      refine ⟨376760268468755480400607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502347024625007307200809 376760268468755480400607)
                      ·
                        rfl

theorem cell23_733738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_733738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733738 prefixEnd_733738 := by exact prefixLift 733738
  have htrace : WordTrace (prefixWord ++ tailWord_733738) baseStart_733738 baseEnd_733738 := by
    simpa [prefixWord, tailWord_733738, baseEnd_733738] using wordTrace_append hprefix tailTrace_733738
  have hstable : (prefixWord ++ tailWord_733738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733738).length < 2 ^ (prefixWord ++ tailWord_733738).sum := by decide
  have hdescent : baseEnd_733738 < baseStart_733738 := by decide
  rcases family_descends (prefixWord ++ tailWord_733738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733748 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_733748 : Nat := 118140960795 + 733748 * 2 ^ 59
def prefixEnd_733748 : Nat := 4983230072969 + 3 ^ 40 * 733748 * 2
def baseEnd_733748 : Nat := 125588467758433480425187

theorem tailTrace_733748 : CollatzResearch.WordTrace tailWord_733748 prefixEnd_733748 125588467758433480425187 := by
  unfold tailWord_733748
  simp only [CollatzResearch.WordTrace]
  refine ⟨13380994072881892513368949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17841325430509190017825265 13380994072881892513368949)
  ·
    refine ⟨1254468194332677423128339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13380994072881892513368949 1254468194332677423128339)
    ·
      refine ⟨1881702291499016134692509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1254468194332677423128339 1881702291499016134692509)
      ·
        refine ⟨705638359312131050509691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1881702291499016134692509 705638359312131050509691)
        ·
          refine ⟨1058457538968196575764537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705638359312131050509691 1058457538968196575764537)
          ·
            refine ⟨793843154226147431823403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1058457538968196575764537 793843154226147431823403)
            ·
              refine ⟨1190764731339221147735105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793843154226147431823403 1190764731339221147735105)
              ·
                refine ⟨893073548504415860801329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190764731339221147735105 893073548504415860801329)
                ·
                  refine ⟨669805161378311895600997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 893073548504415860801329 669805161378311895600997)
                  ·
                    refine ⟨125588467758433480425187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 669805161378311895600997 125588467758433480425187)
                    ·
                      rfl

theorem cell23_733748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_733748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733748 prefixEnd_733748 := by exact prefixLift 733748
  have htrace : WordTrace (prefixWord ++ tailWord_733748) baseStart_733748 baseEnd_733748 := by
    simpa [prefixWord, tailWord_733748, baseEnd_733748] using wordTrace_append hprefix tailTrace_733748
  have hstable : (prefixWord ++ tailWord_733748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733748).length < 2 ^ (prefixWord ++ tailWord_733748).sum := by decide
  have hdescent : baseEnd_733748 < baseStart_733748 := by decide
  rcases family_descends (prefixWord ++ tailWord_733748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733754 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3]
def baseStart_733754 : Nat := 118140960795 + 733754 * 2 ^ 59
def prefixEnd_733754 : Nat := 4983230072969 + 3 ^ 40 * 733754 * 2
def baseEnd_733754 : Nat := 376768484159227417800533

theorem tailTrace_733754 : CollatzResearch.WordTrace tailWord_733754 prefixEnd_733754 376768484159227417800533 := by
  unfold tailWord_733754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6690551745935512012864079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17841471322494698700970877 6690551745935512012864079)
  ·
    refine ⟨10035827618903268019296119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6690551745935512012864079 10035827618903268019296119)
    ·
      refine ⟨15053741428354902028944179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10035827618903268019296119 15053741428354902028944179)
      ·
        refine ⟨22580612142532353043416269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15053741428354902028944179 22580612142532353043416269)
        ·
          refine ⟨8467729553449632391281101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22580612142532353043416269 8467729553449632391281101)
          ·
            refine ⟨3175398582543612146730413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8467729553449632391281101 3175398582543612146730413)
            ·
              refine ⟨1190774468453854555023905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3175398582543612146730413 1190774468453854555023905)
              ·
                refine ⟨893080851340390916267929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190774468453854555023905 893080851340390916267929)
                ·
                  refine ⟨669810638505293187200947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 893080851340390916267929 669810638505293187200947)
                  ·
                    refine ⟨1004715957757939780801421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 669810638505293187200947 1004715957757939780801421)
                    ·
                      refine ⟨376768484159227417800533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1004715957757939780801421 376768484159227417800533)
                      ·
                        rfl

theorem cell23_733754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_733754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733754 prefixEnd_733754 := by exact prefixLift 733754
  have htrace : WordTrace (prefixWord ++ tailWord_733754) baseStart_733754 baseEnd_733754 := by
    simpa [prefixWord, tailWord_733754, baseEnd_733754] using wordTrace_append hprefix tailTrace_733754
  have hstable : (prefixWord ++ tailWord_733754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733754).length < 2 ^ (prefixWord ++ tailWord_733754).sum := by decide
  have hdescent : baseEnd_733754 < baseStart_733754 := by decide
  rcases family_descends (prefixWord ++ tailWord_733754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733770 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_733770 : Nat := 118140960795 + 733770 * 2 ^ 59
def prefixEnd_733770 : Nat := 4983230072969 + 3 ^ 40 * 733770 * 2
def baseEnd_733770 : Nat := 125592233283233118400153

theorem tailTrace_733770 : CollatzResearch.WordTrace tailWord_733770 prefixEnd_733770 125592233283233118400153 := by
  unfold tailWord_733770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6690697637921020696009691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17841860367789388522692509 6690697637921020696009691)
  ·
    refine ⟨10036046456881531044014537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6690697637921020696009691 10036046456881531044014537)
    ·
      refine ⟨7527034842661148283010903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10036046456881531044014537 7527034842661148283010903)
      ·
        refine ⟨11290552263991722424516355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7527034842661148283010903 11290552263991722424516355)
        ·
          refine ⟨16935828395987583636774533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11290552263991722424516355 16935828395987583636774533)
          ·
            refine ⟨3175467824247671931895225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16935828395987583636774533 3175467824247671931895225)
            ·
              refine ⟨2381600868185753948921419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3175467824247671931895225 2381600868185753948921419)
              ·
                refine ⟨3572401302278630923382129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381600868185753948921419 3572401302278630923382129)
                ·
                  refine ⟨2679300976708973192536597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3572401302278630923382129 2679300976708973192536597)
                  ·
                    refine ⟨125592233283233118400153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2679300976708973192536597 125592233283233118400153)
                    ·
                      rfl

theorem cell23_733770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_733770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733770 prefixEnd_733770 := by exact prefixLift 733770
  have htrace : WordTrace (prefixWord ++ tailWord_733770) baseStart_733770 baseEnd_733770 := by
    simpa [prefixWord, tailWord_733770, baseEnd_733770] using wordTrace_append hprefix tailTrace_733770
  have hstable : (prefixWord ++ tailWord_733770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733770).length < 2 ^ (prefixWord ++ tailWord_733770).sum := by decide
  have hdescent : baseEnd_733770 < baseStart_733770 := by decide
  rcases family_descends (prefixWord ++ tailWord_733770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733797 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 5]
def baseStart_733797 : Nat := 118140960795 + 733797 * 2 ^ 59
def prefixEnd_733797 : Nat := 4983230072969 + 3 ^ 40 * 733797 * 2
def baseEnd_733797 : Nat := 376790563827370749562835

theorem tailTrace_733797 : CollatzResearch.WordTrace tailWord_733797 prefixEnd_733797 376790563827370749562835 := by
  unfold tailWord_733797
  simp only [CollatzResearch.WordTrace]
  refine ⟨26763775322586266395271645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17842516881724177596847763 26763775322586266395271645)
  ·
    refine ⟨10036415745969849898226867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26763775322586266395271645 10036415745969849898226867)
    ·
      refine ⟨15054623618954774847340301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10036415745969849898226867 15054623618954774847340301)
      ·
        refine ⟨5645483857108040567752613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15054623618954774847340301 5645483857108040567752613)
        ·
          refine ⟨1058528223207757606453615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5645483857108040567752613 1058528223207757606453615)
          ·
            refine ⟨1587792334811636409680423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058528223207757606453615 1587792334811636409680423)
            ·
              refine ⟨2381688502217454614520635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587792334811636409680423 2381688502217454614520635)
              ·
                refine ⟨3572532753326181921780953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381688502217454614520635 3572532753326181921780953)
                ·
                  refine ⟨2679399564994636441335715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3572532753326181921780953 2679399564994636441335715)
                  ·
                    refine ⟨4019099347491954662003573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2679399564994636441335715 4019099347491954662003573)
                    ·
                      refine ⟨376790563827370749562835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4019099347491954662003573 376790563827370749562835)
                      ·
                        rfl

theorem cell23_733797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_733797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733797 prefixEnd_733797 := by exact prefixLift 733797
  have htrace : WordTrace (prefixWord ++ tailWord_733797) baseStart_733797 baseEnd_733797 := by
    simpa [prefixWord, tailWord_733797, baseEnd_733797] using wordTrace_append hprefix tailTrace_733797
  have hstable : (prefixWord ++ tailWord_733797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733797).length < 2 ^ (prefixWord ++ tailWord_733797).sum := by decide
  have hdescent : baseEnd_733797 < baseStart_733797 := by decide
  rcases family_descends (prefixWord ++ tailWord_733797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733817 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 7]
def baseStart_733817 : Nat := 118140960795 + 733817 * 2 ^ 59
def prefixEnd_733817 : Nat := 4983230072969 + 3 ^ 40 * 733817 * 2
def baseEnd_733817 : Nat := 41866759271162296812527

theorem tailTrace_733817 : CollatzResearch.WordTrace tailWord_733817 prefixEnd_733817 41866759271162296812527 := by
  unfold tailWord_733817
  simp only [CollatzResearch.WordTrace]
  refine ⟨26764504782513809810999705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17843003188342539873999803 26764504782513809810999705)
  ·
    refine ⟨20073378586885357358249779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26764504782513809810999705 20073378586885357358249779)
    ·
      refine ⟨30110067880328036037374669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20073378586885357358249779 30110067880328036037374669)
      ·
        refine ⟨11291275455123013514015501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30110067880328036037374669 11291275455123013514015501)
        ·
          refine ⟨4234228295671130067755813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11291275455123013514015501 4234228295671130067755813)
          ·
            refine ⟨793917805438336887704215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4234228295671130067755813 793917805438336887704215)
            ·
              refine ⟨1190876708157505331556323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793917805438336887704215 1190876708157505331556323)
              ·
                refine ⟨1786315062236257997334485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190876708157505331556323 1786315062236257997334485)
                ·
                  refine ⟨41866759271162296812527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1786315062236257997334485 41866759271162296812527)
                  ·
                    rfl

theorem cell23_733817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 7].length) (baseStart_733817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733817 prefixEnd_733817 := by exact prefixLift 733817
  have htrace : WordTrace (prefixWord ++ tailWord_733817) baseStart_733817 baseEnd_733817 := by
    simpa [prefixWord, tailWord_733817, baseEnd_733817] using wordTrace_append hprefix tailTrace_733817
  have hstable : (prefixWord ++ tailWord_733817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733817).length < 2 ^ (prefixWord ++ tailWord_733817).sum := by decide
  have hdescent : baseEnd_733817 < baseStart_733817 := by decide
  rcases family_descends (prefixWord ++ tailWord_733817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733828 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_733828 : Nat := 118140960795 + 733828 * 2 ^ 59
def prefixEnd_733828 : Nat := 4983230072969 + 3 ^ 40 * 733828 * 2
def baseEnd_733828 : Nat := 376806481727660128275193

theorem tailTrace_733828 : CollatzResearch.WordTrace tailWord_733828 prefixEnd_733828 376806481727660128275193 := by
  unfold tailWord_733828
  simp only [CollatzResearch.WordTrace]
  refine ⟨13382452992736979344825069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17843270656982639126433425 13382452992736979344825069)
  ·
    refine ⟨5018419872276367254309401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13382452992736979344825069 5018419872276367254309401)
    ·
      refine ⟨3763814904207275440732051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5018419872276367254309401 3763814904207275440732051)
      ·
        refine ⟨5645722356310913161098077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3763814904207275440732051 5645722356310913161098077)
        ·
          refine ⟨2117145883616592435411779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5645722356310913161098077 2117145883616592435411779)
          ·
            refine ⟨3175718825424888653117669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117145883616592435411779 3175718825424888653117669)
            ·
              refine ⟨595447279767166622459563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3175718825424888653117669 595447279767166622459563)
              ·
                refine ⟨893170919650749933689345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595447279767166622459563 893170919650749933689345)
                ·
                  refine ⟨669878189738062450267009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 893170919650749933689345 669878189738062450267009)
                  ·
                    refine ⟨502408642303546837700257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 669878189738062450267009 502408642303546837700257)
                    ·
                      refine ⟨376806481727660128275193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502408642303546837700257 376806481727660128275193)
                      ·
                        rfl

theorem cell23_733828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_733828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733828 prefixEnd_733828 := by exact prefixLift 733828
  have htrace : WordTrace (prefixWord ++ tailWord_733828) baseStart_733828 baseEnd_733828 := by
    simpa [prefixWord, tailWord_733828, baseEnd_733828] using wordTrace_append hprefix tailTrace_733828
  have hstable : (prefixWord ++ tailWord_733828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733828).length < 2 ^ (prefixWord ++ tailWord_733828).sum := by decide
  have hdescent : baseEnd_733828 < baseStart_733828 := by decide
  rcases family_descends (prefixWord ++ tailWord_733828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733847 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 2, 5]
def baseStart_733847 : Nat := 118140960795 + 733847 * 2 ^ 59
def prefixEnd_733847 : Nat := 4983230072969 + 3 ^ 40 * 733847 * 2
def baseEnd_733847 : Nat := 125605412620031851312535

theorem tailTrace_733847 : CollatzResearch.WordTrace tailWord_733847 prefixEnd_733847 125605412620031851312535 := by
  unfold tailWord_733847
  simp only [CollatzResearch.WordTrace]
  refine ⟨26765598972405124934591795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17843732648270083289727863 26765598972405124934591795)
  ·
    refine ⟨40148398458607687401887693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26765598972405124934591795 40148398458607687401887693)
    ·
      refine ⟨15055649421977882775707885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40148398458607687401887693 15055649421977882775707885)
      ·
        refine ⟨5645868533241706040890457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15055649421977882775707885 5645868533241706040890457)
        ·
          refine ⟨4234401399931279530667843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5645868533241706040890457 4234401399931279530667843)
          ·
            refine ⟨6351602099896919296001765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4234401399931279530667843 6351602099896919296001765)
            ·
              refine ⟨1190925393730672368000331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6351602099896919296001765 1190925393730672368000331)
              ·
                refine ⟨1786388090596008552000497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190925393730672368000331 1786388090596008552000497)
                ·
                  refine ⟨1339791067947006414000373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1786388090596008552000497 1339791067947006414000373)
                  ·
                    refine ⟨125605412620031851312535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1339791067947006414000373 125605412620031851312535)
                    ·
                      rfl

theorem cell23_733847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_733847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733847 prefixEnd_733847 := by exact prefixLift 733847
  have htrace : WordTrace (prefixWord ++ tailWord_733847) baseStart_733847 baseEnd_733847 := by
    simpa [prefixWord, tailWord_733847, baseEnd_733847] using wordTrace_append hprefix tailTrace_733847
  have hstable : (prefixWord ++ tailWord_733847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733847).length < 2 ^ (prefixWord ++ tailWord_733847).sum := by decide
  have hdescent : baseEnd_733847 < baseStart_733847 := by decide
  rcases family_descends (prefixWord ++ tailWord_733847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733880 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_733880 : Nat := 118140960795 + 733880 * 2 ^ 59
def prefixEnd_733880 : Nat := 4983230072969 + 3 ^ 40 * 733880 * 2
def baseEnd_733880 : Nat := 376833182721693924824953

theorem tailTrace_733880 : CollatzResearch.WordTrace tailWord_733880 prefixEnd_733880 376833182721693924824953 := by
  unfold tailWord_733880
  simp only [CollatzResearch.WordTrace]
  refine ⟨13383401290642785785271547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17844535054190381047028729 13383401290642785785271547)
  ·
    refine ⟨20075101935964178677907321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13383401290642785785271547 20075101935964178677907321)
    ·
      refine ⟨15056326451973134008430491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20075101935964178677907321 15056326451973134008430491)
      ·
        refine ⟨22584489677959701012645737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15056326451973134008430491 22584489677959701012645737)
        ·
          refine ⟨16938367258469775759484303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22584489677959701012645737 16938367258469775759484303)
          ·
            refine ⟨25407550887704663639226455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16938367258469775759484303 25407550887704663639226455)
            ·
              refine ⟨38111326331556995458839683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25407550887704663639226455 38111326331556995458839683)
              ·
                refine ⟨57166989497335493188259525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38111326331556995458839683 57166989497335493188259525)
                ·
                  refine ⟨10718810530750404972798661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57166989497335493188259525 10718810530750404972798661)
                  ·
                    refine ⟨2009776974515700932399749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10718810530750404972798661 2009776974515700932399749)
                    ·
                      refine ⟨376833182721693924824953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2009776974515700932399749 376833182721693924824953)
                      ·
                        rfl

theorem cell23_733880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_733880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733880 prefixEnd_733880 := by exact prefixLift 733880
  have htrace : WordTrace (prefixWord ++ tailWord_733880) baseStart_733880 baseEnd_733880 := by
    simpa [prefixWord, tailWord_733880, baseEnd_733880] using wordTrace_append hprefix tailTrace_733880
  have hstable : (prefixWord ++ tailWord_733880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733880).length < 2 ^ (prefixWord ++ tailWord_733880).sum := by decide
  have hdescent : baseEnd_733880 < baseStart_733880 := by decide
  rcases family_descends (prefixWord ++ tailWord_733880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733884 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 2, 4, 2]
def baseStart_733884 : Nat := 118140960795 + 733884 * 2 ^ 59
def prefixEnd_733884 : Nat := 4983230072969 + 3 ^ 40 * 733884 * 2
def baseEnd_733884 : Nat := 376835236644311909174935

theorem tailTrace_733884 : CollatzResearch.WordTrace tailWord_733884 prefixEnd_733884 376835236644311909174935 := by
  unfold tailWord_733884
  simp only [CollatzResearch.WordTrace]
  refine ⟨13383474236635540126844353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17844632315514053502459137 13383474236635540126844353)
  ·
    refine ⟨10037605677476655095133265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13383474236635540126844353 10037605677476655095133265)
    ·
      refine ⟨7528204258107491321349949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10037605677476655095133265 7528204258107491321349949)
      ·
        refine ⟨2823076596790309245506231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7528204258107491321349949 2823076596790309245506231)
        ·
          refine ⟨4234614895185463868259347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2823076596790309245506231 4234614895185463868259347)
          ·
            refine ⟨6351922342778195802389021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4234614895185463868259347 6351922342778195802389021)
            ·
              refine ⟨2381970878541823425895883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6351922342778195802389021 2381970878541823425895883)
              ·
                refine ⟨3572956317812735138843825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381970878541823425895883 3572956317812735138843825)
                ·
                  refine ⟨2679717238359551354132869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3572956317812735138843825 2679717238359551354132869)
                  ·
                    refine ⟨502446982192415878899913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2679717238359551354132869 502446982192415878899913)
                    ·
                      refine ⟨376835236644311909174935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502446982192415878899913 376835236644311909174935)
                      ·
                        rfl

theorem cell23_733884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_733884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733884 prefixEnd_733884 := by exact prefixLift 733884
  have htrace : WordTrace (prefixWord ++ tailWord_733884) baseStart_733884 baseEnd_733884 := by
    simpa [prefixWord, tailWord_733884, baseEnd_733884] using wordTrace_append hprefix tailTrace_733884
  have hstable : (prefixWord ++ tailWord_733884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733884).length < 2 ^ (prefixWord ++ tailWord_733884).sum := by decide
  have hdescent : baseEnd_733884 < baseStart_733884 := by decide
  rcases family_descends (prefixWord ++ tailWord_733884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733901 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_733901 : Nat := 118140960795 + 733901 * 2 ^ 59
def prefixEnd_733901 : Nat := 4983230072969 + 3 ^ 40 * 733901 * 2
def baseEnd_733901 : Nat := 376843965815438342662357

theorem tailTrace_733901 : CollatzResearch.WordTrace tailWord_733901 prefixEnd_733901 376843965815438342662357 := by
  unfold tailWord_733901
  simp only [CollatzResearch.WordTrace]
  refine ⟨26767568514209492157057557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17845045676139661438038371 26767568514209492157057557)
  ·
    refine ⟨1254729774103569944862073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26767568514209492157057557 1254729774103569944862073)
    ·
      refine ⟨941047330577677458646555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1254729774103569944862073 941047330577677458646555)
      ·
        refine ⟨1411570995866516187969833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941047330577677458646555 1411570995866516187969833)
        ·
          refine ⟨1058678246899887140977375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1411570995866516187969833 1058678246899887140977375)
          ·
            refine ⟨1588017370349830711466063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058678246899887140977375 1588017370349830711466063)
            ·
              refine ⟨2382026055524746067199095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588017370349830711466063 2382026055524746067199095)
              ·
                refine ⟨3573039083287119100798643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382026055524746067199095 3573039083287119100798643)
                ·
                  refine ⟨5359558624930678651197965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573039083287119100798643 5359558624930678651197965)
                  ·
                    refine ⟨2009834484349004494199237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5359558624930678651197965 2009834484349004494199237)
                    ·
                      refine ⟨376843965815438342662357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2009834484349004494199237 376843965815438342662357)
                      ·
                        rfl

theorem cell23_733901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_733901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733901 prefixEnd_733901 := by exact prefixLift 733901
  have htrace : WordTrace (prefixWord ++ tailWord_733901) baseStart_733901 baseEnd_733901 := by
    simpa [prefixWord, tailWord_733901, baseEnd_733901] using wordTrace_append hprefix tailTrace_733901
  have hstable : (prefixWord ++ tailWord_733901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733901).length < 2 ^ (prefixWord ++ tailWord_733901).sum := by decide
  have hdescent : baseEnd_733901 < baseStart_733901 := by decide
  rcases family_descends (prefixWord ++ tailWord_733901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733911 : List Nat := [1, 1, 3, 2, 1, 5, 2, 3, 1, 4]
def baseStart_733911 : Nat := 118140960795 + 733911 * 2 ^ 59
def prefixEnd_733911 : Nat := 4983230072969 + 3 ^ 40 * 733911 * 2
def baseEnd_733911 : Nat := 125616366873994434512437

theorem tailTrace_733911 : CollatzResearch.WordTrace tailWord_733911 prefixEnd_733911 125616366873994434512437 := by
  unfold tailWord_733911
  simp only [CollatzResearch.WordTrace]
  refine ⟨26767933244173263864921587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17845288829448842576614391 26767933244173263864921587)
  ·
    refine ⟨40151899866259895797382381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26767933244173263864921587 40151899866259895797382381)
    ·
      refine ⟨15056962449847460924018393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40151899866259895797382381 15056962449847460924018393)
      ·
        refine ⟨11292721837385595693013795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15056962449847460924018393 11292721837385595693013795)
        ·
          refine ⟨16939082756078393539520693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11292721837385595693013795 16939082756078393539520693)
          ·
            refine ⟨1588039008382349394330065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16939082756078393539520693 1588039008382349394330065)
            ·
              refine ⟨1191029256286762045747549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1588039008382349394330065 1191029256286762045747549)
              ·
                refine ⟨446635971107535767155331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1191029256286762045747549 446635971107535767155331)
                ·
                  refine ⟨669953956661303650732997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446635971107535767155331 669953956661303650732997)
                  ·
                    refine ⟨125616366873994434512437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 669953956661303650732997 125616366873994434512437)
                    ·
                      rfl

theorem cell23_733911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_733911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733911 prefixEnd_733911 := by exact prefixLift 733911
  have htrace : WordTrace (prefixWord ++ tailWord_733911) baseStart_733911 baseEnd_733911 := by
    simpa [prefixWord, tailWord_733911, baseEnd_733911] using wordTrace_append hprefix tailTrace_733911
  have hstable : (prefixWord ++ tailWord_733911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733911).length < 2 ^ (prefixWord ++ tailWord_733911).sum := by decide
  have hdescent : baseEnd_733911 < baseStart_733911 := by decide
  rcases family_descends (prefixWord ++ tailWord_733911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733924 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 6]
def baseStart_733924 : Nat := 118140960795 + 733924 * 2 ^ 59
def prefixEnd_733924 : Nat := 4983230072969 + 3 ^ 40 * 733924 * 2
def baseEnd_733924 : Nat := 41872863985610194741639

theorem tailTrace_733924 : CollatzResearch.WordTrace tailWord_733924 prefixEnd_733924 41872863985610194741639 := by
  unfold tailWord_733924
  simp only [CollatzResearch.WordTrace]
  refine ⟨13384203696563083542572413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17845604928750778056763217 13384203696563083542572413)
  ·
    refine ⟨5019076386211156328464655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13384203696563083542572413 5019076386211156328464655)
    ·
      refine ⟨7528614579316734492696983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5019076386211156328464655 7528614579316734492696983)
      ·
        refine ⟨11292921868975101739045475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7528614579316734492696983 11292921868975101739045475)
        ·
          refine ⟨16939382803462652608568213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11292921868975101739045475 16939382803462652608568213)
          ·
            refine ⟨794033568912311841026635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16939382803462652608568213 794033568912311841026635)
            ·
              refine ⟨1191050353368467761539953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794033568912311841026635 1191050353368467761539953)
              ·
                refine ⟨893287765026350821154965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191050353368467761539953 893287765026350821154965)
                ·
                  refine ⟨41872863985610194741639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 893287765026350821154965 41872863985610194741639)
                  ·
                    rfl

theorem cell23_733924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_733924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733924 prefixEnd_733924 := by exact prefixLift 733924
  have htrace : WordTrace (prefixWord ++ tailWord_733924) baseStart_733924 baseEnd_733924 := by
    simpa [prefixWord, tailWord_733924, baseEnd_733924] using wordTrace_append hprefix tailTrace_733924
  have hstable : (prefixWord ++ tailWord_733924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733924).length < 2 ^ (prefixWord ++ tailWord_733924).sum := by decide
  have hdescent : baseEnd_733924 < baseStart_733924 := by decide
  rcases family_descends (prefixWord ++ tailWord_733924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733957 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_733957 : Nat := 118140960795 + 733957 * 2 ^ 59
def prefixEnd_733957 : Nat := 4983230072969 + 3 ^ 40 * 733957 * 2
def baseEnd_733957 : Nat := 376872720732090123562099

theorem tailTrace_733957 : CollatzResearch.WordTrace tailWord_733957 prefixEnd_733957 376872720732090123562099 := by
  unfold tailWord_733957
  simp only [CollatzResearch.WordTrace]
  refine ⟨26769611002006613721096125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17846407334671075814064083 26769611002006613721096125)
  ·
    refine ⟨10038604125752480145411047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26769611002006613721096125 10038604125752480145411047)
    ·
      refine ⟨15057906188628720218116571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10038604125752480145411047 15057906188628720218116571)
      ·
        refine ⟨22586859282943080327174857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15057906188628720218116571 22586859282943080327174857)
        ·
          refine ⟨16940144462207310245381143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22586859282943080327174857 16940144462207310245381143)
          ·
            refine ⟨25410216693310965368071715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16940144462207310245381143 25410216693310965368071715)
            ·
              refine ⟨38115325039966448052107573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25410216693310965368071715 38115325039966448052107573)
              ·
                refine ⟨3573311722496854504885085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38115325039966448052107573 3573311722496854504885085)
                ·
                  refine ⟨1339991895936320439331907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3573311722496854504885085 1339991895936320439331907)
                  ·
                    refine ⟨2009987843904480658997861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1339991895936320439331907 2009987843904480658997861)
                    ·
                      refine ⟨376872720732090123562099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2009987843904480658997861 376872720732090123562099)
                      ·
                        rfl

theorem cell23_733957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_733957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733957 prefixEnd_733957 := by exact prefixLift 733957
  have htrace : WordTrace (prefixWord ++ tailWord_733957) baseStart_733957 baseEnd_733957 := by
    simpa [prefixWord, tailWord_733957, baseEnd_733957] using wordTrace_append hprefix tailTrace_733957
  have hstable : (prefixWord ++ tailWord_733957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733957).length < 2 ^ (prefixWord ++ tailWord_733957).sum := by decide
  have hdescent : baseEnd_733957 < baseStart_733957 := by decide
  rcases family_descends (prefixWord ++ tailWord_733957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733967 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 6, 4]
def baseStart_733967 : Nat := 118140960795 + 733967 * 2 ^ 59
def prefixEnd_733967 : Nat := 4983230072969 + 3 ^ 40 * 733967 * 2
def baseEnd_733967 : Nat := 125625951846211694812351

theorem tailTrace_733967 : CollatzResearch.WordTrace tailWord_733967 prefixEnd_733967 125625951846211694812351 := by
  unfold tailWord_733967
  simp only [CollatzResearch.WordTrace]
  refine ⟨26769975731970385428960155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17846650487980256952640103 26769975731970385428960155)
  ·
    refine ⟨40154963597955578143440233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26769975731970385428960155 40154963597955578143440233)
    ·
      refine ⟨30116222698466683607580175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40154963597955578143440233 30116222698466683607580175)
      ·
        refine ⟨45174334047700025411370263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30116222698466683607580175 45174334047700025411370263)
        ·
          refine ⟨67761501071550038117055395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45174334047700025411370263 67761501071550038117055395)
          ·
            refine ⟨101642251607325057175583093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67761501071550038117055395 101642251607325057175583093)
            ·
              refine ⟨9528961088186724110210915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101642251607325057175583093 9528961088186724110210915)
              ·
                refine ⟨14293441632280086165316373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9528961088186724110210915 14293441632280086165316373)
                ·
                  refine ⟨670005076513129038999205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14293441632280086165316373 670005076513129038999205)
                  ·
                    refine ⟨125625951846211694812351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 670005076513129038999205 125625951846211694812351)
                    ·
                      rfl

theorem cell23_733967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 4].length) (baseStart_733967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733967 prefixEnd_733967 := by exact prefixLift 733967
  have htrace : WordTrace (prefixWord ++ tailWord_733967) baseStart_733967 baseEnd_733967 := by
    simpa [prefixWord, tailWord_733967, baseEnd_733967] using wordTrace_append hprefix tailTrace_733967
  have hstable : (prefixWord ++ tailWord_733967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733967).length < 2 ^ (prefixWord ++ tailWord_733967).sum := by decide
  have hdescent : baseEnd_733967 < baseStart_733967 := by decide
  rcases family_descends (prefixWord ++ tailWord_733967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733984 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 4, 4]
def baseStart_733984 : Nat := 118140960795 + 733984 * 2 ^ 59
def prefixEnd_733984 : Nat := 4983230072969 + 3 ^ 40 * 733984 * 2
def baseEnd_733984 : Nat := 125628861569920505974825

theorem tailTrace_733984 : CollatzResearch.WordTrace tailWord_733984 prefixEnd_733984 125628861569920505974825 := by
  unfold tailWord_733984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13385297886454398666164503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17847063848605864888219337 13385297886454398666164503)
  ·
    refine ⟨20077946829681597999246755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13385297886454398666164503 20077946829681597999246755)
    ·
      refine ⟨30116920244522396998870133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20077946829681597999246755 30116920244522396998870133)
      ·
        refine ⟨2823461272923974718644075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30116920244522396998870133 2823461272923974718644075)
        ·
          refine ⟨4235191909385962077966113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2823461272923974718644075 4235191909385962077966113)
          ·
            refine ⟨3176393932039471558474585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4235191909385962077966113 3176393932039471558474585)
            ·
              refine ⟨2382295449029603668855939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3176393932039471558474585 2382295449029603668855939)
              ·
                refine ⟨3573443173544405503283909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382295449029603668855939 3573443173544405503283909)
                ·
                  refine ⟨670020595039576031865733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3573443173544405503283909 670020595039576031865733)
                  ·
                    refine ⟨125628861569920505974825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 670020595039576031865733 125628861569920505974825)
                    ·
                      rfl

theorem cell23_733984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4, 4].length) (baseStart_733984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_733984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_733984 prefixEnd_733984 := by exact prefixLift 733984
  have htrace : WordTrace (prefixWord ++ tailWord_733984) baseStart_733984 baseEnd_733984 := by
    simpa [prefixWord, tailWord_733984, baseEnd_733984] using wordTrace_append hprefix tailTrace_733984
  have hstable : (prefixWord ++ tailWord_733984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733984).length < 2 ^ (prefixWord ++ tailWord_733984).sum := by decide
  have hdescent : baseEnd_733984 < baseStart_733984 := by decide
  rcases family_descends (prefixWord ++ tailWord_733984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734024 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_734024 : Nat := 118140960795 + 734024 * 2 ^ 59
def prefixEnd_734024 : Nat := 4983230072969 + 3 ^ 40 * 734024 * 2
def baseEnd_734024 : Nat := 376907123935941361424291

theorem tailTrace_734024 : CollatzResearch.WordTrace tailWord_734024 prefixEnd_734024 376907123935941361424291 := by
  unfold tailWord_734024
  simp only [CollatzResearch.WordTrace]
  refine ⟨13386027346381942081892563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17848036461842589442523417 13386027346381942081892563)
  ·
    refine ⟨20079041019572913122838845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13386027346381942081892563 20079041019572913122838845)
    ·
      refine ⟨7529640382339842421064567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20079041019572913122838845 7529640382339842421064567)
      ·
        refine ⟨11294460573509763631596851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7529640382339842421064567 11294460573509763631596851)
        ·
          refine ⟨16941690860264645447395277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11294460573509763631596851 16941690860264645447395277)
          ·
            refine ⟨6353134072599242042773229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16941690860264645447395277 6353134072599242042773229)
            ·
              refine ⟨2382425277224715766039961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6353134072599242042773229 2382425277224715766039961)
              ·
                refine ⟨1786818957918536824529971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382425277224715766039961 1786818957918536824529971)
                ·
                  refine ⟨2680228436877805236794957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786818957918536824529971 2680228436877805236794957)
                  ·
                    refine ⟨1005085663829176963798109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2680228436877805236794957 1005085663829176963798109)
                    ·
                      refine ⟨376907123935941361424291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1005085663829176963798109 376907123935941361424291)
                      ·
                        rfl

theorem cell23_734024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_734024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734024 prefixEnd_734024 := by exact prefixLift 734024
  have htrace : WordTrace (prefixWord ++ tailWord_734024) baseStart_734024 baseEnd_734024 := by
    simpa [prefixWord, tailWord_734024, baseEnd_734024] using wordTrace_append hprefix tailTrace_734024
  have hstable : (prefixWord ++ tailWord_734024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734024).length < 2 ^ (prefixWord ++ tailWord_734024).sum := by decide
  have hdescent : baseEnd_734024 < baseStart_734024 := by decide
  rcases family_descends (prefixWord ++ tailWord_734024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734028 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 1, 2, 3]
def baseStart_734028 : Nat := 118140960795 + 734028 * 2 ^ 59
def prefixEnd_734028 : Nat := 4983230072969 + 3 ^ 40 * 734028 * 2
def baseEnd_734028 : Nat := 376909177858559345774273

theorem tailTrace_734028 : CollatzResearch.WordTrace tailWord_734028 prefixEnd_734028 376909177858559345774273 := by
  unfold tailWord_734028
  simp only [CollatzResearch.WordTrace]
  refine ⟨13386100292374696423465369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17848133723166261897953825 13386100292374696423465369)
  ·
    refine ⟨10039575219281022317599027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13386100292374696423465369 10039575219281022317599027)
    ·
      refine ⟨15059362828921533476398541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10039575219281022317599027 15059362828921533476398541)
      ·
        refine ⟨5647261060845575053649453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15059362828921533476398541 5647261060845575053649453)
        ·
          refine ⟨2117722897817090645118545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5647261060845575053649453 2117722897817090645118545)
          ·
            refine ⟨1588292173362817983838909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2117722897817090645118545 1588292173362817983838909)
            ·
              refine ⟨595609565011056743939591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1588292173362817983838909 595609565011056743939591)
              ·
                refine ⟨893414347516585115909387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595609565011056743939591 893414347516585115909387)
                ·
                  refine ⟨1340121521274877673864081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893414347516585115909387 1340121521274877673864081)
                  ·
                    refine ⟨1005091140956158255398061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1340121521274877673864081 1005091140956158255398061)
                    ·
                      refine ⟨376909177858559345774273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1005091140956158255398061 376909177858559345774273)
                      ·
                        rfl

theorem cell23_734028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_734028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734028 prefixEnd_734028 := by exact prefixLift 734028
  have htrace : WordTrace (prefixWord ++ tailWord_734028) baseStart_734028 baseEnd_734028 := by
    simpa [prefixWord, tailWord_734028, baseEnd_734028] using wordTrace_append hprefix tailTrace_734028
  have hstable : (prefixWord ++ tailWord_734028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734028).length < 2 ^ (prefixWord ++ tailWord_734028).sum := by decide
  have hdescent : baseEnd_734028 < baseStart_734028 := by decide
  rcases family_descends (prefixWord ++ tailWord_734028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734041 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 2, 1, 3]
def baseStart_734041 : Nat := 118140960795 + 734041 * 2 ^ 59
def prefixEnd_734041 : Nat := 4983230072969 + 3 ^ 40 * 734041 * 2
def baseEnd_734041 : Nat := 376915853107067794911713

theorem tailTrace_734041 : CollatzResearch.WordTrace tailWord_734041 prefixEnd_734041 376915853107067794911713 := by
  unfold tailWord_734041
  simp only [CollatzResearch.WordTrace]
  refine ⟨26772674733702296067153977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17848449822468197378102651 26772674733702296067153977)
  ·
    refine ⟨20079506050276722050365483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26772674733702296067153977 20079506050276722050365483)
    ·
      refine ⟨30119259075415083075548225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20079506050276722050365483 30119259075415083075548225)
      ·
        refine ⟨22589444306561312306661169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30119259075415083075548225 22589444306561312306661169)
        ·
          refine ⟨16942083229920984229995877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22589444306561312306661169 16942083229920984229995877)
          ·
            refine ⟨3176640605610184543124227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16942083229920984229995877 3176640605610184543124227)
            ·
              refine ⟨4764960908415276814686341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176640605610184543124227 4764960908415276814686341)
              ·
                refine ⟨893430170327864402753689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4764960908415276814686341 893430170327864402753689)
                ·
                  refine ⟨670072627745898302065267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 893430170327864402753689 670072627745898302065267)
                  ·
                    refine ⟨1005108941618847453097901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 670072627745898302065267 1005108941618847453097901)
                    ·
                      refine ⟨376915853107067794911713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1005108941618847453097901 376915853107067794911713)
                      ·
                        rfl

theorem cell23_734041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_734041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734041 prefixEnd_734041 := by exact prefixLift 734041
  have htrace : WordTrace (prefixWord ++ tailWord_734041) baseStart_734041 baseEnd_734041 := by
    simpa [prefixWord, tailWord_734041, baseEnd_734041] using wordTrace_append hprefix tailTrace_734041
  have hstable : (prefixWord ++ tailWord_734041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734041).length < 2 ^ (prefixWord ++ tailWord_734041).sum := by decide
  have hdescent : baseEnd_734041 < baseStart_734041 := by decide
  rcases family_descends (prefixWord ++ tailWord_734041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734042 : List Nat := [3, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2]
def baseStart_734042 : Nat := 118140960795 + 734042 * 2 ^ 59
def prefixEnd_734042 : Nat := 4983230072969 + 3 ^ 40 * 734042 * 2
def baseEnd_734042 : Nat := 376916366587722290999209

theorem tailTrace_734042 : CollatzResearch.WordTrace tailWord_734042 prefixEnd_734042 376916366587722290999209 := by
  unfold tailWord_734042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6693177801674668309485095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17848474137799115491960253 6693177801674668309485095)
  ·
    refine ⟨10039766702512002464227643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6693177801674668309485095 10039766702512002464227643)
    ·
      refine ⟨15059650053768003696341465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10039766702512002464227643 15059650053768003696341465)
      ·
        refine ⟨11294737540326002772256099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15059650053768003696341465 11294737540326002772256099)
        ·
          refine ⟨16942106310489004158384149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11294737540326002772256099 16942106310489004158384149)
          ·
            refine ⟨794161233304172069924257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16942106310489004158384149 794161233304172069924257)
            ·
              refine ⟨595620924978129052443193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794161233304172069924257 595620924978129052443193)
              ·
                refine ⟨446715693733596789332395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595620924978129052443193 446715693733596789332395)
                ·
                  refine ⟨670073540600395183998593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446715693733596789332395 670073540600395183998593)
                  ·
                    refine ⟨502555155450296387998945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 670073540600395183998593 502555155450296387998945)
                    ·
                      refine ⟨376916366587722290999209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502555155450296387998945 376916366587722290999209)
                      ·
                        rfl

theorem cell23_734042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_734042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734042 prefixEnd_734042 := by exact prefixLift 734042
  have htrace : WordTrace (prefixWord ++ tailWord_734042) baseStart_734042 baseEnd_734042 := by
    simpa [prefixWord, tailWord_734042, baseEnd_734042] using wordTrace_append hprefix tailTrace_734042
  have hstable : (prefixWord ++ tailWord_734042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734042).length < 2 ^ (prefixWord ++ tailWord_734042).sum := by decide
  have hdescent : baseEnd_734042 < baseStart_734042 := by decide
  rcases family_descends (prefixWord ++ tailWord_734042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734044 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_734044 : Nat := 118140960795 + 734044 * 2 ^ 59
def prefixEnd_734044 : Nat := 4983230072969 + 3 ^ 40 * 734044 * 2
def baseEnd_734044 : Nat := 125639131183010427724733

theorem tailTrace_734044 : CollatzResearch.WordTrace tailWord_734044 prefixEnd_734044 125639131183010427724733 := by
  unfold tailWord_734044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13386392076345713789756593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17848522768460951719675457 13386392076345713789756593)
  ·
    refine ⟨10039794057259285342317445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13386392076345713789756593 10039794057259285342317445)
    ·
      refine ⟨1882461385736116001684521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10039794057259285342317445 1882461385736116001684521)
      ·
        refine ⟨1411846039302087001263391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1882461385736116001684521 1411846039302087001263391)
        ·
          refine ⟨2117769058953130501895087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411846039302087001263391 2117769058953130501895087)
          ·
            refine ⟨3176653588429695752842631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117769058953130501895087 3176653588429695752842631)
            ·
              refine ⟨4764980382644543629263947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176653588429695752842631 4764980382644543629263947)
              ·
                refine ⟨7147470573966815443895921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4764980382644543629263947 7147470573966815443895921)
                ·
                  refine ⟨5360602930475111582921941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7147470573966815443895921 5360602930475111582921941)
                  ·
                    refine ⟨125639131183010427724733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5360602930475111582921941 125639131183010427724733)
                    ·
                      rfl

theorem cell23_734044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_734044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734044 prefixEnd_734044 := by exact prefixLift 734044
  have htrace : WordTrace (prefixWord ++ tailWord_734044) baseStart_734044 baseEnd_734044 := by
    simpa [prefixWord, tailWord_734044, baseEnd_734044] using wordTrace_append hprefix tailTrace_734044
  have hstable : (prefixWord ++ tailWord_734044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734044).length < 2 ^ (prefixWord ++ tailWord_734044).sum := by decide
  have hdescent : baseEnd_734044 < baseStart_734044 := by decide
  rcases family_descends (prefixWord ++ tailWord_734044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734047 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 4]
def baseStart_734047 : Nat := 118140960795 + 734047 * 2 ^ 59
def prefixEnd_734047 : Nat := 4983230072969 + 3 ^ 40 * 734047 * 2
def baseEnd_734047 : Nat := 376918933990994771436685

theorem tailTrace_734047 : CollatzResearch.WordTrace tailWord_734047 prefixEnd_734047 376918933990994771436685 := by
  unfold tailWord_734047
  simp only [CollatzResearch.WordTrace]
  refine ⟨26772893571680559091872395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17848595714453706061248263 26772893571680559091872395)
  ·
    refine ⟨40159340357520838637808593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26772893571680559091872395 40159340357520838637808593)
    ·
      refine ⟨30119505268140628978356445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40159340357520838637808593 30119505268140628978356445)
      ·
        refine ⟨11294814475552735866883667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30119505268140628978356445 11294814475552735866883667)
        ·
          refine ⟨16942221713329103800325501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11294814475552735866883667 16942221713329103800325501)
          ·
            refine ⟨6353333142498413925122063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16942221713329103800325501 6353333142498413925122063)
            ·
              refine ⟨9529999713747620887683095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6353333142498413925122063 9529999713747620887683095)
              ·
                refine ⟨14294999570621431331524643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9529999713747620887683095 14294999570621431331524643)
                ·
                  refine ⟨21442499355932146997286965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14294999570621431331524643 21442499355932146997286965)
                  ·
                    refine ⟨2010234314618638780995653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21442499355932146997286965 2010234314618638780995653)
                    ·
                      refine ⟨376918933990994771436685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2010234314618638780995653 376918933990994771436685)
                      ·
                        rfl

theorem cell23_734047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_734047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734047 prefixEnd_734047 := by exact prefixLift 734047
  have htrace : WordTrace (prefixWord ++ tailWord_734047) baseStart_734047 baseEnd_734047 := by
    simpa [prefixWord, tailWord_734047, baseEnd_734047] using wordTrace_append hprefix tailTrace_734047
  have hstable : (prefixWord ++ tailWord_734047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734047).length < 2 ^ (prefixWord ++ tailWord_734047).sum := by decide
  have hdescent : baseEnd_734047 < baseStart_734047 := by decide
  rcases family_descends (prefixWord ++ tailWord_734047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734051 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 3, 3, 2]
def baseStart_734051 : Nat := 118140960795 + 734051 * 2 ^ 59
def prefixEnd_734051 : Nat := 4983230072969 + 3 ^ 40 * 734051 * 2
def baseEnd_734051 : Nat := 376920987913612755786667

theorem tailTrace_734051 : CollatzResearch.WordTrace tailWord_734051 prefixEnd_734051 376920987913612755786667 := by
  unfold tailWord_734051
  simp only [CollatzResearch.WordTrace]
  refine ⟨26773039463666067775018007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17848692975777378516678671 26773039463666067775018007)
  ·
    refine ⟨40159559195499101662527011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26773039463666067775018007 40159559195499101662527011)
    ·
      refine ⟨60239338793248652493790517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40159559195499101662527011 60239338793248652493790517)
      ·
        refine ⟨5647438011867061171292861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60239338793248652493790517 5647438011867061171292861)
        ·
          refine ⟨2117789254450147939234823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5647438011867061171292861 2117789254450147939234823)
          ·
            refine ⟨3176683881675221908852235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117789254450147939234823 3176683881675221908852235)
            ·
              refine ⟨4765025822512832863278353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176683881675221908852235 4765025822512832863278353)
              ·
                refine ⟨3573769366884624647458765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4765025822512832863278353 3573769366884624647458765)
                ·
                  refine ⟨1340163512581734242797037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3573769366884624647458765 1340163512581734242797037)
                  ·
                    refine ⟨502561317218150341048889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340163512581734242797037 502561317218150341048889)
                    ·
                      refine ⟨376920987913612755786667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 502561317218150341048889 376920987913612755786667)
                      ·
                        rfl

theorem cell23_734051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_734051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_734051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_734051 prefixEnd_734051 := by exact prefixLift 734051
  have htrace : WordTrace (prefixWord ++ tailWord_734051) baseStart_734051 baseEnd_734051 := by
    simpa [prefixWord, tailWord_734051, baseEnd_734051] using wordTrace_append hprefix tailTrace_734051
  have hstable : (prefixWord ++ tailWord_734051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734051).length < 2 ^ (prefixWord ++ tailWord_734051).sum := by decide
  have hdescent : baseEnd_734051 < baseStart_734051 := by decide
  rcases family_descends (prefixWord ++ tailWord_734051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
