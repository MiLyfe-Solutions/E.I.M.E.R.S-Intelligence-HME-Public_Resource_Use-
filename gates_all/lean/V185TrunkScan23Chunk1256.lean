import V185TrunkScan23Chunk1255

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7440541 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_7440541 : Nat := 118140960795 + 7440541 * 2 ^ 59
def prefixEnd_7440541 : Nat := 4983230072969 + 3 ^ 40 * 7440541 * 2
def baseEnd_7440541 : Nat := 3820573862485078582819081

theorem tailTrace_7440541 : CollatzResearch.WordTrace tailWord_7440541 prefixEnd_7440541 3820573862485078582819081 := by
  unfold tailWord_7440541
  simp only [CollatzResearch.WordTrace]
  refine ⟨271378824937198175078873477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180919216624798783385915651 271378824937198175078873477)
  ·
    refine ⟨50883529675724657827288777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271378824937198175078873477 50883529675724657827288777)
    ·
      refine ⟨38162647256793493370466583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50883529675724657827288777 38162647256793493370466583)
      ·
        refine ⟨57243970885190240055699875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38162647256793493370466583 57243970885190240055699875)
        ·
          refine ⟨85865956327785360083549813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57243970885190240055699875 85865956327785360083549813)
          ·
            refine ⟨8049933405729877507832795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85865956327785360083549813 8049933405729877507832795)
            ·
              refine ⟨12074900108594816261749193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8049933405729877507832795 12074900108594816261749193)
              ·
                refine ⟨9056175081446112196311895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12074900108594816261749193 9056175081446112196311895)
                ·
                  refine ⟨13584262622169168294467843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9056175081446112196311895 13584262622169168294467843)
                  ·
                    refine ⟨20376393933253752441701765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13584262622169168294467843 20376393933253752441701765)
                    ·
                      refine ⟨3820573862485078582819081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20376393933253752441701765 3820573862485078582819081)
                      ·
                        rfl

theorem cell23_7440541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_7440541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440541 prefixEnd_7440541 := by exact prefixLift 7440541
  have htrace : WordTrace (prefixWord ++ tailWord_7440541) baseStart_7440541 baseEnd_7440541 := by
    simpa [prefixWord, tailWord_7440541, baseEnd_7440541] using wordTrace_append hprefix tailTrace_7440541
  have hstable : (prefixWord ++ tailWord_7440541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440541).length < 2 ^ (prefixWord ++ tailWord_7440541).sum := by decide
  have hdescent : baseEnd_7440541 < baseStart_7440541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440544 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 3]
def baseStart_7440544 : Nat := 118140960795 + 7440544 * 2 ^ 59
def prefixEnd_7440544 : Nat := 4983230072969 + 3 ^ 40 * 7440544 * 2
def baseEnd_7440544 : Nat := 3820575402927042071081567

theorem tailTrace_7440544 : CollatzResearch.WordTrace tailWord_7440544 prefixEnd_7440544 3820575402927042071081567 := by
  unfold tailWord_7440544
  simp only [CollatzResearch.WordTrace]
  refine ⟨135689467178093653295616343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180919289570791537727488457 135689467178093653295616343)
  ·
    refine ⟨203534200767140479943424515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135689467178093653295616343 203534200767140479943424515)
    ·
      refine ⟨305301301150710719915136773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203534200767140479943424515 305301301150710719915136773)
      ·
        refine ⟨57243993965758259984088145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305301301150710719915136773 57243993965758259984088145)
        ·
          refine ⟨42932995474318694988066109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57243993965758259984088145 42932995474318694988066109)
          ·
            refine ⟨16099873302869510620524791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42932995474318694988066109 16099873302869510620524791)
            ·
              refine ⟨24149809954304265930787187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16099873302869510620524791 24149809954304265930787187)
              ·
                refine ⟨36224714931456398896180781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24149809954304265930787187 36224714931456398896180781)
                ·
                  refine ⟨13584268099296149586067793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36224714931456398896180781 13584268099296149586067793)
                  ·
                    refine ⟨10188201074472112189550845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13584268099296149586067793 10188201074472112189550845)
                    ·
                      refine ⟨3820575402927042071081567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10188201074472112189550845 3820575402927042071081567)
                      ·
                        rfl

theorem cell23_7440544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_7440544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440544 prefixEnd_7440544 := by exact prefixLift 7440544
  have htrace : WordTrace (prefixWord ++ tailWord_7440544) baseStart_7440544 baseEnd_7440544 := by
    simpa [prefixWord, tailWord_7440544, baseEnd_7440544] using wordTrace_append hprefix tailTrace_7440544
  have hstable : (prefixWord ++ tailWord_7440544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440544).length < 2 ^ (prefixWord ++ tailWord_7440544).sum := by decide
  have hdescent : baseEnd_7440544 < baseStart_7440544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440560 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 3, 9]
def baseStart_7440560 : Nat := 118140960795 + 7440560 * 2 ^ 59
def prefixEnd_7440560 : Nat := 4983230072969 + 3 ^ 40 * 7440560 * 2
def baseEnd_7440560 : Nat := 1273527872872504669493831

theorem tailTrace_7440560 : CollatzResearch.WordTrace tailWord_7440560 prefixEnd_7440560 1273527872872504669493831 := by
  unfold tailWord_7440560
  simp only [CollatzResearch.WordTrace]
  refine ⟨135689758962064670661907567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180919678616086227549210089 135689758962064670661907567)
  ·
    refine ⟨203534638443097005992861351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135689758962064670661907567 203534638443097005992861351)
    ·
      refine ⟨305301957664645508989292027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203534638443097005992861351 305301957664645508989292027)
      ·
        refine ⟨457952936496968263483938041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305301957664645508989292027 457952936496968263483938041)
        ·
          refine ⟨343464702372726197612953531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457952936496968263483938041 343464702372726197612953531)
          ·
            refine ⟨515197053559089296419430297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343464702372726197612953531 515197053559089296419430297)
            ·
              refine ⟨386397790169316972314572723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515197053559089296419430297 386397790169316972314572723)
              ·
                refine ⟨579596685253975458471859085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386397790169316972314572723 579596685253975458471859085)
                ·
                  refine ⟨217348756970240796926947157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579596685253975458471859085 217348756970240796926947157)
                  ·
                    refine ⟨1273527872872504669493831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 217348756970240796926947157 1273527872872504669493831)
                    ·
                      rfl

theorem cell23_7440560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_7440560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440560 prefixEnd_7440560 := by exact prefixLift 7440560
  have htrace : WordTrace (prefixWord ++ tailWord_7440560) baseStart_7440560 baseEnd_7440560 := by
    simpa [prefixWord, tailWord_7440560, baseEnd_7440560] using wordTrace_append hprefix tailTrace_7440560
  have hstable : (prefixWord ++ tailWord_7440560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440560).length < 2 ^ (prefixWord ++ tailWord_7440560).sum := by decide
  have hdescent : baseEnd_7440560 < baseStart_7440560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440561 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 5]
def baseStart_7440561 : Nat := 118140960795 + 7440561 * 2 ^ 59
def prefixEnd_7440561 : Nat := 4983230072969 + 3 ^ 40 * 7440561 * 2
def baseEnd_7440561 : Nat := 3820584132098168504568989

theorem tailTrace_7440561 : CollatzResearch.WordTrace tailWord_7440561 prefixEnd_7440561 3820584132098168504568989 := by
  unfold tailWord_7440561
  simp only [CollatzResearch.WordTrace]
  refine ⟨271379554397125718494601537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180919702931417145663067691 271379554397125718494601537)
  ·
    refine ⟨203534665797844288870951153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271379554397125718494601537 203534665797844288870951153)
    ·
      refine ⟨152650999348383216653213365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203534665797844288870951153 152650999348383216653213365)
      ·
        refine ⟨14311031188910926561238753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152650999348383216653213365 14311031188910926561238753)
        ·
          refine ⟨10733273391683194920929065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14311031188910926561238753 10733273391683194920929065)
          ·
            refine ⟨8049955043762396190696799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10733273391683194920929065 8049955043762396190696799)
            ·
              refine ⟨12074932565643594286045199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8049955043762396190696799 12074932565643594286045199)
              ·
                refine ⟨18112398848465391429067799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12074932565643594286045199 18112398848465391429067799)
                ·
                  refine ⟨27168598272698087143601699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18112398848465391429067799 27168598272698087143601699)
                  ·
                    refine ⟨40752897409047130715402549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27168598272698087143601699 40752897409047130715402549)
                    ·
                      refine ⟨3820584132098168504568989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40752897409047130715402549 3820584132098168504568989)
                      ·
                        rfl

theorem cell23_7440561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_7440561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440561 prefixEnd_7440561 := by exact prefixLift 7440561
  have htrace : WordTrace (prefixWord ++ tailWord_7440561) baseStart_7440561 baseEnd_7440561 := by
    simpa [prefixWord, tailWord_7440561, baseEnd_7440561] using wordTrace_append hprefix tailTrace_7440561
  have hstable : (prefixWord ++ tailWord_7440561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440561).length < 2 ^ (prefixWord ++ tailWord_7440561).sum := by decide
  have hdescent : baseEnd_7440561 < baseStart_7440561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440578 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_7440578 : Nat := 118140960795 + 7440578 * 2 ^ 59
def prefixEnd_7440578 : Nat := 4983230072969 + 3 ^ 40 * 7440578 * 2
def baseEnd_7440578 : Nat := 3820592861269294938056411

theorem tailTrace_7440578 : CollatzResearch.WordTrace tailWord_7440578 prefixEnd_7440578 3820592861269294938056411 := by
  unfold tailWord_7440578
  simp only [CollatzResearch.WordTrace]
  refine ⟨67845043609516032599492597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180920116292042753598646925 67845043609516032599492597)
  ·
    refine ⟨6360472838392128056202431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67845043609516032599492597 6360472838392128056202431)
    ·
      refine ⟨9540709257588192084303647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6360472838392128056202431 9540709257588192084303647)
      ·
        refine ⟨14311063886382288126455471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9540709257588192084303647 14311063886382288126455471)
        ·
          refine ⟨21466595829573432189683207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14311063886382288126455471 21466595829573432189683207)
          ·
            refine ⟨32199893744360148284524811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21466595829573432189683207 32199893744360148284524811)
            ·
              refine ⟨48299840616540222426787217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32199893744360148284524811 48299840616540222426787217)
              ·
                refine ⟨36224880462405166820090413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48299840616540222426787217 36224880462405166820090413)
                ·
                  refine ⟨13584330173401937557533905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36224880462405166820090413 13584330173401937557533905)
                  ·
                    refine ⟨10188247630051453168150429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13584330173401937557533905 10188247630051453168150429)
                    ·
                      refine ⟨3820592861269294938056411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10188247630051453168150429 3820592861269294938056411)
                      ·
                        rfl

theorem cell23_7440578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_7440578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440578 prefixEnd_7440578 := by exact prefixLift 7440578
  have htrace : WordTrace (prefixWord ++ tailWord_7440578) baseStart_7440578 baseEnd_7440578 := by
    simpa [prefixWord, tailWord_7440578, baseEnd_7440578] using wordTrace_append hprefix tailTrace_7440578
  have hstable : (prefixWord ++ tailWord_7440578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440578).length < 2 ^ (prefixWord ++ tailWord_7440578).sum := by decide
  have hdescent : baseEnd_7440578 < baseStart_7440578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440617 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 4, 4, 3]
def baseStart_7440617 : Nat := 118140960795 + 7440617 * 2 ^ 59
def prefixEnd_7440617 : Nat := 4983230072969 + 3 ^ 40 * 7440617 * 2
def baseEnd_7440617 : Nat := 3820612887014820285468731

theorem tailTrace_7440617 : CollatzResearch.WordTrace tailWord_7440617 prefixEnd_7440617 3820612887014820285468731 := by
  unfold tailWord_7440617
  simp only [CollatzResearch.WordTrace]
  refine ⟨271381596884922840058640105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180921064589948560039093403 271381596884922840058640105)
  ·
    refine ⟨203536197663692130043980079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271381596884922840058640105 203536197663692130043980079)
    ·
      refine ⟨305304296495538195065970119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203536197663692130043980079 305304296495538195065970119)
      ·
        refine ⟨457956444743307292598955179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305304296495538195065970119 457956444743307292598955179)
        ·
          refine ⟨686934667114960938898432769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457956444743307292598955179 686934667114960938898432769)
          ·
            refine ⟨515201000336220704173824577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686934667114960938898432769 515201000336220704173824577)
            ·
              refine ⟨386400750252165528130368433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515201000336220704173824577 386400750252165528130368433)
              ·
                refine ⟨289800562689124146097776325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386400750252165528130368433 289800562689124146097776325)
                ·
                  refine ⟨54337605504210777393333061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289800562689124146097776325 54337605504210777393333061)
                  ·
                    refine ⟨10188301032039520761249949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54337605504210777393333061 10188301032039520761249949)
                    ·
                      refine ⟨3820612887014820285468731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10188301032039520761249949 3820612887014820285468731)
                      ·
                        rfl

theorem cell23_7440617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4, 3].length) (baseStart_7440617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440617 prefixEnd_7440617 := by exact prefixLift 7440617
  have htrace : WordTrace (prefixWord ++ tailWord_7440617) baseStart_7440617 baseEnd_7440617 := by
    simpa [prefixWord, tailWord_7440617, baseEnd_7440617] using wordTrace_append hprefix tailTrace_7440617
  have hstable : (prefixWord ++ tailWord_7440617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440617).length < 2 ^ (prefixWord ++ tailWord_7440617).sum := by decide
  have hdescent : baseEnd_7440617 < baseStart_7440617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440627 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 4]
def baseStart_7440627 : Nat := 118140960795 + 7440627 * 2 ^ 59
def prefixEnd_7440627 : Nat := 4983230072969 + 3 ^ 40 * 7440627 * 2
def baseEnd_7440627 : Nat := 3820618021821365246343685

theorem tailTrace_7440627 : CollatzResearch.WordTrace tailWord_7440627 prefixEnd_7440627 3820618021821365246343685 := by
  unfold tailWord_7440627
  simp only [CollatzResearch.WordTrace]
  refine ⟨271381961614886611766504135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180921307743257741177669423 271381961614886611766504135)
  ·
    refine ⟨407072942422329917649756203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271381961614886611766504135 407072942422329917649756203)
    ·
      refine ⟨610609413633494876474634305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407072942422329917649756203 610609413633494876474634305)
      ·
        refine ⟨457957060225121157355975729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610609413633494876474634305 457957060225121157355975729)
        ·
          refine ⟨343467795168840868016981797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457957060225121157355975729 343467795168840868016981797)
          ·
            refine ⟨64400211594157662753184087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343467795168840868016981797 64400211594157662753184087)
            ·
              refine ⟨96600317391236494129776131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64400211594157662753184087 96600317391236494129776131)
              ·
                refine ⟨144900476086854741194664197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96600317391236494129776131 144900476086854741194664197)
                ·
                  refine ⟨27168839266285263973999537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144900476086854741194664197 27168839266285263973999537)
                  ·
                    refine ⟨20376629449713947980499653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27168839266285263973999537 20376629449713947980499653)
                    ·
                      refine ⟨3820618021821365246343685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20376629449713947980499653 3820618021821365246343685)
                      ·
                        rfl

theorem cell23_7440627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_7440627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440627 prefixEnd_7440627 := by exact prefixLift 7440627
  have htrace : WordTrace (prefixWord ++ tailWord_7440627) baseStart_7440627 baseEnd_7440627 := by
    simpa [prefixWord, tailWord_7440627, baseEnd_7440627] using wordTrace_append hprefix tailTrace_7440627
  have hstable : (prefixWord ++ tailWord_7440627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440627).length < 2 ^ (prefixWord ++ tailWord_7440627).sum := by decide
  have hdescent : baseEnd_7440627 < baseStart_7440627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440648 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 1, 4, 2]
def baseStart_7440648 : Nat := 118140960795 + 7440648 * 2 ^ 59
def prefixEnd_7440648 : Nat := 4983230072969 + 3 ^ 40 * 7440648 * 2
def baseEnd_7440648 : Nat := 3820628804915109664181089

theorem tailTrace_7440648 : CollatzResearch.WordTrace tailWord_7440648 prefixEnd_7440648 3820628804915109664181089 := by
  unfold tailWord_7440648
  simp only [CollatzResearch.WordTrace]
  refine ⟨135691363773905266176509299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180921818365207021568679065 135691363773905266176509299)
  ·
    refine ⟨203537045660857899264763949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135691363773905266176509299 203537045660857899264763949)
    ·
      refine ⟨76326392122821712224286481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203537045660857899264763949 76326392122821712224286481)
      ·
        refine ⟨57244794092116284168214861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76326392122821712224286481 57244794092116284168214861)
        ·
          refine ⟨21466797784543606563080573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57244794092116284168214861 21466797784543606563080573)
          ·
            refine ⟨8050049169203852461155215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21466797784543606563080573 8050049169203852461155215)
            ·
              refine ⟨12075073753805778691732823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8050049169203852461155215 12075073753805778691732823)
              ·
                refine ⟨18112610630708668037599235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12075073753805778691732823 18112610630708668037599235)
                ·
                  refine ⟨27168915946063002056398853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18112610630708668037599235 27168915946063002056398853)
                  ·
                    refine ⟨5094171739886812885574785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27168915946063002056398853 5094171739886812885574785)
                    ·
                      refine ⟨3820628804915109664181089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094171739886812885574785 3820628804915109664181089)
                      ·
                        rfl

theorem cell23_7440648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_7440648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440648 prefixEnd_7440648 := by exact prefixLift 7440648
  have htrace : WordTrace (prefixWord ++ tailWord_7440648) baseStart_7440648 baseEnd_7440648 := by
    simpa [prefixWord, tailWord_7440648, baseEnd_7440648] using wordTrace_append hprefix tailTrace_7440648
  have hstable : (prefixWord ++ tailWord_7440648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440648).length < 2 ^ (prefixWord ++ tailWord_7440648).sum := by decide
  have hdescent : baseEnd_7440648 < baseStart_7440648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440667 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 1, 7]
def baseStart_7440667 : Nat := 118140960795 + 7440667 * 2 ^ 59
def prefixEnd_7440667 : Nat := 4983230072969 + 3 ^ 40 * 7440667 * 2
def baseEnd_7440667 : Nat := 1273546187015848363281167

theorem tailTrace_7440667 : CollatzResearch.WordTrace tailWord_7440667 prefixEnd_7440667 1273546187015848363281167 := by
  unfold tailWord_7440667
  simp only [CollatzResearch.WordTrace]
  refine ⟨271383420534741698597960255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180922280356494465731973503 271383420534741698597960255)
  ·
    refine ⟨407075130802112547896940383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271383420534741698597960255 407075130802112547896940383)
    ·
      refine ⟨610612696203168821845410575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407075130802112547896940383 610612696203168821845410575)
      ·
        refine ⟨915919044304753232768115863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610612696203168821845410575 915919044304753232768115863)
        ·
          refine ⟨1373878566457129849152173795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915919044304753232768115863 1373878566457129849152173795)
          ·
            refine ⟨2060817849685694773728260693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373878566457129849152173795 2060817849685694773728260693)
            ·
              refine ⟨24150209176004235629628055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2060817849685694773728260693 24150209176004235629628055)
              ·
                refine ⟨36225313764006353444442083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24150209176004235629628055 36225313764006353444442083)
                ·
                  refine ⟨54337970646009530166663125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36225313764006353444442083 54337970646009530166663125)
                  ·
                    refine ⟨1273546187015848363281167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54337970646009530166663125 1273546187015848363281167)
                    ·
                      rfl

theorem cell23_7440667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 7].length) (baseStart_7440667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440667 prefixEnd_7440667 := by exact prefixLift 7440667
  have htrace : WordTrace (prefixWord ++ tailWord_7440667) baseStart_7440667 baseEnd_7440667 := by
    simpa [prefixWord, tailWord_7440667, baseEnd_7440667] using wordTrace_append hprefix tailTrace_7440667
  have hstable : (prefixWord ++ tailWord_7440667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440667).length < 2 ^ (prefixWord ++ tailWord_7440667).sum := by decide
  have hdescent : baseEnd_7440667 < baseStart_7440667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440671 : List Nat := [1, 1, 2, 4, 3, 1, 3, 3, 5]
def baseStart_7440671 : Nat := 118140960795 + 7440671 * 2 ^ 59
def prefixEnd_7440671 : Nat := 4983230072969 + 3 ^ 40 * 7440671 * 2
def baseEnd_7440671 : Nat := 424515623885573674910387

theorem tailTrace_7440671 : CollatzResearch.WordTrace tailWord_7440671 prefixEnd_7440671 424515623885573674910387 := by
  unfold tailWord_7440671
  simp only [CollatzResearch.WordTrace]
  refine ⟨271383566426727207281105867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180922377617818138187403911 271383566426727207281105867)
  ·
    refine ⟨407075349640090810921658801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271383566426727207281105867 407075349640090810921658801)
    ·
      refine ⟨305306512230068108191244101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407075349640090810921658801 305306512230068108191244101)
      ·
        refine ⟨57244971043137770285858269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305306512230068108191244101 57244971043137770285858269)
        ·
          refine ⟨21466864141176663857196851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57244971043137770285858269 21466864141176663857196851)
          ·
            refine ⟨32200296211764995785795277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21466864141176663857196851 32200296211764995785795277)
            ·
              refine ⟨12075111079411873419673229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32200296211764995785795277 12075111079411873419673229)
              ·
                refine ⟨4528166654779452532377461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12075111079411873419673229 4528166654779452532377461)
                ·
                  refine ⟨424515623885573674910387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4528166654779452532377461 424515623885573674910387)
                  ·
                    rfl

theorem cell23_7440671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 5].length) (baseStart_7440671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440671 prefixEnd_7440671 := by exact prefixLift 7440671
  have htrace : WordTrace (prefixWord ++ tailWord_7440671) baseStart_7440671 baseEnd_7440671 := by
    simpa [prefixWord, tailWord_7440671, baseEnd_7440671] using wordTrace_append hprefix tailTrace_7440671
  have hstable : (prefixWord ++ tailWord_7440671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440671).length < 2 ^ (prefixWord ++ tailWord_7440671).sum := by decide
  have hdescent : baseEnd_7440671 < baseStart_7440671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440721 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 4]
def baseStart_7440721 : Nat := 118140960795 + 7440721 * 2 ^ 59
def prefixEnd_7440721 : Nat := 4983230072969 + 3 ^ 40 * 7440721 * 2
def baseEnd_7440721 : Nat := 3820666289002887878568253

theorem tailTrace_7440721 : CollatzResearch.WordTrace tailWord_7440721 prefixEnd_7440721 3820666289002887878568253 := by
  unfold tailWord_7440721
  simp only [CollatzResearch.WordTrace]
  refine ⟨271385390076546065820426017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180923593384364043880284011 271385390076546065820426017)
  ·
    refine ⟨203539042557409549365319513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271385390076546065820426017 203539042557409549365319513)
    ·
      refine ⟨152654281918057162023989635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203539042557409549365319513 152654281918057162023989635)
      ·
        refine ⟨228981422877085743035984453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152654281918057162023989635 228981422877085743035984453)
        ·
          refine ⟨42934016789453576819247085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228981422877085743035984453 42934016789453576819247085)
          ·
            refine ⟨16100256296045091307217657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42934016789453576819247085 16100256296045091307217657)
            ·
              refine ⟨12075192222033818480413243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16100256296045091307217657 12075192222033818480413243)
              ·
                refine ⟨18112788333050727720619865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12075192222033818480413243 18112788333050727720619865)
                ·
                  refine ⟨13584591249788045790464899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18112788333050727720619865 13584591249788045790464899)
                  ·
                    refine ⟨20376886874682068685697349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13584591249788045790464899 20376886874682068685697349)
                    ·
                      refine ⟨3820666289002887878568253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20376886874682068685697349 3820666289002887878568253)
                      ·
                        rfl

theorem cell23_7440721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_7440721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440721 prefixEnd_7440721 := by exact prefixLift 7440721
  have htrace : WordTrace (prefixWord ++ tailWord_7440721) baseStart_7440721 baseEnd_7440721 := by
    simpa [prefixWord, tailWord_7440721, baseEnd_7440721] using wordTrace_append hprefix tailTrace_7440721
  have hstable : (prefixWord ++ tailWord_7440721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440721).length < 2 ^ (prefixWord ++ tailWord_7440721).sum := by decide
  have hdescent : baseEnd_7440721 < baseStart_7440721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440741 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 2, 2, 3]
def baseStart_7440741 : Nat := 118140960795 + 7440741 * 2 ^ 59
def prefixEnd_7440741 : Nat := 4983230072969 + 3 ^ 40 * 7440741 * 2
def baseEnd_7440741 : Nat := 3820676558615977800318161

theorem tailTrace_7440741 : CollatzResearch.WordTrace tailWord_7440741 prefixEnd_7440741 3820676558615977800318161 := by
  unfold tailWord_7440741
  simp only [CollatzResearch.WordTrace]
  refine ⟨271386119536473609236154077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180924079690982406157436051 271386119536473609236154077)
  ·
    refine ⟨101769794826177603463557779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271386119536473609236154077 101769794826177603463557779)
    ·
      refine ⟨152654692239266405195336669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101769794826177603463557779 152654692239266405195336669)
      ·
        refine ⟨57245509589724901948251251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152654692239266405195336669 57245509589724901948251251)
        ·
          refine ⟨85868264384587352922376877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57245509589724901948251251 85868264384587352922376877)
          ·
            refine ⟨32200599144220257345891329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85868264384587352922376877 32200599144220257345891329)
            ·
              refine ⟨24150449358165193009418497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32200599144220257345891329 24150449358165193009418497)
              ·
                refine ⟨18112837018623894757063873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24150449358165193009418497 18112837018623894757063873)
                ·
                  refine ⟨13584627763967921067797905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18112837018623894757063873 13584627763967921067797905)
                  ·
                    refine ⟨10188470822975940800848429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13584627763967921067797905 10188470822975940800848429)
                    ·
                      refine ⟨3820676558615977800318161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10188470822975940800848429 3820676558615977800318161)
                      ·
                        rfl

theorem cell23_7440741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_7440741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440741 prefixEnd_7440741 := by exact prefixLift 7440741
  have htrace : WordTrace (prefixWord ++ tailWord_7440741) baseStart_7440741 baseEnd_7440741 := by
    simpa [prefixWord, tailWord_7440741, baseEnd_7440741] using wordTrace_append hprefix tailTrace_7440741
  have hstable : (prefixWord ++ tailWord_7440741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440741).length < 2 ^ (prefixWord ++ tailWord_7440741).sum := by decide
  have hdescent : baseEnd_7440741 < baseStart_7440741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440747 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 8]
def baseStart_7440747 : Nat := 118140960795 + 7440747 * 2 ^ 59
def prefixEnd_7440747 : Nat := 4983230072969 + 3 ^ 40 * 7440747 * 2
def baseEnd_7440747 : Nat := 3820679639499904776843133

theorem tailTrace_7440747 : CollatzResearch.WordTrace tailWord_7440747 prefixEnd_7440747 3820679639499904776843133 := by
  unfold tailWord_7440747
  simp only [CollatzResearch.WordTrace]
  refine ⟨271386338374451872260872495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180924225582967914840581663 271386338374451872260872495)
  ·
    refine ⟨407079507561677808391308743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271386338374451872260872495 407079507561677808391308743)
    ·
      refine ⟨610619261342516712586963115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407079507561677808391308743 610619261342516712586963115)
      ·
        refine ⟨915928892013775068880444673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610619261342516712586963115 915928892013775068880444673)
        ·
          refine ⟨686946669010331301660333505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915928892013775068880444673 686946669010331301660333505)
          ·
            refine ⟨515210001757748476245250129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686946669010331301660333505 515210001757748476245250129)
            ·
              refine ⟨386407501318311357183937597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515210001757748476245250129 386407501318311357183937597)
              ·
                refine ⟨144902812994366758943976599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386407501318311357183937597 144902812994366758943976599)
                ·
                  refine ⟨217354219491550138415964899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144902812994366758943976599 217354219491550138415964899)
                  ·
                    refine ⟨326031329237325207623947349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217354219491550138415964899 326031329237325207623947349)
                    ·
                      refine ⟨3820679639499904776843133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 326031329237325207623947349 3820679639499904776843133)
                      ·
                        rfl

theorem cell23_7440747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_7440747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440747 prefixEnd_7440747 := by exact prefixLift 7440747
  have htrace : WordTrace (prefixWord ++ tailWord_7440747) baseStart_7440747 baseEnd_7440747 := by
    simpa [prefixWord, tailWord_7440747, baseEnd_7440747] using wordTrace_append hprefix tailTrace_7440747
  have hstable : (prefixWord ++ tailWord_7440747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440747).length < 2 ^ (prefixWord ++ tailWord_7440747).sum := by decide
  have hdescent : baseEnd_7440747 < baseStart_7440747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440804 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_7440804 : Nat := 118140960795 + 7440804 * 2 ^ 59
def prefixEnd_7440804 : Nat := 4983230072969 + 3 ^ 40 * 7440804 * 2
def baseEnd_7440804 : Nat := 1273569635965737017943457

theorem tailTrace_7440804 : CollatzResearch.WordTrace tailWord_7440804 prefixEnd_7440804 1273569635965737017943457 := by
  unfold tailWord_7440804
  simp only [CollatzResearch.WordTrace]
  refine ⟨135694208667622685497848733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180925611556830247330464977 135694208667622685497848733)
  ·
    refine ⟨50885328250358507061693275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135694208667622685497848733 50885328250358507061693275)
    ·
      refine ⟨76327992375537760592539913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50885328250358507061693275 76327992375537760592539913)
      ·
        refine ⟨57245994281653320444404935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76327992375537760592539913 57245994281653320444404935)
        ·
          refine ⟨85868991422479980666607403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57245994281653320444404935 85868991422479980666607403)
          ·
            refine ⟨128803487133719970999911105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85868991422479980666607403 128803487133719970999911105)
            ·
              refine ⟨96602615350289978249933329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128803487133719970999911105 96602615350289978249933329)
              ·
                refine ⟨72451961512717483687449997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96602615350289978249933329 72451961512717483687449997)
                ·
                  refine ⟨27169485567269056382793749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72451961512717483687449997 27169485567269056382793749)
                  ·
                    refine ⟨1273569635965737017943457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27169485567269056382793749 1273569635965737017943457)
                    ·
                      rfl

theorem cell23_7440804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_7440804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440804 prefixEnd_7440804 := by exact prefixLift 7440804
  have htrace : WordTrace (prefixWord ++ tailWord_7440804) baseStart_7440804 baseEnd_7440804 := by
    simpa [prefixWord, tailWord_7440804, baseEnd_7440804] using wordTrace_append hprefix tailTrace_7440804
  have hstable : (prefixWord ++ tailWord_7440804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440804).length < 2 ^ (prefixWord ++ tailWord_7440804).sum := by decide
  have hdescent : baseEnd_7440804 < baseStart_7440804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440828 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_7440828 : Nat := 118140960795 + 7440828 * 2 ^ 59
def prefixEnd_7440828 : Nat := 4983230072969 + 3 ^ 40 * 7440828 * 2
def baseEnd_7440828 : Nat := 3820721231432918959930261

theorem tailTrace_7440828 : CollatzResearch.WordTrace tailWord_7440828 prefixEnd_7440828 3820721231432918959930261 := by
  unfold tailWord_7440828
  simp only [CollatzResearch.WordTrace]
  refine ⟨135694646343579211547285569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180926195124772282063047425 135694646343579211547285569)
  ·
    refine ⟨101770984757684408660464177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135694646343579211547285569 101770984757684408660464177)
    ·
      refine ⟨76328238568263306495348133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101770984757684408660464177 76328238568263306495348133)
      ·
        refine ⟨14311544731549369967877775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76328238568263306495348133 14311544731549369967877775)
        ·
          refine ⟨21467317097324054951816663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14311544731549369967877775 21467317097324054951816663)
          ·
            refine ⟨32200975645986082427724995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21467317097324054951816663 32200975645986082427724995)
            ·
              refine ⟨48301463468979123641587493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32200975645986082427724995 48301463468979123641587493)
              ·
                refine ⟨9056524400433585682797655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48301463468979123641587493 9056524400433585682797655)
                ·
                  refine ⟨13584786600650378524196483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9056524400433585682797655 13584786600650378524196483)
                  ·
                    refine ⟨20377179900975567786294725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13584786600650378524196483 20377179900975567786294725)
                    ·
                      refine ⟨3820721231432918959930261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20377179900975567786294725 3820721231432918959930261)
                      ·
                        rfl

theorem cell23_7440828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_7440828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440828 prefixEnd_7440828 := by exact prefixLift 7440828
  have htrace : WordTrace (prefixWord ++ tailWord_7440828) baseStart_7440828 baseEnd_7440828 := by
    simpa [prefixWord, tailWord_7440828, baseEnd_7440828] using wordTrace_append hprefix tailTrace_7440828
  have hstable : (prefixWord ++ tailWord_7440828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440828).length < 2 ^ (prefixWord ++ tailWord_7440828).sum := by decide
  have hdescent : baseEnd_7440828 < baseStart_7440828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440864 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 2, 7]
def baseStart_7440864 : Nat := 118140960795 + 7440864 * 2 ^ 59
def prefixEnd_7440864 : Nat := 4983230072969 + 3 ^ 40 * 7440864 * 2
def baseEnd_7440864 : Nat := 1273579905578826939693365

theorem tailTrace_7440864 : CollatzResearch.WordTrace tailWord_7440864 prefixEnd_7440864 1273579905578826939693365 := by
  unfold tailWord_7440864
  simp only [CollatzResearch.WordTrace]
  refine ⟨135695302857514000621440823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180927070476685334161921097 135695302857514000621440823)
  ·
    refine ⟨203542954286271000932161235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135695302857514000621440823 203542954286271000932161235)
    ·
      refine ⟨305314431429406501398241853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203542954286271000932161235 305314431429406501398241853)
      ·
        refine ⟨114492911786027438024340695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305314431429406501398241853 114492911786027438024340695)
        ·
          refine ⟨171739367679041157036511043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114492911786027438024340695 171739367679041157036511043)
          ·
            refine ⟨257609051518561735554766565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171739367679041157036511043 257609051518561735554766565)
            ·
              refine ⟨48301697159730325416518731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257609051518561735554766565 48301697159730325416518731)
              ·
                refine ⟨72452545739595488124778097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48301697159730325416518731 72452545739595488124778097)
                ·
                  refine ⟨54339409304696616093583573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72452545739595488124778097 54339409304696616093583573)
                  ·
                    refine ⟨1273579905578826939693365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54339409304696616093583573 1273579905578826939693365)
                    ·
                      rfl

theorem cell23_7440864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_7440864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440864 prefixEnd_7440864 := by exact prefixLift 7440864
  have htrace : WordTrace (prefixWord ++ tailWord_7440864) baseStart_7440864 baseEnd_7440864 := by
    simpa [prefixWord, tailWord_7440864, baseEnd_7440864] using wordTrace_append hprefix tailTrace_7440864
  have hstable : (prefixWord ++ tailWord_7440864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440864).length < 2 ^ (prefixWord ++ tailWord_7440864).sum := by decide
  have hdescent : baseEnd_7440864 < baseStart_7440864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440882 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_7440882 : Nat := 118140960795 + 7440882 * 2 ^ 59
def prefixEnd_7440882 : Nat := 4983230072969 + 3 ^ 40 * 7440882 * 2
def baseEnd_7440882 : Nat := 3820748959388261748655013

theorem tailTrace_7440882 : CollatzResearch.WordTrace tailWord_7440882 prefixEnd_7440882 3820748959388261748655013 := by
  unfold tailWord_7440882
  simp only [CollatzResearch.WordTrace]
  refine ⟨67847815557240697579259225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180927508152641860211357933 67847815557240697579259225)
  ·
    refine ⟨50885861667930523184444419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67847815557240697579259225 50885861667930523184444419)
    ·
      refine ⟨76328792501895784776666629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50885861667930523184444419 76328792501895784776666629)
      ·
        refine ⟨14311648594105459645624993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76328792501895784776666629 14311648594105459645624993)
        ·
          refine ⟨10733736445579094734218745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14311648594105459645624993 10733736445579094734218745)
          ·
            refine ⟨8050302334184321050664059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10733736445579094734218745 8050302334184321050664059)
            ·
              refine ⟨12075453501276481575996089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8050302334184321050664059 12075453501276481575996089)
              ·
                refine ⟨9056590125957361181997067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12075453501276481575996089 9056590125957361181997067)
                ·
                  refine ⟨13584885188936041772995601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9056590125957361181997067 13584885188936041772995601)
                  ·
                    refine ⟨10188663891702031329746701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13584885188936041772995601 10188663891702031329746701)
                    ·
                      refine ⟨3820748959388261748655013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10188663891702031329746701 3820748959388261748655013)
                      ·
                        rfl

theorem cell23_7440882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_7440882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440882 prefixEnd_7440882 := by exact prefixLift 7440882
  have htrace : WordTrace (prefixWord ++ tailWord_7440882) baseStart_7440882 baseEnd_7440882 := by
    simpa [prefixWord, tailWord_7440882, baseEnd_7440882] using wordTrace_append hprefix tailTrace_7440882
  have hstable : (prefixWord ++ tailWord_7440882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440882).length < 2 ^ (prefixWord ++ tailWord_7440882).sum := by decide
  have hdescent : baseEnd_7440882 < baseStart_7440882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440888 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 3, 3, 2]
def baseStart_7440888 : Nat := 118140960795 + 7440888 * 2 ^ 59
def prefixEnd_7440888 : Nat := 4983230072969 + 3 ^ 40 * 7440888 * 2
def baseEnd_7440888 : Nat := 3820752040272188725179985

theorem tailTrace_7440888 : CollatzResearch.WordTrace tailWord_7440888 prefixEnd_7440888 3820752040272188725179985 := by
  unfold tailWord_7440888
  simp only [CollatzResearch.WordTrace]
  refine ⟨135695740533470526670877659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180927654044627368894503545 135695740533470526670877659)
  ·
    refine ⟨203543610800205790006316489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135695740533470526670877659 203543610800205790006316489)
    ·
      refine ⟨152657708100154342504737367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203543610800205790006316489 152657708100154342504737367)
      ·
        refine ⟨228986562150231513757106051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152657708100154342504737367 228986562150231513757106051)
        ·
          refine ⟨343479843225347270635659077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228986562150231513757106051 343479843225347270635659077)
          ·
            refine ⟨64402470604752613244186077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343479843225347270635659077 64402470604752613244186077)
            ·
              refine ⟨24150926476782229966569779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64402470604752613244186077 24150926476782229966569779)
              ·
                refine ⟨36226389715173344949854669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24150926476782229966569779 36226389715173344949854669)
                ·
                  refine ⟨13584896143190004356195501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36226389715173344949854669 13584896143190004356195501)
                  ·
                    refine ⟨5094336053696251633573313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13584896143190004356195501 5094336053696251633573313)
                    ·
                      refine ⟨3820752040272188725179985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094336053696251633573313 3820752040272188725179985)
                      ·
                        rfl

theorem cell23_7440888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 3, 2].length) (baseStart_7440888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440888 prefixEnd_7440888 := by exact prefixLift 7440888
  have htrace : WordTrace (prefixWord ++ tailWord_7440888) baseStart_7440888 baseEnd_7440888 := by
    simpa [prefixWord, tailWord_7440888, baseEnd_7440888] using wordTrace_append hprefix tailTrace_7440888
  have hstable : (prefixWord ++ tailWord_7440888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440888).length < 2 ^ (prefixWord ++ tailWord_7440888).sum := by decide
  have hdescent : baseEnd_7440888 < baseStart_7440888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440928 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 2, 6]
def baseStart_7440928 : Nat := 118140960795 + 7440928 * 2 ^ 59
def prefixEnd_7440928 : Nat := 4983230072969 + 3 ^ 40 * 7440928 * 2
def baseEnd_7440928 : Nat := 1273590859832789522893267

theorem tailTrace_7440928 : CollatzResearch.WordTrace tailWord_7440928 prefixEnd_7440928 1273590859832789522893267 := by
  unfold tailWord_7440928
  simp only [CollatzResearch.WordTrace]
  refine ⟨135696469993398070086605719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180928626657864093448807625 135696469993398070086605719)
  ·
    refine ⟨203544704990097105129908579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135696469993398070086605719 203544704990097105129908579)
    ·
      refine ⟨305317057485145657694862869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203544704990097105129908579 305317057485145657694862869)
      ·
        refine ⟨14311737069616202704446697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 305317057485145657694862869 14311737069616202704446697)
        ·
          refine ⟨10733802802212152028335023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14311737069616202704446697 10733802802212152028335023)
          ·
            refine ⟨16100704203318228042502535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10733802802212152028335023 16100704203318228042502535)
            ·
              refine ⟨24151056304977342063753803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16100704203318228042502535 24151056304977342063753803)
              ·
                refine ⟨36226584457466013095630705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24151056304977342063753803 36226584457466013095630705)
                ·
                  refine ⟨27169938343099509821723029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36226584457466013095630705 27169938343099509821723029)
                  ·
                    refine ⟨1273590859832789522893267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27169938343099509821723029 1273590859832789522893267)
                    ·
                      rfl

theorem cell23_7440928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 6].length) (baseStart_7440928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440928 prefixEnd_7440928 := by exact prefixLift 7440928
  have htrace : WordTrace (prefixWord ++ tailWord_7440928) baseStart_7440928 baseEnd_7440928 := by
    simpa [prefixWord, tailWord_7440928, baseEnd_7440928] using wordTrace_append hprefix tailTrace_7440928
  have hstable : (prefixWord ++ tailWord_7440928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440928).length < 2 ^ (prefixWord ++ tailWord_7440928).sum := by decide
  have hdescent : baseEnd_7440928 < baseStart_7440928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440931 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 4]
def baseStart_7440931 : Nat := 118140960795 + 7440931 * 2 ^ 59
def prefixEnd_7440931 : Nat := 4983230072969 + 3 ^ 40 * 7440931 * 2
def baseEnd_7440931 : Nat := 3820774119940332056942287

theorem tailTrace_7440931 : CollatzResearch.WordTrace tailWord_7440931 prefixEnd_7440931 3820774119940332056942287 := by
  unfold tailWord_7440931
  simp only [CollatzResearch.WordTrace]
  refine ⟨271393049405785271685570647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180928699603856847790380431 271393049405785271685570647)
  ·
    refine ⟨407089574108677907528355971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271393049405785271685570647 407089574108677907528355971)
    ·
      refine ⟨610634361163016861292533957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407089574108677907528355971 610634361163016861292533957)
      ·
        refine ⟨114493942718065661492350117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 610634361163016861292533957 114493942718065661492350117)
        ·
          refine ⟨21467614259637311529815647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114493942718065661492350117 21467614259637311529815647)
          ·
            refine ⟨32201421389455967294723471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21467614259637311529815647 32201421389455967294723471)
            ·
              refine ⟨48302132084183950942085207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32201421389455967294723471 48302132084183950942085207)
              ·
                refine ⟨72453198126275926413127811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48302132084183950942085207 72453198126275926413127811)
                ·
                  refine ⟨108679797189413889619691717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72453198126275926413127811 108679797189413889619691717)
                  ·
                    refine ⟨20377461973015104303692197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108679797189413889619691717 20377461973015104303692197)
                    ·
                      refine ⟨3820774119940332056942287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20377461973015104303692197 3820774119940332056942287)
                      ·
                        rfl

theorem cell23_7440931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_7440931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440931 prefixEnd_7440931 := by exact prefixLift 7440931
  have htrace : WordTrace (prefixWord ++ tailWord_7440931) baseStart_7440931 baseEnd_7440931 := by
    simpa [prefixWord, tailWord_7440931, baseEnd_7440931] using wordTrace_append hprefix tailTrace_7440931
  have hstable : (prefixWord ++ tailWord_7440931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440931).length < 2 ^ (prefixWord ++ tailWord_7440931).sum := by decide
  have hdescent : baseEnd_7440931 < baseStart_7440931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440951 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 3]
def baseStart_7440951 : Nat := 118140960795 + 7440951 * 2 ^ 59
def prefixEnd_7440951 : Nat := 4983230072969 + 3 ^ 40 * 7440951 * 2
def baseEnd_7440951 : Nat := 3820784389553421978692195

theorem tailTrace_7440951 : CollatzResearch.WordTrace tailWord_7440951 prefixEnd_7440951 3820784389553421978692195 := by
  unfold tailWord_7440951
  simp only [CollatzResearch.WordTrace]
  refine ⟨271393778865712815101298707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180929185910475210067532471 271393778865712815101298707)
  ·
    refine ⟨407090668298569222651948061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271393778865712815101298707 407090668298569222651948061)
    ·
      refine ⟨152659000611963458494480523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407090668298569222651948061 152659000611963458494480523)
      ·
        refine ⟨228988500917945187741720785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152659000611963458494480523 228988500917945187741720785)
        ·
          refine ⟨171741375688458890806290589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228988500917945187741720785 171741375688458890806290589)
          ·
            refine ⟨64403015883172084052358971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171741375688458890806290589 64403015883172084052358971)
            ·
              refine ⟨96604523824758126078538457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64403015883172084052358971 96604523824758126078538457)
              ·
                refine ⟨72453392868568594558903843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96604523824758126078538457 72453392868568594558903843)
                ·
                  refine ⟨108680089302852891838355765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72453392868568594558903843 108680089302852891838355765)
                  ·
                    refine ⟨10188758372142458609845853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108680089302852891838355765 10188758372142458609845853)
                    ·
                      refine ⟨3820784389553421978692195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10188758372142458609845853 3820784389553421978692195)
                      ·
                        rfl

theorem cell23_7440951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_7440951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440951 prefixEnd_7440951 := by exact prefixLift 7440951
  have htrace : WordTrace (prefixWord ++ tailWord_7440951) baseStart_7440951 baseEnd_7440951 := by
    simpa [prefixWord, tailWord_7440951, baseEnd_7440951] using wordTrace_append hprefix tailTrace_7440951
  have hstable : (prefixWord ++ tailWord_7440951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440951).length < 2 ^ (prefixWord ++ tailWord_7440951).sum := by decide
  have hdescent : baseEnd_7440951 < baseStart_7440951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440971 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 2, 5]
def baseStart_7440971 : Nat := 118140960795 + 7440971 * 2 ^ 59
def prefixEnd_7440971 : Nat := 4983230072969 + 3 ^ 40 * 7440971 * 2
def baseEnd_7440971 : Nat := 1273598219722170633480701

theorem tailTrace_7440971 : CollatzResearch.WordTrace tailWord_7440971 prefixEnd_7440971 1273598219722170633480701 := by
  unfold tailWord_7440971
  simp only [CollatzResearch.WordTrace]
  refine ⟨271394508325640358517026767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180929672217093572344684511 271394508325640358517026767)
  ·
    refine ⟨407091762488460537775540151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271394508325640358517026767 407091762488460537775540151)
    ·
      refine ⟨610637643732690806663310227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407091762488460537775540151 610637643732690806663310227)
      ·
        refine ⟨915956465599036209994965341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610637643732690806663310227 915956465599036209994965341)
        ·
          refine ⟨343483674599638578748112003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 915956465599036209994965341 343483674599638578748112003)
          ·
            refine ⟨515225511899457868122168005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343483674599638578748112003 515225511899457868122168005)
            ·
              refine ⟨96604783481148350272906501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 515225511899457868122168005 96604783481148350272906501)
              ·
                refine ⟨18113396902715315676169969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96604783481148350272906501 18113396902715315676169969)
                ·
                  refine ⟨13585047677036486757127477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18113396902715315676169969 13585047677036486757127477)
                  ·
                    refine ⟨1273598219722170633480701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13585047677036486757127477 1273598219722170633480701)
                    ·
                      rfl

theorem cell23_7440971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 5].length) (baseStart_7440971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440971 prefixEnd_7440971 := by exact prefixLift 7440971
  have htrace : WordTrace (prefixWord ++ tailWord_7440971) baseStart_7440971 baseEnd_7440971 := by
    simpa [prefixWord, tailWord_7440971, baseEnd_7440971] using wordTrace_append hprefix tailTrace_7440971
  have hstable : (prefixWord ++ tailWord_7440971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440971).length < 2 ^ (prefixWord ++ tailWord_7440971).sum := by decide
  have hdescent : baseEnd_7440971 < baseStart_7440971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440981 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_7440981 : Nat := 118140960795 + 7440981 * 2 ^ 59
def prefixEnd_7440981 : Nat := 4983230072969 + 3 ^ 40 * 7440981 * 2
def baseEnd_7440981 : Nat := 3820799793973056861317057

theorem tailTrace_7440981 : CollatzResearch.WordTrace tailWord_7440981 prefixEnd_7440981 3820799793973056861317057 := by
  unfold tailWord_7440981
  simp only [CollatzResearch.WordTrace]
  refine ⟨271394873055604130224890797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180929915370402753483260531 271394873055604130224890797)
  ·
    refine ⟨101773077395851548834334049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271394873055604130224890797 101773077395851548834334049)
    ·
      refine ⟨76329808046888661625750537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101773077395851548834334049 76329808046888661625750537)
      ·
        refine ⟨57247356035166496219312903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76329808046888661625750537 57247356035166496219312903)
        ·
          refine ⟨85871034052749744328969355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57247356035166496219312903 85871034052749744328969355)
          ·
            refine ⟨128806551079124616493454033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85871034052749744328969355 128806551079124616493454033)
            ·
              refine ⟨96604913309343462370090525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128806551079124616493454033 96604913309343462370090525)
              ·
                refine ⟨36226842491003798388783947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96604913309343462370090525 36226842491003798388783947)
                ·
                  refine ⟨54340263736505697583175921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36226842491003798388783947 54340263736505697583175921)
                  ·
                    refine ⟨40755197802379273187381941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54340263736505697583175921 40755197802379273187381941)
                    ·
                      refine ⟨3820799793973056861317057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40755197802379273187381941 3820799793973056861317057)
                      ·
                        rfl

theorem cell23_7440981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_7440981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440981 prefixEnd_7440981 := by exact prefixLift 7440981
  have htrace : WordTrace (prefixWord ++ tailWord_7440981) baseStart_7440981 baseEnd_7440981 := by
    simpa [prefixWord, tailWord_7440981, baseEnd_7440981] using wordTrace_append hprefix tailTrace_7440981
  have hstable : (prefixWord ++ tailWord_7440981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440981).length < 2 ^ (prefixWord ++ tailWord_7440981).sum := by decide
  have hdescent : baseEnd_7440981 < baseStart_7440981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441026 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 7]
def baseStart_7441026 : Nat := 118140960795 + 7441026 * 2 ^ 59
def prefixEnd_7441026 : Nat := 4983230072969 + 3 ^ 40 * 7441026 * 2
def baseEnd_7441026 : Nat := 424535877844723242806039

theorem tailTrace_7441026 : CollatzResearch.WordTrace tailWord_7441026 prefixEnd_7441026 424535877844723242806039 := by
  unfold tailWord_7441026
  simp only [CollatzResearch.WordTrace]
  refine ⟨67849128585110275727569733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180931009560294068606852621 67849128585110275727569733)
  ·
    refine ⟨12721711609708176698919325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67849128585110275727569733 12721711609708176698919325)
    ·
      refine ⟨4770641853640566262094747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12721711609708176698919325 4770641853640566262094747)
      ·
        refine ⟨7155962780460849393142121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770641853640566262094747 7155962780460849393142121)
        ·
          refine ⟨5366972085345637044856591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7155962780460849393142121 5366972085345637044856591)
          ·
            refine ⟨8050458128018455567284887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366972085345637044856591 8050458128018455567284887)
            ·
              refine ⟨12075687192027683350927331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8050458128018455567284887 12075687192027683350927331)
              ·
                refine ⟨18113530788041525026390997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12075687192027683350927331 18113530788041525026390997)
                ·
                  refine ⟨424535877844723242806039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18113530788041525026390997 424535877844723242806039)
                  ·
                    rfl

theorem cell23_7441026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_7441026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441026 prefixEnd_7441026 := by exact prefixLift 7441026
  have htrace : WordTrace (prefixWord ++ tailWord_7441026) baseStart_7441026 baseEnd_7441026 := by
    simpa [prefixWord, tailWord_7441026, baseEnd_7441026] using wordTrace_append hprefix tailTrace_7441026
  have hstable : (prefixWord ++ tailWord_7441026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441026).length < 2 ^ (prefixWord ++ tailWord_7441026).sum := by decide
  have hdescent : baseEnd_7441026 < baseStart_7441026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441031 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 8]
def baseStart_7441031 : Nat := 118140960795 + 7441031 * 2 ^ 59
def prefixEnd_7441031 : Nat := 4983230072969 + 3 ^ 40 * 7441031 * 2
def baseEnd_7441031 : Nat := 424536163111753518410203

theorem tailTrace_7441031 : CollatzResearch.WordTrace tailWord_7441031 prefixEnd_7441031 424536163111753518410203 := by
  unfold tailWord_7441031
  simp only [CollatzResearch.WordTrace]
  refine ⟨271396696705422988764210947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180931131136948659176140631 271396696705422988764210947)
  ·
    refine ⟨407095045058134483146316421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271396696705422988764210947 407095045058134483146316421)
    ·
      refine ⟨76330320948400215589934329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407095045058134483146316421 76330320948400215589934329)
      ·
        refine ⟨57247740711300161692450747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76330320948400215589934329 57247740711300161692450747)
        ·
          refine ⟨85871611066950242538676121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57247740711300161692450747 85871611066950242538676121)
          ·
            refine ⟨64403708300212681904007091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85871611066950242538676121 64403708300212681904007091)
            ·
              refine ⟨96605562450319022856010637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64403708300212681904007091 96605562450319022856010637)
              ·
                refine ⟨36227085918869633571003989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96605562450319022856010637 36227085918869633571003989)
                ·
                  refine ⟨424536163111753518410203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36227085918869633571003989 424536163111753518410203)
                  ·
                    rfl

theorem cell23_7441031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 8].length) (baseStart_7441031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441031 prefixEnd_7441031 := by exact prefixLift 7441031
  have htrace : WordTrace (prefixWord ++ tailWord_7441031) baseStart_7441031 baseEnd_7441031 := by
    simpa [prefixWord, tailWord_7441031, baseEnd_7441031] using wordTrace_append hprefix tailTrace_7441031
  have hstable : (prefixWord ++ tailWord_7441031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441031).length < 2 ^ (prefixWord ++ tailWord_7441031).sum := by decide
  have hdescent : baseEnd_7441031 < baseStart_7441031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441048 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 6]
def baseStart_7441048 : Nat := 118140960795 + 7441048 * 2 ^ 59
def prefixEnd_7441048 : Nat := 4983230072969 + 3 ^ 40 * 7441048 * 2
def baseEnd_7441048 : Nat := 424537133019656455464361

theorem tailTrace_7441048 : CollatzResearch.WordTrace tailWord_7441048 prefixEnd_7441048 424537133019656455464361 := by
  unfold tailWord_7441048
  simp only [CollatzResearch.WordTrace]
  refine ⟨135698658373180700333789899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180931544497574267111719865 135698658373180700333789899)
  ·
    refine ⟨203547987559771050500684849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135698658373180700333789899 203547987559771050500684849)
    ·
      refine ⟨152660990669828287875513637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203547987559771050500684849 152660990669828287875513637)
      ·
        refine ⟨28623935750592803976658807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152660990669828287875513637 28623935750592803976658807)
        ·
          refine ⟨42935903625889205964988211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28623935750592803976658807 42935903625889205964988211)
          ·
            refine ⟨64403855438833808947482317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42935903625889205964988211 64403855438833808947482317)
            ·
              refine ⟨24151445789562678355305869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64403855438833808947482317 24151445789562678355305869)
              ·
                refine ⟨9056792171086004383239701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24151445789562678355305869 9056792171086004383239701)
                ·
                  refine ⟨424537133019656455464361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9056792171086004383239701 424537133019656455464361)
                  ·
                    rfl

theorem cell23_7441048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 6].length) (baseStart_7441048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441048 prefixEnd_7441048 := by exact prefixLift 7441048
  have htrace : WordTrace (prefixWord ++ tailWord_7441048) baseStart_7441048 baseEnd_7441048 := by
    simpa [prefixWord, tailWord_7441048, baseEnd_7441048] using wordTrace_append hprefix tailTrace_7441048
  have hstable : (prefixWord ++ tailWord_7441048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441048).length < 2 ^ (prefixWord ++ tailWord_7441048).sum := by decide
  have hdescent : baseEnd_7441048 < baseStart_7441048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441109 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7441109 : Nat := 118140960795 + 7441109 * 2 ^ 59
def prefixEnd_7441109 : Nat := 4983230072969 + 3 ^ 40 * 7441109 * 2
def baseEnd_7441109 : Nat := 3820865519496832360516469

theorem tailTrace_7441109 : CollatzResearch.WordTrace tailWord_7441109 prefixEnd_7441109 3820865519496832360516469 := by
  unfold tailWord_7441109
  simp only [CollatzResearch.WordTrace]
  refine ⟨271399541599140408085550381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180933027732760272057033587 271399541599140408085550381)
  ·
    refine ⟨101774828099677653032081393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271399541599140408085550381 101774828099677653032081393)
    ·
      refine ⟨76331121074758239774061045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101774828099677653032081393 76331121074758239774061045)
      ·
        refine ⟨7156042600758584978818223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76331121074758239774061045 7156042600758584978818223)
        ·
          refine ⟨10734063901137877468227335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7156042600758584978818223 10734063901137877468227335)
          ·
            refine ⟨16101095851706816202341003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10734063901137877468227335 16101095851706816202341003)
            ·
              refine ⟨24151643777560224303511505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16101095851706816202341003 24151643777560224303511505)
              ·
                refine ⟨18113732833170168227633629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24151643777560224303511505 18113732833170168227633629)
                ·
                  refine ⟨6792649812438813085362611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18113732833170168227633629 6792649812438813085362611)
                  ·
                    refine ⟨10188974718658219628043917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6792649812438813085362611 10188974718658219628043917)
                    ·
                      refine ⟨3820865519496832360516469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10188974718658219628043917 3820865519496832360516469)
                      ·
                        rfl

theorem cell23_7441109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7441109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441109 prefixEnd_7441109 := by exact prefixLift 7441109
  have htrace : WordTrace (prefixWord ++ tailWord_7441109) baseStart_7441109 baseEnd_7441109 := by
    simpa [prefixWord, tailWord_7441109, baseEnd_7441109] using wordTrace_append hprefix tailTrace_7441109
  have hstable : (prefixWord ++ tailWord_7441109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441109).length < 2 ^ (prefixWord ++ tailWord_7441109).sum := by decide
  have hdescent : baseEnd_7441109 < baseStart_7441109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441138 : List Nat := [3, 2, 1, 3, 1, 3, 10]
def baseStart_7441138 : Nat := 118140960795 + 7441138 * 2 ^ 59
def prefixEnd_7441138 : Nat := 4983230072969 + 3 ^ 40 * 7441138 * 2
def baseEnd_7441138 : Nat := 47171363091800157371035

theorem tailTrace_7441138 : CollatzResearch.WordTrace tailWord_7441138 prefixEnd_7441138 47171363091800157371035 := by
  unfold tailWord_7441138
  simp only [CollatzResearch.WordTrace]
  refine ⟨67850149829008836509589017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180933732877356897358904045 67850149829008836509589017)
  ·
    refine ⟨50887612371756627382191763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67850149829008836509589017 50887612371756627382191763)
    ·
      refine ⟨76331418557634941073287645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50887612371756627382191763 76331418557634941073287645)
      ·
        refine ⟨28624281959113102902482867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76331418557634941073287645 28624281959113102902482867)
        ·
          refine ⟨42936422938669654353724301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28624281959113102902482867 42936422938669654353724301)
          ·
            refine ⟨16101158602001120382646613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42936422938669654353724301 16101158602001120382646613)
            ·
              refine ⟨47171363091800157371035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16101158602001120382646613 47171363091800157371035)
              ·
                rfl

theorem cell23_7441138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 10].length) (baseStart_7441138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441138 prefixEnd_7441138 := by exact prefixLift 7441138
  have htrace : WordTrace (prefixWord ++ tailWord_7441138) baseStart_7441138 baseEnd_7441138 := by
    simpa [prefixWord, tailWord_7441138, baseEnd_7441138] using wordTrace_append hprefix tailTrace_7441138
  have hstable : (prefixWord ++ tailWord_7441138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441138).length < 2 ^ (prefixWord ++ tailWord_7441138).sum := by decide
  have hdescent : baseEnd_7441138 < baseStart_7441138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441149 : List Nat := [1, 4, 1, 1, 1, 1, 3, 6, 1, 2, 2]
def baseStart_7441149 : Nat := 118140960795 + 7441149 * 2 ^ 59
def prefixEnd_7441149 : Nat := 4983230072969 + 3 ^ 40 * 7441149 * 2
def baseEnd_7441149 : Nat := 3820886058723012204016285

theorem tailTrace_7441149 : CollatzResearch.WordTrace tailWord_7441149 prefixEnd_7441149 3820886058723012204016285 := by
  unfold tailWord_7441149
  simp only [CollatzResearch.WordTrace]
  refine ⟨271401000518995494917006501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180934000345996996611337667 271401000518995494917006501)
  ·
    refine ⟨50887687597311655296938719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271401000518995494917006501 50887687597311655296938719)
    ·
      refine ⟨76331531395967482945408079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50887687597311655296938719 76331531395967482945408079)
      ·
        refine ⟨114497297093951224418112119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76331531395967482945408079 114497297093951224418112119)
        ·
          refine ⟨171745945640926836627168179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114497297093951224418112119 171745945640926836627168179)
          ·
            refine ⟨257618918461390254940752269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171745945640926836627168179 257618918461390254940752269)
            ·
              refine ⟨96607094423021345602782101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257618918461390254940752269 96607094423021345602782101)
              ·
                refine ⟨4528457551079125575130411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96607094423021345602782101 4528457551079125575130411)
                ·
                  refine ⟨6792686326618688362695617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528457551079125575130411 6792686326618688362695617)
                  ·
                    refine ⟨5094514744964016272021713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6792686326618688362695617 5094514744964016272021713)
                    ·
                      refine ⟨3820886058723012204016285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094514744964016272021713 3820886058723012204016285)
                      ·
                        rfl

theorem cell23_7441149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_7441149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441149 prefixEnd_7441149 := by exact prefixLift 7441149
  have htrace : WordTrace (prefixWord ++ tailWord_7441149) baseStart_7441149 baseEnd_7441149 := by
    simpa [prefixWord, tailWord_7441149, baseEnd_7441149] using wordTrace_append hprefix tailTrace_7441149
  have hstable : (prefixWord ++ tailWord_7441149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441149).length < 2 ^ (prefixWord ++ tailWord_7441149).sum := by decide
  have hdescent : baseEnd_7441149 < baseStart_7441149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441159 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 2, 4]
def baseStart_7441159 : Nat := 118140960795 + 7441159 * 2 ^ 59
def prefixEnd_7441159 : Nat := 4983230072969 + 3 ^ 40 * 7441159 * 2
def baseEnd_7441159 : Nat := 1273630397843185721630413

theorem tailTrace_7441159 : CollatzResearch.WordTrace tailWord_7441159 prefixEnd_7441159 1273630397843185721630413 := by
  unfold tailWord_7441159
  simp only [CollatzResearch.WordTrace]
  refine ⟨271401365248959266624870531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180934243499306177749913687 271401365248959266624870531)
  ·
    refine ⟨407102047873438899937305797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271401365248959266624870531 407102047873438899937305797)
    ·
      refine ⟨76331633976269793738244837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407102047873438899937305797 76331633976269793738244837)
      ·
        refine ⟨14312181370550586325920907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76331633976269793738244837 14312181370550586325920907)
        ·
          refine ⟨21468272055825879488881361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14312181370550586325920907 21468272055825879488881361)
          ·
            refine ⟨16101204041869409616661021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21468272055825879488881361 16101204041869409616661021)
            ·
              refine ⟨6037951515701028606247883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16101204041869409616661021 6037951515701028606247883)
              ·
                refine ⟨9056927273551542909371825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037951515701028606247883 9056927273551542909371825)
                ·
                  refine ⟨6792695455163657182028869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9056927273551542909371825 6792695455163657182028869)
                  ·
                    refine ⟨1273630397843185721630413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6792695455163657182028869 1273630397843185721630413)
                    ·
                      rfl

theorem cell23_7441159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_7441159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441159 prefixEnd_7441159 := by exact prefixLift 7441159
  have htrace : WordTrace (prefixWord ++ tailWord_7441159) baseStart_7441159 baseEnd_7441159 := by
    simpa [prefixWord, tailWord_7441159, baseEnd_7441159] using wordTrace_append hprefix tailTrace_7441159
  have hstable : (prefixWord ++ tailWord_7441159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441159).length < 2 ^ (prefixWord ++ tailWord_7441159).sum := by decide
  have hdescent : baseEnd_7441159 < baseStart_7441159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441178 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_7441178 : Nat := 118140960795 + 7441178 * 2 ^ 59
def prefixEnd_7441178 : Nat := 4983230072969 + 3 ^ 40 * 7441178 * 2
def baseEnd_7441178 : Nat := 3820900949661992590553651

theorem tailTrace_7441178 : CollatzResearch.WordTrace tailWord_7441178 prefixEnd_7441178 3820900949661992590553651 := by
  unfold tailWord_7441178
  simp only [CollatzResearch.WordTrace]
  refine ⟨67850514558972608217453047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180934705490593621913208125 67850514558972608217453047)
  ·
    refine ⟨101775771838458912326179571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67850514558972608217453047 101775771838458912326179571)
    ·
      refine ⟨152663657757688368489269357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101775771838458912326179571 152663657757688368489269357)
      ·
        refine ⟨57248871659133138183476009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152663657757688368489269357 57248871659133138183476009)
        ·
          refine ⟨42936653744349853637607007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57248871659133138183476009 42936653744349853637607007)
          ·
            refine ⟨64404980616524780456410511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42936653744349853637607007 64404980616524780456410511)
            ·
              refine ⟨96607470924787170684615767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64404980616524780456410511 96607470924787170684615767)
              ·
                refine ⟨144911206387180756026923651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96607470924787170684615767 144911206387180756026923651)
                ·
                  refine ⟨217366809580771134040385477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144911206387180756026923651 217366809580771134040385477)
                  ·
                    refine ⟨40756276796394587632572277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217366809580771134040385477 40756276796394587632572277)
                    ·
                      refine ⟨3820900949661992590553651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40756276796394587632572277 3820900949661992590553651)
                      ·
                        rfl

theorem cell23_7441178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_7441178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441178 prefixEnd_7441178 := by exact prefixLift 7441178
  have htrace : WordTrace (prefixWord ++ tailWord_7441178) baseStart_7441178 baseEnd_7441178 := by
    simpa [prefixWord, tailWord_7441178, baseEnd_7441178] using wordTrace_append hprefix tailTrace_7441178
  have hstable : (prefixWord ++ tailWord_7441178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441178).length < 2 ^ (prefixWord ++ tailWord_7441178).sum := by decide
  have hdescent : baseEnd_7441178 < baseStart_7441178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441208 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_7441208 : Nat := 118140960795 + 7441208 * 2 ^ 59
def prefixEnd_7441208 : Nat := 4983230072969 + 3 ^ 40 * 7441208 * 2
def baseEnd_7441208 : Nat := 3820916354081627473178513

theorem tailTrace_7441208 : CollatzResearch.WordTrace tailWord_7441208 prefixEnd_7441208 3820916354081627473178513 := by
  unfold tailWord_7441208
  simp only [CollatzResearch.WordTrace]
  refine ⟨135701576212890873996702139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180935434950521165328936185 135701576212890873996702139)
  ·
    refine ⟨203552364319336310995053209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135701576212890873996702139 203552364319336310995053209)
    ·
      refine ⟨152664273239502233246289907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203552364319336310995053209 152664273239502233246289907)
      ·
        refine ⟨228996409859253349869434861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152664273239502233246289907 228996409859253349869434861)
        ·
          refine ⟨85873653697220006201038073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228996409859253349869434861 85873653697220006201038073)
          ·
            refine ⟨64405240272915004650778555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85873653697220006201038073 64405240272915004650778555)
            ·
              refine ⟨96607860409372506976167833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64405240272915004650778555 96607860409372506976167833)
              ·
                refine ⟨72455895307029380232125875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96607860409372506976167833 72455895307029380232125875)
                ·
                  refine ⟨108683842960544070348188813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72455895307029380232125875 108683842960544070348188813)
                  ·
                    refine ⟨40756441110204026380570805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108683842960544070348188813 40756441110204026380570805)
                    ·
                      refine ⟨3820916354081627473178513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40756441110204026380570805 3820916354081627473178513)
                      ·
                        rfl

theorem cell23_7441208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_7441208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441208 prefixEnd_7441208 := by exact prefixLift 7441208
  have htrace : WordTrace (prefixWord ++ tailWord_7441208) baseStart_7441208 baseEnd_7441208 := by
    simpa [prefixWord, tailWord_7441208, baseEnd_7441208] using wordTrace_append hprefix tailTrace_7441208
  have hstable : (prefixWord ++ tailWord_7441208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441208).length < 2 ^ (prefixWord ++ tailWord_7441208).sum := by decide
  have hdescent : baseEnd_7441208 < baseStart_7441208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441256 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_7441256 : Nat := 118140960795 + 7441256 * 2 ^ 59
def prefixEnd_7441256 : Nat := 4983230072969 + 3 ^ 40 * 7441256 * 2
def baseEnd_7441256 : Nat := 3820941001153043285378293

theorem tailTrace_7441256 : CollatzResearch.WordTrace tailWord_7441256 prefixEnd_7441256 3820941001153043285378293 := by
  unfold tailWord_7441256
  simp only [CollatzResearch.WordTrace]
  refine ⟨135702451564803926095575811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180936602086405234794101081 135702451564803926095575811)
  ·
    refine ⟨203553677347205889143363717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135702451564803926095575811 203553677347205889143363717)
    ·
      refine ⟨38166314502601104214380697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203553677347205889143363717 38166314502601104214380697)
      ·
        refine ⟨28624735876950828160785523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38166314502601104214380697 28624735876950828160785523)
        ·
          refine ⟨42937103815426242241178285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28624735876950828160785523 42937103815426242241178285)
          ·
            refine ⟨16101413930784840840441857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42937103815426242241178285 16101413930784840840441857)
            ·
              refine ⟨12076060448088630630331393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16101413930784840840441857 12076060448088630630331393)
              ·
                refine ⟨9057045336066472972748545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12076060448088630630331393 9057045336066472972748545)
                ·
                  refine ⟨6792784002049854729561409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9057045336066472972748545 6792784002049854729561409)
                  ·
                    refine ⟨5094588001537391047171057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6792784002049854729561409 5094588001537391047171057)
                    ·
                      refine ⟨3820941001153043285378293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094588001537391047171057 3820941001153043285378293)
                      ·
                        rfl

theorem cell23_7441256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_7441256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441256 prefixEnd_7441256 := by exact prefixLift 7441256
  have htrace : WordTrace (prefixWord ++ tailWord_7441256) baseStart_7441256 baseEnd_7441256 := by
    simpa [prefixWord, tailWord_7441256, baseEnd_7441256] using wordTrace_append hprefix tailTrace_7441256
  have hstable : (prefixWord ++ tailWord_7441256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441256).length < 2 ^ (prefixWord ++ tailWord_7441256).sum := by decide
  have hdescent : baseEnd_7441256 < baseStart_7441256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441305 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 7, 4]
def baseStart_7441305 : Nat := 118140960795 + 7441305 * 2 ^ 59
def prefixEnd_7441305 : Nat := 4983230072969 + 3 ^ 40 * 7441305 * 2
def baseEnd_7441305 : Nat := 1273655387235037864555189

theorem tailTrace_7441305 : CollatzResearch.WordTrace tailWord_7441305 prefixEnd_7441305 1273655387235037864555189 := by
  unfold tailWord_7441305
  simp only [CollatzResearch.WordTrace]
  refine ⟨271406690306430333559685369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180937793537620222373123579 271406690306430333559685369)
  ·
    refine ⟨203555017729822750169764027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271406690306430333559685369 203555017729822750169764027)
    ·
      refine ⟨305332526594734125254646041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203555017729822750169764027 305332526594734125254646041)
      ·
        refine ⟨228999394946050593940984531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305332526594734125254646041 228999394946050593940984531)
        ·
          refine ⟨343499092419075890911476797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228999394946050593940984531 343499092419075890911476797)
          ·
            refine ⟨128812159657153459091803799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343499092419075890911476797 128812159657153459091803799)
            ·
              refine ⟨193218239485730188637705699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128812159657153459091803799 193218239485730188637705699)
              ·
                refine ⟨289827359228595282956558549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193218239485730188637705699 289827359228595282956558549)
                ·
                  refine ⟨6792828731920201944294341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 289827359228595282956558549 6792828731920201944294341)
                  ·
                    refine ⟨1273655387235037864555189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6792828731920201944294341 1273655387235037864555189)
                    ·
                      rfl

theorem cell23_7441305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 4].length) (baseStart_7441305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441305 prefixEnd_7441305 := by exact prefixLift 7441305
  have htrace : WordTrace (prefixWord ++ tailWord_7441305) baseStart_7441305 baseEnd_7441305 := by
    simpa [prefixWord, tailWord_7441305, baseEnd_7441305] using wordTrace_append hprefix tailTrace_7441305
  have hstable : (prefixWord ++ tailWord_7441305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441305).length < 2 ^ (prefixWord ++ tailWord_7441305).sum := by decide
  have hdescent : baseEnd_7441305 < baseStart_7441305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441312 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 2, 4, 2]
def baseStart_7441312 : Nat := 118140960795 + 7441312 * 2 ^ 59
def prefixEnd_7441312 : Nat := 4983230072969 + 3 ^ 40 * 7441312 * 2
def baseEnd_7441312 : Nat := 3820969756069695066278035

theorem tailTrace_7441312 : CollatzResearch.WordTrace tailWord_7441312 prefixEnd_7441312 3820969756069695066278035 := by
  unfold tailWord_7441312
  simp only [CollatzResearch.WordTrace]
  refine ⟨135703472808702486877595095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180937963744936649170126793 135703472808702486877595095)
  ·
    refine ⟨203555209213053730316392643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135703472808702486877595095 203555209213053730316392643)
    ·
      refine ⟨305332813819580595474588965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203555209213053730316392643 305332813819580595474588965)
      ·
        refine ⟨57249902591171361651485431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305332813819580595474588965 57249902591171361651485431)
        ·
          refine ⟨85874853886757042477228147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57249902591171361651485431 85874853886757042477228147)
          ·
            refine ⟨128812280830135563715842221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85874853886757042477228147 128812280830135563715842221)
            ·
              refine ⟨48304605311300836393440833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128812280830135563715842221 48304605311300836393440833)
              ·
                refine ⟨36228453983475627295080625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48304605311300836393440833 36228453983475627295080625)
                ·
                  refine ⟨27171340487606720471310469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36228453983475627295080625 27171340487606720471310469)
                  ·
                    refine ⟨5094626341426260088370713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27171340487606720471310469 5094626341426260088370713)
                    ·
                      refine ⟨3820969756069695066278035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094626341426260088370713 3820969756069695066278035)
                      ·
                        rfl

theorem cell23_7441312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_7441312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441312 prefixEnd_7441312 := by exact prefixLift 7441312
  have htrace : WordTrace (prefixWord ++ tailWord_7441312) baseStart_7441312 baseEnd_7441312 := by
    simpa [prefixWord, tailWord_7441312, baseEnd_7441312] using wordTrace_append hprefix tailTrace_7441312
  have hstable : (prefixWord ++ tailWord_7441312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441312).length < 2 ^ (prefixWord ++ tailWord_7441312).sum := by decide
  have hdescent : baseEnd_7441312 < baseStart_7441312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441335 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 6]
def baseStart_7441335 : Nat := 118140960795 + 7441335 * 2 ^ 59
def prefixEnd_7441335 : Nat := 4983230072969 + 3 ^ 40 * 7441335 * 2
def baseEnd_7441335 : Nat := 424553507347194275143381

theorem tailTrace_7441335 : CollatzResearch.WordTrace tailWord_7441335 prefixEnd_7441335 424553507347194275143381 := by
  unfold tailWord_7441335
  simp only [CollatzResearch.WordTrace]
  refine ⟨271407784496321648683277459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180938522997547765788851639 271407784496321648683277459)
  ·
    refine ⟨407111676744482473024916189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271407784496321648683277459 407111676744482473024916189)
    ·
      refine ⟨152666878779180927384343571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407111676744482473024916189 152666878779180927384343571)
      ·
        refine ⟨229000318168771391076515357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152666878779180927384343571 229000318168771391076515357)
        ·
          refine ⟨85875119313289271653693259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229000318168771391076515357 85875119313289271653693259)
          ·
            refine ⟨128812678969933907480539889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85875119313289271653693259 128812678969933907480539889)
            ·
              refine ⟨96609509227450430610404917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128812678969933907480539889 96609509227450430610404917)
              ·
                refine ⟨9057141490073477869725461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96609509227450430610404917 9057141490073477869725461)
                ·
                  refine ⟨424553507347194275143381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9057141490073477869725461 424553507347194275143381)
                  ·
                    rfl

theorem cell23_7441335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 6].length) (baseStart_7441335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441335 prefixEnd_7441335 := by exact prefixLift 7441335
  have htrace : WordTrace (prefixWord ++ tailWord_7441335) baseStart_7441335 baseEnd_7441335 := by
    simpa [prefixWord, tailWord_7441335, baseEnd_7441335] using wordTrace_append hprefix tailTrace_7441335
  have hstable : (prefixWord ++ tailWord_7441335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441335).length < 2 ^ (prefixWord ++ tailWord_7441335).sum := by decide
  have hdescent : baseEnd_7441335 < baseStart_7441335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441366 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_7441366 : Nat := 118140960795 + 7441366 * 2 ^ 59
def prefixEnd_7441366 : Nat := 4983230072969 + 3 ^ 40 * 7441366 * 2
def baseEnd_7441366 : Nat := 3820997484025037855002787

theorem tailTrace_7441366 : CollatzResearch.WordTrace tailWord_7441366 prefixEnd_7441366 3820997484025037855002787 := by
  unfold tailWord_7441366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16963057197450583811103497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180939276772806227318437301 16963057197450583811103497)
  ·
    refine ⟨12722292898087937858327623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16963057197450583811103497 12722292898087937858327623)
    ·
      refine ⟨19083439347131906787491435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12722292898087937858327623 19083439347131906787491435)
      ·
        refine ⟨28625159020697860181237153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19083439347131906787491435 28625159020697860181237153)
        ·
          refine ⟨21468869265523395135927865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28625159020697860181237153 21468869265523395135927865)
          ·
            refine ⟨16101651949142546351945899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21468869265523395135927865 16101651949142546351945899)
            ·
              refine ⟨24152477923713819527918849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16101651949142546351945899 24152477923713819527918849)
              ·
                refine ⟨18114358442785364645939137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24152477923713819527918849 18114358442785364645939137)
                ·
                  refine ⟨13585768832089023484454353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18114358442785364645939137 13585768832089023484454353)
                  ·
                    refine ⟨10189326624066767613340765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13585768832089023484454353 10189326624066767613340765)
                    ·
                      refine ⟨3820997484025037855002787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10189326624066767613340765 3820997484025037855002787)
                      ·
                        rfl

theorem cell23_7441366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_7441366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441366 prefixEnd_7441366 := by exact prefixLift 7441366
  have htrace : WordTrace (prefixWord ++ tailWord_7441366) baseStart_7441366 baseEnd_7441366 := by
    simpa [prefixWord, tailWord_7441366, baseEnd_7441366] using wordTrace_append hprefix tailTrace_7441366
  have hstable : (prefixWord ++ tailWord_7441366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441366).length < 2 ^ (prefixWord ++ tailWord_7441366).sum := by decide
  have hdescent : baseEnd_7441366 < baseStart_7441366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441373 : List Nat := [1, 4, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_7441373 : Nat := 118140960795 + 7441373 * 2 ^ 59
def prefixEnd_7441373 : Nat := 4983230072969 + 3 ^ 40 * 7441373 * 2
def baseEnd_7441373 : Nat := 1273667026129873109205085

theorem tailTrace_7441373 : CollatzResearch.WordTrace tailWord_7441373 prefixEnd_7441373 1273667026129873109205085 := by
  unfold tailWord_7441373
  simp only [CollatzResearch.WordTrace]
  refine ⟨271409170470183981173160773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180939446980122654115440515 271409170470183981173160773)
  ·
    refine ⟨50889219463159496469967645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271409170470183981173160773 50889219463159496469967645)
    ·
      refine ⟨19083457298684811176237867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50889219463159496469967645 19083457298684811176237867)
      ·
        refine ⟨28625185948027216764356801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19083457298684811176237867 28625185948027216764356801)
        ·
          refine ⟨21468889461020412573267601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28625185948027216764356801 21468889461020412573267601)
          ·
            refine ⟨16101667095765309429950701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21468889461020412573267601 16101667095765309429950701)
            ·
              refine ⟨6038125160911991036231513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16101667095765309429950701 6038125160911991036231513)
              ·
                refine ⟨4528593870683993277173635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6038125160911991036231513 4528593870683993277173635)
                ·
                  refine ⟨6792890806025989915760453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528593870683993277173635 6792890806025989915760453)
                  ·
                    refine ⟨1273667026129873109205085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6792890806025989915760453 1273667026129873109205085)
                    ·
                      rfl

theorem cell23_7441373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_7441373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441373 prefixEnd_7441373 := by exact prefixLift 7441373
  have htrace : WordTrace (prefixWord ++ tailWord_7441373) baseStart_7441373 baseEnd_7441373 := by
    simpa [prefixWord, tailWord_7441373, baseEnd_7441373] using wordTrace_append hprefix tailTrace_7441373
  have hstable : (prefixWord ++ tailWord_7441373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441373).length < 2 ^ (prefixWord ++ tailWord_7441373).sum := by decide
  have hdescent : baseEnd_7441373 < baseStart_7441373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441402 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2]
def baseStart_7441402 : Nat := 118140960795 + 7441402 * 2 ^ 59
def prefixEnd_7441402 : Nat := 4983230072969 + 3 ^ 40 * 7441402 * 2
def baseEnd_7441402 : Nat := 3821015969328599714152621

theorem tailTrace_7441402 : CollatzResearch.WordTrace tailWord_7441402 prefixEnd_7441402 3821015969328599714152621 := by
  unfold tailWord_7441402
  simp only [CollatzResearch.WordTrace]
  refine ⟨67852557046769729781491615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180940152124719279417310973 67852557046769729781491615)
  ·
    refine ⟨101778835570154594672237423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67852557046769729781491615 101778835570154594672237423)
    ·
      refine ⟨152668253355231892008356135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101778835570154594672237423 152668253355231892008356135)
      ·
        refine ⟨229002380032847838012534203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152668253355231892008356135 229002380032847838012534203)
        ·
          refine ⟨343503570049271757018801305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229002380032847838012534203 343503570049271757018801305)
          ·
            refine ⟨257627677536953817764100979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343503570049271757018801305 257627677536953817764100979)
            ·
              refine ⟨386441516305430726646151469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257627677536953817764100979 386441516305430726646151469)
              ·
                refine ⟨144915568614536522492306801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386441516305430726646151469 144915568614536522492306801)
                ·
                  refine ⟨108686676460902391869230101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144915568614536522492306801 108686676460902391869230101)
                  ·
                    refine ⟨5094687959104799618870161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108686676460902391869230101 5094687959104799618870161)
                    ·
                      refine ⟨3821015969328599714152621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094687959104799618870161 3821015969328599714152621)
                      ·
                        rfl

theorem cell23_7441402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2].length) (baseStart_7441402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441402 prefixEnd_7441402 := by exact prefixLift 7441402
  have htrace : WordTrace (prefixWord ++ tailWord_7441402) baseStart_7441402 baseEnd_7441402 := by
    simpa [prefixWord, tailWord_7441402, baseEnd_7441402] using wordTrace_append hprefix tailTrace_7441402
  have hstable : (prefixWord ++ tailWord_7441402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441402).length < 2 ^ (prefixWord ++ tailWord_7441402).sum := by decide
  have hdescent : baseEnd_7441402 < baseStart_7441402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441429 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 2, 4]
def baseStart_7441429 : Nat := 118140960795 + 7441429 * 2 ^ 59
def prefixEnd_7441429 : Nat := 4983230072969 + 3 ^ 40 * 7441429 * 2
def baseEnd_7441429 : Nat := 1273676611102090369504999

theorem tailTrace_7441429 : CollatzResearch.WordTrace tailWord_7441429 prefixEnd_7441429 1273676611102090369504999 := by
  unfold tailWord_7441429
  simp only [CollatzResearch.WordTrace]
  refine ⟨271411212957981102737199341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180940808638654068491466227 271411212957981102737199341)
  ·
    refine ⟨101779204859242913526449753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271411212957981102737199341 101779204859242913526449753)
    ·
      refine ⟨76334403644432185144837315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101779204859242913526449753 76334403644432185144837315)
      ·
        refine ⟨114501605466648277717255973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76334403644432185144837315 114501605466648277717255973)
        ·
          refine ⟨21469051024996552071985495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114501605466648277717255973 21469051024996552071985495)
          ·
            refine ⟨32203576537494828107978243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21469051024996552071985495 32203576537494828107978243)
            ·
              refine ⟨48305364806242242161967365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32203576537494828107978243 48305364806242242161967365)
              ·
                refine ⟨9057255901170420405368881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48305364806242242161967365 9057255901170420405368881)
                ·
                  refine ⟨6792941925877815304026661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9057255901170420405368881 6792941925877815304026661)
                  ·
                    refine ⟨1273676611102090369504999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6792941925877815304026661 1273676611102090369504999)
                    ·
                      rfl

theorem cell23_7441429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_7441429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441429 prefixEnd_7441429 := by exact prefixLift 7441429
  have htrace : WordTrace (prefixWord ++ tailWord_7441429) baseStart_7441429 baseEnd_7441429 := by
    simpa [prefixWord, tailWord_7441429, baseEnd_7441429] using wordTrace_append hprefix tailTrace_7441429
  have hstable : (prefixWord ++ tailWord_7441429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441429).length < 2 ^ (prefixWord ++ tailWord_7441429).sum := by decide
  have hdescent : baseEnd_7441429 < baseStart_7441429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441442 : List Nat := [3, 3, 1, 1, 1, 3, 3, 8]
def baseStart_7441442 : Nat := 118140960795 + 7441442 * 2 ^ 59
def prefixEnd_7441442 : Nat := 4983230072969 + 3 ^ 40 * 7441442 * 2
def baseEnd_7441442 : Nat := 141519870687214057690831

theorem tailTrace_7441442 : CollatzResearch.WordTrace tailWord_7441442 prefixEnd_7441442 141519870687214057690831 := by
  unfold tailWord_7441442
  simp only [CollatzResearch.WordTrace]
  refine ⟨67852921776733501489355645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180941124737956003971615053 67852921776733501489355645)
  ·
    refine ⟨25444845666275063058508367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67852921776733501489355645 25444845666275063058508367)
    ·
      refine ⟨38167268499412594587762551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25444845666275063058508367 38167268499412594587762551)
      ·
        refine ⟨57250902749118891881643827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38167268499412594587762551 57250902749118891881643827)
        ·
          refine ⟨85876354123678337822465741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57250902749118891881643827 85876354123678337822465741)
          ·
            refine ⟨32203632796379376683424653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85876354123678337822465741 32203632796379376683424653)
            ·
              refine ⟨12076362298642266256284245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32203632796379376683424653 12076362298642266256284245)
              ·
                refine ⟨141519870687214057690831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12076362298642266256284245 141519870687214057690831)
                ·
                  rfl

theorem cell23_7441442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 8].length) (baseStart_7441442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441442 prefixEnd_7441442 := by exact prefixLift 7441442
  have htrace : WordTrace (prefixWord ++ tailWord_7441442) baseStart_7441442 baseEnd_7441442 := by
    simpa [prefixWord, tailWord_7441442, baseEnd_7441442] using wordTrace_append hprefix tailTrace_7441442
  have hstable : (prefixWord ++ tailWord_7441442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441442).length < 2 ^ (prefixWord ++ tailWord_7441442).sum := by decide
  have hdescent : baseEnd_7441442 < baseStart_7441442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441469 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_7441469 : Nat := 118140960795 + 7441469 * 2 ^ 59
def prefixEnd_7441469 : Nat := 4983230072969 + 3 ^ 40 * 7441469 * 2
def baseEnd_7441469 : Nat := 3821050372532450952014813

theorem tailTrace_7441469 : CollatzResearch.WordTrace tailWord_7441469 prefixEnd_7441469 3821050372532450952014813 := by
  unfold tailWord_7441469
  simp only [CollatzResearch.WordTrace]
  refine ⟨271412671877836189568655461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180941781251890793045770307 271412671877836189568655461)
  ·
    refine ⟨50889875977094285544122899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271412671877836189568655461 50889875977094285544122899)
    ·
      refine ⟨76334813965641428316184349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50889875977094285544122899 76334813965641428316184349)
      ·
        refine ⟨28625555237115535618569131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76334813965641428316184349 28625555237115535618569131)
        ·
          refine ⟨42938332855673303427853697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28625555237115535618569131 42938332855673303427853697)
          ·
            refine ⟨32203749641754977570890273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42938332855673303427853697 32203749641754977570890273)
            ·
              refine ⟨24152812231316233178167705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32203749641754977570890273 24152812231316233178167705)
              ·
                refine ⟨18114609173487174883625779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24152812231316233178167705 18114609173487174883625779)
                ·
                  refine ⟨27171913760230762325438669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18114609173487174883625779 27171913760230762325438669)
                  ·
                    refine ⟨10189467660086535872039501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27171913760230762325438669 10189467660086535872039501)
                    ·
                      refine ⟨3821050372532450952014813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10189467660086535872039501 3821050372532450952014813)
                      ·
                        rfl

theorem cell23_7441469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_7441469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441469 prefixEnd_7441469 := by exact prefixLift 7441469
  have htrace : WordTrace (prefixWord ++ tailWord_7441469) baseStart_7441469 baseEnd_7441469 := by
    simpa [prefixWord, tailWord_7441469, baseEnd_7441469] using wordTrace_append hprefix tailTrace_7441469
  have hstable : (prefixWord ++ tailWord_7441469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441469).length < 2 ^ (prefixWord ++ tailWord_7441469).sum := by decide
  have hdescent : baseEnd_7441469 < baseStart_7441469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441470 : List Nat := [4, 2, 1, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_7441470 : Nat := 118140960795 + 7441470 * 2 ^ 59
def prefixEnd_7441470 : Nat := 4983230072969 + 3 ^ 40 * 7441470 * 2
def baseEnd_7441470 : Nat := 3821050886013105448102309

theorem tailTrace_7441470 : CollatzResearch.WordTrace tailWord_7441470 prefixEnd_7441470 3821050886013105448102309 := by
  unfold tailWord_7441470
  simp only [CollatzResearch.WordTrace]
  refine ⟨33926588543854070842430233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180941805567221711159627909 33926588543854070842430233)
  ·
    refine ⟨25444941407890553131822675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33926588543854070842430233 25444941407890553131822675)
    ·
      refine ⟨38167412111835829697734013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25444941407890553131822675 38167412111835829697734013)
      ·
        refine ⟨14312779541938436136650255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38167412111835829697734013 14312779541938436136650255)
        ·
          refine ⟨21469169312907654204975383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14312779541938436136650255 21469169312907654204975383)
          ·
            refine ⟨32203753969361481307463075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21469169312907654204975383 32203753969361481307463075)
            ·
              refine ⟨48305630954042221961194613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32203753969361481307463075 48305630954042221961194613)
              ·
                refine ⟨4528652901941458308861995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48305630954042221961194613 4528652901941458308861995)
                ·
                  refine ⟨6792979352912187463292993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528652901941458308861995 6792979352912187463292993)
                  ·
                    refine ⟨5094734514684140597469745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6792979352912187463292993 5094734514684140597469745)
                    ·
                      refine ⟨3821050886013105448102309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094734514684140597469745 3821050886013105448102309)
                      ·
                        rfl

theorem cell23_7441470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_7441470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441470 prefixEnd_7441470 := by exact prefixLift 7441470
  have htrace : WordTrace (prefixWord ++ tailWord_7441470) baseStart_7441470 baseEnd_7441470 := by
    simpa [prefixWord, tailWord_7441470, baseEnd_7441470] using wordTrace_append hprefix tailTrace_7441470
  have hstable : (prefixWord ++ tailWord_7441470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441470).length < 2 ^ (prefixWord ++ tailWord_7441470).sum := by decide
  have hdescent : baseEnd_7441470 < baseStart_7441470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441492 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_7441492 : Nat := 118140960795 + 7441492 * 2 ^ 59
def prefixEnd_7441492 : Nat := 4983230072969 + 3 ^ 40 * 7441492 * 2
def baseEnd_7441492 : Nat := 3821062182587504362027207

theorem tailTrace_7441492 : CollatzResearch.WordTrace tailWord_7441492 prefixEnd_7441492 3821062182587504362027207 := by
  unfold tailWord_7441492
  simp only [CollatzResearch.WordTrace]
  refine ⟨135706755378376432248371365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180942340504501909664495153 135706755378376432248371365)
  ·
    refine ⟨25445016633445581046569631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135706755378376432248371365 25445016633445581046569631)
    ·
      refine ⟨38167524950168371569854447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25445016633445581046569631 38167524950168371569854447)
      ·
        refine ⟨57251287425252557354781671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38167524950168371569854447 57251287425252557354781671)
        ·
          refine ⟨85876931137878836032172507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57251287425252557354781671 85876931137878836032172507)
          ·
            refine ⟨128815396706818254048258761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85876931137878836032172507 128815396706818254048258761)
            ·
              refine ⟨96611547530113690536194071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128815396706818254048258761 96611547530113690536194071)
              ·
                refine ⟨144917321295170535804291107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96611547530113690536194071 144917321295170535804291107)
                ·
                  refine ⟨217375981942755803706436661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144917321295170535804291107 217375981942755803706436661)
                  ·
                    refine ⟨20378998307133356597478437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 217375981942755803706436661 20378998307133356597478437)
                    ·
                      refine ⟨3821062182587504362027207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20378998307133356597478437 3821062182587504362027207)
                      ·
                        rfl

theorem cell23_7441492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_7441492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441492 prefixEnd_7441492 := by exact prefixLift 7441492
  have htrace : WordTrace (prefixWord ++ tailWord_7441492) baseStart_7441492 baseEnd_7441492 := by
    simpa [prefixWord, tailWord_7441492, baseEnd_7441492] using wordTrace_append hprefix tailTrace_7441492
  have hstable : (prefixWord ++ tailWord_7441492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441492).length < 2 ^ (prefixWord ++ tailWord_7441492).sum := by decide
  have hdescent : baseEnd_7441492 < baseStart_7441492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441526 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_7441526 : Nat := 118140960795 + 7441526 * 2 ^ 59
def prefixEnd_7441526 : Nat := 4983230072969 + 3 ^ 40 * 7441526 * 2
def baseEnd_7441526 : Nat := 3821079640929757229002051

theorem tailTrace_7441526 : CollatzResearch.WordTrace tailWord_7441526 prefixEnd_7441526 3821079640929757229002051 := by
  unfold tailWord_7441526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16963421927414355518967527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180943167225753125535653621 16963421927414355518967527)
  ·
    refine ⟨25445132891121533278451291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16963421927414355518967527 25445132891121533278451291)
    ·
      refine ⟨38167699336682299917676937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25445132891121533278451291 38167699336682299917676937)
      ·
        refine ⟨28625774502511724938257703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38167699336682299917676937 28625774502511724938257703)
        ·
          refine ⟨42938661753767587407386555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28625774502511724938257703 42938661753767587407386555)
          ·
            refine ⟨64407992630651381111079833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42938661753767587407386555 64407992630651381111079833)
            ·
              refine ⟨48305994472988535833309875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64407992630651381111079833 48305994472988535833309875)
              ·
                refine ⟨72458991709482803749964813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48305994472988535833309875 72458991709482803749964813)
                ·
                  refine ⟨27172121891056051406236805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72458991709482803749964813 27172121891056051406236805)
                  ·
                    refine ⟨5094772854573009638669401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27172121891056051406236805 5094772854573009638669401)
                    ·
                      refine ⟨3821079640929757229002051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094772854573009638669401 3821079640929757229002051)
                      ·
                        rfl

theorem cell23_7441526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_7441526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441526 prefixEnd_7441526 := by exact prefixLift 7441526
  have htrace : WordTrace (prefixWord ++ tailWord_7441526) baseStart_7441526 baseEnd_7441526 := by
    simpa [prefixWord, tailWord_7441526, baseEnd_7441526] using wordTrace_append hprefix tailTrace_7441526
  have hstable : (prefixWord ++ tailWord_7441526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441526).length < 2 ^ (prefixWord ++ tailWord_7441526).sum := by decide
  have hdescent : baseEnd_7441526 < baseStart_7441526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441529 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 5]
def baseStart_7441529 : Nat := 118140960795 + 7441529 * 2 ^ 59
def prefixEnd_7441529 : Nat := 4983230072969 + 3 ^ 40 * 7441529 * 2
def baseEnd_7441529 : Nat := 3821081181371720717264537

theorem tailTrace_7441529 : CollatzResearch.WordTrace tailWord_7441529 prefixEnd_7441529 3821081181371720717264537 := by
  unfold tailWord_7441529
  simp only [CollatzResearch.WordTrace]
  refine ⟨271414860257618819815839641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180943240171745879877226427 271414860257618819815839641)
  ·
    refine ⟨203561145193214114861879731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271414860257618819815839641 203561145193214114861879731)
    ·
      refine ⟨305341717789821172292819597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203561145193214114861879731 305341717789821172292819597)
      ·
        refine ⟨114503144171182939609807349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305341717789821172292819597 114503144171182939609807349)
        ·
          refine ⟨10734669766048400588419439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114503144171182939609807349 10734669766048400588419439)
          ·
            refine ⟨16102004649072600882629159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10734669766048400588419439 16102004649072600882629159)
            ·
              refine ⟨24153006973608901323943739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16102004649072600882629159 24153006973608901323943739)
              ·
                refine ⟨36229510460413351985915609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24153006973608901323943739 36229510460413351985915609)
                ·
                  refine ⟨27172132845310013989436707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36229510460413351985915609 27172132845310013989436707)
                  ·
                    refine ⟨40758199267965020984155061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27172132845310013989436707 40758199267965020984155061)
                    ·
                      refine ⟨3821081181371720717264537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40758199267965020984155061 3821081181371720717264537)
                      ·
                        rfl

theorem cell23_7441529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_7441529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441529 prefixEnd_7441529 := by exact prefixLift 7441529
  have htrace : WordTrace (prefixWord ++ tailWord_7441529) baseStart_7441529 baseEnd_7441529 := by
    simpa [prefixWord, tailWord_7441529, baseEnd_7441529] using wordTrace_append hprefix tailTrace_7441529
  have hstable : (prefixWord ++ tailWord_7441529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441529).length < 2 ^ (prefixWord ++ tailWord_7441529).sum := by decide
  have hdescent : baseEnd_7441529 < baseStart_7441529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441560 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 2, 2, 2]
def baseStart_7441560 : Nat := 118140960795 + 7441560 * 2 ^ 59
def prefixEnd_7441560 : Nat := 4983230072969 + 3 ^ 40 * 7441560 * 2
def baseEnd_7441560 : Nat := 3821097099272010095976895

theorem tailTrace_7441560 : CollatzResearch.WordTrace tailWord_7441560 prefixEnd_7441560 3821097099272010095976895 := by
  unfold tailWord_7441560
  simp only [CollatzResearch.WordTrace]
  refine ⟨135707995460253256055109067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180943993947004341406812089 135707995460253256055109067)
  ·
    refine ⟨203561993190379884082663601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135707995460253256055109067 203561993190379884082663601)
    ·
      refine ⟨152671494892784913061997701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203561993190379884082663601 152671494892784913061997701)
      ·
        refine ⟨28625905292397171199124569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152671494892784913061997701 28625905292397171199124569)
        ·
          refine ⟨21469428969297878399343427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28625905292397171199124569 21469428969297878399343427)
          ·
            refine ⟨32204143453946817599015141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21469428969297878399343427 32204143453946817599015141)
            ·
              refine ⟨6038276897615028299815339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32204143453946817599015141 6038276897615028299815339)
              ·
                refine ⟨9057415346422542449723009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6038276897615028299815339 9057415346422542449723009)
                ·
                  refine ⟨6793061509816906837292257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9057415346422542449723009 6793061509816906837292257)
                  ·
                    refine ⟨5094796132362680127969193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6793061509816906837292257 5094796132362680127969193)
                    ·
                      refine ⟨3821097099272010095976895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094796132362680127969193 3821097099272010095976895)
                      ·
                        rfl

theorem cell23_7441560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_7441560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441560 prefixEnd_7441560 := by exact prefixLift 7441560
  have htrace : WordTrace (prefixWord ++ tailWord_7441560) baseStart_7441560 baseEnd_7441560 := by
    simpa [prefixWord, tailWord_7441560, baseEnd_7441560] using wordTrace_append hprefix tailTrace_7441560
  have hstable : (prefixWord ++ tailWord_7441560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441560).length < 2 ^ (prefixWord ++ tailWord_7441560).sum := by decide
  have hdescent : baseEnd_7441560 < baseStart_7441560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441599 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 4]
def baseStart_7441599 : Nat := 118140960795 + 7441599 * 2 ^ 59
def prefixEnd_7441599 : Nat := 4983230072969 + 3 ^ 40 * 7441599 * 2
def baseEnd_7441599 : Nat := 3821117125017535443389215

theorem tailTrace_7441599 : CollatzResearch.WordTrace tailWord_7441599 prefixEnd_7441599 3821117125017535443389215 := by
  unfold tailWord_7441599
  simp only [CollatzResearch.WordTrace]
  refine ⟨271417413367365221770887851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180944942244910147847258567 271417413367365221770887851)
  ·
    refine ⟨407126120051047832656331777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271417413367365221770887851 407126120051047832656331777)
    ·
      refine ⟨305344590038285874492248833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407126120051047832656331777 305344590038285874492248833)
      ·
        refine ⟨229008442528714405869186625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305344590038285874492248833 229008442528714405869186625)
        ·
          refine ⟨171756331896535804401889969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229008442528714405869186625 171756331896535804401889969)
          ·
            refine ⟨128817248922401853301417477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171756331896535804401889969 128817248922401853301417477)
            ·
              refine ⟨24153234172950347494015777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128817248922401853301417477 24153234172950347494015777)
              ·
                refine ⟨18114925629712760620511833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24153234172950347494015777 18114925629712760620511833)
                ·
                  refine ⟨13586194222284570465383875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18114925629712760620511833 13586194222284570465383875)
                  ·
                    refine ⟨20379291333426855698075813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13586194222284570465383875 20379291333426855698075813)
                    ·
                      refine ⟨3821117125017535443389215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20379291333426855698075813 3821117125017535443389215)
                      ·
                        rfl

theorem cell23_7441599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_7441599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441599 prefixEnd_7441599 := by exact prefixLift 7441599
  have htrace : WordTrace (prefixWord ++ tailWord_7441599) baseStart_7441599 baseEnd_7441599 := by
    simpa [prefixWord, tailWord_7441599, baseEnd_7441599] using wordTrace_append hprefix tailTrace_7441599
  have hstable : (prefixWord ++ tailWord_7441599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441599).length < 2 ^ (prefixWord ++ tailWord_7441599).sum := by decide
  have hdescent : baseEnd_7441599 < baseStart_7441599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441600 : List Nat := [2, 1, 1, 2, 7, 1, 2, 2, 5]
def baseStart_7441600 : Nat := 118140960795 + 7441600 * 2 ^ 59
def prefixEnd_7441600 : Nat := 4983230072969 + 3 ^ 40 * 7441600 * 2
def baseEnd_7441600 : Nat := 424568626499798882164079

theorem tailTrace_7441600 : CollatzResearch.WordTrace tailWord_7441600 prefixEnd_7441600 424568626499798882164079 := by
  unfold tailWord_7441600
  simp only [CollatzResearch.WordTrace]
  refine ⟨135708724920180799470837127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180944966560241065961116169 135708724920180799470837127)
  ·
    refine ⟨203563087380271199206255691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135708724920180799470837127 203563087380271199206255691)
    ·
      refine ⟨305344631070406798809383537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203563087380271199206255691 305344631070406798809383537)
      ·
        refine ⟨229008473302805099107037653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305344631070406798809383537 229008473302805099107037653)
        ·
          refine ⟨5367386093034494510321195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 229008473302805099107037653 5367386093034494510321195)
          ·
            refine ⟨8051079139551741765481793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367386093034494510321195 8051079139551741765481793)
            ·
              refine ⟨6038309354663806324111345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8051079139551741765481793 6038309354663806324111345)
              ·
                refine ⟨4528732015997854743083509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6038309354663806324111345 4528732015997854743083509)
                ·
                  refine ⟨424568626499798882164079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4528732015997854743083509 424568626499798882164079)
                  ·
                    rfl

theorem cell23_7441600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 5].length) (baseStart_7441600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441600 prefixEnd_7441600 := by exact prefixLift 7441600
  have htrace : WordTrace (prefixWord ++ tailWord_7441600) baseStart_7441600 baseEnd_7441600 := by
    simpa [prefixWord, tailWord_7441600, baseEnd_7441600] using wordTrace_append hprefix tailTrace_7441600
  have hstable : (prefixWord ++ tailWord_7441600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441600).length < 2 ^ (prefixWord ++ tailWord_7441600).sum := by decide
  have hdescent : baseEnd_7441600 < baseStart_7441600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441636 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_7441636 : Nat := 118140960795 + 7441636 * 2 ^ 59
def prefixEnd_7441636 : Nat := 4983230072969 + 3 ^ 40 * 7441636 * 2
def baseEnd_7441636 : Nat := 3821136123801751798626545

theorem tailTrace_7441636 : CollatzResearch.WordTrace tailWord_7441636 prefixEnd_7441636 3821136123801751798626545 := by
  unfold tailWord_7441636
  simp only [CollatzResearch.WordTrace]
  refine ⟨135709381434115588544992381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180945841912154118059989841 135709381434115588544992381)
  ·
    refine ⟨50891018037793345704372143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135709381434115588544992381 50891018037793345704372143)
    ·
      refine ⟨76336527056690018556558215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50891018037793345704372143 76336527056690018556558215)
      ·
        refine ⟨114504790585035027834837323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76336527056690018556558215 114504790585035027834837323)
        ·
          refine ⟨171757185877552541752255985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114504790585035027834837323 171757185877552541752255985)
          ·
            refine ⟨128817889408164406314191989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171757185877552541752255985 128817889408164406314191989)
            ·
              refine ⟨12076677132015413091955499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128817889408164406314191989 12076677132015413091955499)
              ·
                refine ⟨18115015698023119637933249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12076677132015413091955499 18115015698023119637933249)
                ·
                  refine ⟨13586261773517339728449937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18115015698023119637933249 13586261773517339728449937)
                  ·
                    refine ⟨10189696330138004796337453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13586261773517339728449937 10189696330138004796337453)
                    ·
                      refine ⟨3821136123801751798626545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10189696330138004796337453 3821136123801751798626545)
                      ·
                        rfl

theorem cell23_7441636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_7441636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441636 prefixEnd_7441636 := by exact prefixLift 7441636
  have htrace : WordTrace (prefixWord ++ tailWord_7441636) baseStart_7441636 baseEnd_7441636 := by
    simpa [prefixWord, tailWord_7441636, baseEnd_7441636] using wordTrace_append hprefix tailTrace_7441636
  have hstable : (prefixWord ++ tailWord_7441636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441636).length < 2 ^ (prefixWord ++ tailWord_7441636).sum := by decide
  have hdescent : baseEnd_7441636 < baseStart_7441636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441643 : List Nat := [1, 1, 1, 1, 2, 7, 2, 3, 1, 4]
def baseStart_7441643 : Nat := 118140960795 + 7441643 * 2 ^ 59
def prefixEnd_7441643 : Nat := 4983230072969 + 3 ^ 40 * 7441643 * 2
def baseEnd_7441643 : Nat := 1273713239388777757079671

theorem tailTrace_7441643 : CollatzResearch.WordTrace tailWord_7441643 prefixEnd_7441643 1273713239388777757079671 := by
  unfold tailWord_7441643
  simp only [CollatzResearch.WordTrace]
  refine ⟨271419018179205817285489583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180946012119470544856993055 271419018179205817285489583)
  ·
    refine ⟨407128527268808725928234375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271419018179205817285489583 407128527268808725928234375)
    ·
      refine ⟨610692790903213088892351563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407128527268808725928234375 610692790903213088892351563)
      ·
        refine ⟨916039186354819633338527345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610692790903213088892351563 916039186354819633338527345)
        ·
          refine ⟨687029389766114725003895509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 916039186354819633338527345 687029389766114725003895509)
          ·
            refine ⟨16102251322643313867278801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 687029389766114725003895509 16102251322643313867278801)
            ·
              refine ⟨12076688491982485400459101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16102251322643313867278801 12076688491982485400459101)
              ·
                refine ⟨4528758184493432025172163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12076688491982485400459101 4528758184493432025172163)
                ·
                  refine ⟨6793137276740148037758245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528758184493432025172163 6793137276740148037758245)
                  ·
                    refine ⟨1273713239388777757079671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6793137276740148037758245 1273713239388777757079671)
                    ·
                      rfl

theorem cell23_7441643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 1, 4].length) (baseStart_7441643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441643 prefixEnd_7441643 := by exact prefixLift 7441643
  have htrace : WordTrace (prefixWord ++ tailWord_7441643) baseStart_7441643 baseEnd_7441643 := by
    simpa [prefixWord, tailWord_7441643, baseEnd_7441643] using wordTrace_append hprefix tailTrace_7441643
  have hstable : (prefixWord ++ tailWord_7441643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441643).length < 2 ^ (prefixWord ++ tailWord_7441643).sum := by decide
  have hdescent : baseEnd_7441643 < baseStart_7441643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441676 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 1, 5, 2]
def baseStart_7441676 : Nat := 118140960795 + 7441676 * 2 ^ 59
def prefixEnd_7441676 : Nat := 4983230072969 + 3 ^ 40 * 7441676 * 2
def baseEnd_7441676 : Nat := 3821156663027931642126361

theorem tailTrace_7441676 : CollatzResearch.WordTrace tailWord_7441676 prefixEnd_7441676 3821156663027931642126361 := by
  unfold tailWord_7441676
  simp only [CollatzResearch.WordTrace]
  refine ⟨135710110894043131960720441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180946814525390842614293921 135710110894043131960720441)
  ·
    refine ⟨101782583170532348970540331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135710110894043131960720441 101782583170532348970540331)
    ·
      refine ⟨152673874755798523455810497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101782583170532348970540331 152673874755798523455810497)
      ·
        refine ⟨114505406066848892591857873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152673874755798523455810497 114505406066848892591857873)
        ·
          refine ⟨85879054550136669443893405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114505406066848892591857873 85879054550136669443893405)
          ·
            refine ⟨32204645456301251041460027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85879054550136669443893405 32204645456301251041460027)
            ·
              refine ⟨48306968184451876562190041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32204645456301251041460027 48306968184451876562190041)
              ·
                refine ⟨36230226138338907421642531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48306968184451876562190041 36230226138338907421642531)
                ·
                  refine ⟨54345339207508361132463797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36230226138338907421642531 54345339207508361132463797)
                  ·
                    refine ⟨5094875550703908856168481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54345339207508361132463797 5094875550703908856168481)
                    ·
                      refine ⟨3821156663027931642126361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094875550703908856168481 3821156663027931642126361)
                      ·
                        rfl

theorem cell23_7441676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_7441676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441676 prefixEnd_7441676 := by exact prefixLift 7441676
  have htrace : WordTrace (prefixWord ++ tailWord_7441676) baseStart_7441676 baseEnd_7441676 := by
    simpa [prefixWord, tailWord_7441676, baseEnd_7441676] using wordTrace_append hprefix tailTrace_7441676
  have hstable : (prefixWord ++ tailWord_7441676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441676).length < 2 ^ (prefixWord ++ tailWord_7441676).sum := by decide
  have hdescent : baseEnd_7441676 < baseStart_7441676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441693 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_7441693 : Nat := 118140960795 + 7441693 * 2 ^ 59
def prefixEnd_7441693 : Nat := 4983230072969 + 3 ^ 40 * 7441693 * 2
def baseEnd_7441693 : Nat := 3821165392199058075613783

theorem tailTrace_7441693 : CollatzResearch.WordTrace tailWord_7441693 prefixEnd_7441693 3821165392199058075613783 := by
  unfold tailWord_7441693
  simp only [CollatzResearch.WordTrace]
  refine ⟨271420841829024675824809733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180947227886016450549873155 271420841829024675824809733)
  ·
    refine ⟨50891407842942126717151825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271420841829024675824809733 50891407842942126717151825)
    ·
      refine ⟨38168555882206595037863869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50891407842942126717151825 38168555882206595037863869)
      ·
        refine ⟨14313208455827473139198951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38168555882206595037863869 14313208455827473139198951)
        ·
          refine ⟨21469812683741209708798427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14313208455827473139198951 21469812683741209708798427)
          ·
            refine ⟨32204719025611814563197641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21469812683741209708798427 32204719025611814563197641)
            ·
              refine ⟨24153539269208860922398231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32204719025611814563197641 24153539269208860922398231)
              ·
                refine ⟨36230308903813291383597347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24153539269208860922398231 36230308903813291383597347)
                ·
                  refine ⟨54345463355719937075396021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36230308903813291383597347 54345463355719937075396021)
                  ·
                    refine ⟨5094887189598744100818377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54345463355719937075396021 5094887189598744100818377)
                    ·
                      refine ⟨3821165392199058075613783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094887189598744100818377 3821165392199058075613783)
                      ·
                        rfl

theorem cell23_7441693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_7441693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441693 prefixEnd_7441693 := by exact prefixLift 7441693
  have htrace : WordTrace (prefixWord ++ tailWord_7441693) baseStart_7441693 baseEnd_7441693 := by
    simpa [prefixWord, tailWord_7441693, baseEnd_7441693] using wordTrace_append hprefix tailTrace_7441693
  have hstable : (prefixWord ++ tailWord_7441693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441693).length < 2 ^ (prefixWord ++ tailWord_7441693).sum := by decide
  have hdescent : baseEnd_7441693 < baseStart_7441693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441694 : List Nat := [4, 3, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_7441694 : Nat := 118140960795 + 7441694 * 2 ^ 59
def prefixEnd_7441694 : Nat := 4983230072969 + 3 ^ 40 * 7441694 * 2
def baseEnd_7441694 : Nat := 1273721968559904190567093

theorem tailTrace_7441694 : CollatzResearch.WordTrace tailWord_7441694 prefixEnd_7441694 1273721968559904190567093 := by
  unfold tailWord_7441694
  simp only [CollatzResearch.WordTrace]
  refine ⟨33927609787752631624449517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180947252201347368663730757 33927609787752631624449517)
  ·
    refine ⟨12722853670407236859168569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33927609787752631624449517 12722853670407236859168569)
    ·
      refine ⟨9542140252805427644376427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12722853670407236859168569 9542140252805427644376427)
      ·
        refine ⟨14313210379208141466564641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9542140252805427644376427 14313210379208141466564641)
        ·
          refine ⟨10734907784406106099923481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14313210379208141466564641 10734907784406106099923481)
          ·
            refine ⟨8051180838304579574942611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10734907784406106099923481 8051180838304579574942611)
            ·
              refine ⟨12076771257456869362413917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051180838304579574942611 12076771257456869362413917)
              ·
                refine ⟨4528789221546326010905219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12076771257456869362413917 4528789221546326010905219)
                ·
                  refine ⟨6793183832319489016357829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528789221546326010905219 6793183832319489016357829)
                  ·
                    refine ⟨1273721968559904190567093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6793183832319489016357829 1273721968559904190567093)
                    ·
                      rfl

theorem cell23_7441694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_7441694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441694 prefixEnd_7441694 := by exact prefixLift 7441694
  have htrace : WordTrace (prefixWord ++ tailWord_7441694) baseStart_7441694 baseEnd_7441694 := by
    simpa [prefixWord, tailWord_7441694, baseEnd_7441694] using wordTrace_append hprefix tailTrace_7441694
  have hstable : (prefixWord ++ tailWord_7441694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441694).length < 2 ^ (prefixWord ++ tailWord_7441694).sum := by decide
  have hdescent : baseEnd_7441694 < baseStart_7441694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441717 : List Nat := [1, 3, 3, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_7441717 : Nat := 118140960795 + 7441717 * 2 ^ 59
def prefixEnd_7441717 : Nat := 4983230072969 + 3 ^ 40 * 7441717 * 2
def baseEnd_7441717 : Nat := 3821177715734765981713673

theorem tailTrace_7441717 : CollatzResearch.WordTrace tailWord_7441717 prefixEnd_7441717 3821177715734765981713673 := by
  unfold tailWord_7441717
  simp only [CollatzResearch.WordTrace]
  refine ⟨271421717180937727923683405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180947811453958485282455603 271421717180937727923683405)
  ·
    refine ⟨101783143942851647971381277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271421717180937727923683405 101783143942851647971381277)
    ·
      refine ⟨38168678978569367989267979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101783143942851647971381277 38168678978569367989267979)
      ·
        refine ⟨57253018467854051983901969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38168678978569367989267979 57253018467854051983901969)
        ·
          refine ⟨42939763850890538987926477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57253018467854051983901969 42939763850890538987926477)
          ·
            refine ⟨16102411444083952120472429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42939763850890538987926477 16102411444083952120472429)
            ·
              refine ⟨6038404291531482045177161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16102411444083952120472429 6038404291531482045177161)
              ·
                refine ⟨4528803218648611533882871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6038404291531482045177161 4528803218648611533882871)
                ·
                  refine ⟨6793204827972917300824307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528803218648611533882871 6793204827972917300824307)
                  ·
                    refine ⟨10189807241959375951236461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6793204827972917300824307 10189807241959375951236461)
                    ·
                      refine ⟨3821177715734765981713673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10189807241959375951236461 3821177715734765981713673)
                      ·
                        rfl

theorem cell23_7441717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_7441717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441717 prefixEnd_7441717 := by exact prefixLift 7441717
  have htrace : WordTrace (prefixWord ++ tailWord_7441717) baseStart_7441717 baseEnd_7441717 := by
    simpa [prefixWord, tailWord_7441717, baseEnd_7441717] using wordTrace_append hprefix tailTrace_7441717
  have hstable : (prefixWord ++ tailWord_7441717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441717).length < 2 ^ (prefixWord ++ tailWord_7441717).sum := by decide
  have hdescent : baseEnd_7441717 < baseStart_7441717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441726 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_7441726 : Nat := 118140960795 + 7441726 * 2 ^ 59
def prefixEnd_7441726 : Nat := 4983230072969 + 3 ^ 40 * 7441726 * 2
def baseEnd_7441726 : Nat := 3821182337060656446501131

theorem tailTrace_7441726 : CollatzResearch.WordTrace tailWord_7441726 prefixEnd_7441726 3821182337060656446501131 := by
  unfold tailWord_7441726
  simp only [CollatzResearch.WordTrace]
  refine ⟨33927755679738140307595129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180948030291936748307174021 33927755679738140307595129)
  ·
    refine ⟨25445816759803605230696347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33927755679738140307595129 25445816759803605230696347)
    ·
      refine ⟨38168725139705407846044521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25445816759803605230696347 38168725139705407846044521)
      ·
        refine ⟨28626543854779055884533391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38168725139705407846044521 28626543854779055884533391)
        ·
          refine ⟨42939815782168583826800087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28626543854779055884533391 42939815782168583826800087)
          ·
            refine ⟨64409723673252875740200131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42939815782168583826800087 64409723673252875740200131)
            ·
              refine ⟨96614585509879313610300197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64409723673252875740200131 96614585509879313610300197)
              ·
                refine ⟨18115234783102371301931287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96614585509879313610300197 18115234783102371301931287)
                ·
                  refine ⟨27172852174653556952896931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18115234783102371301931287 27172852174653556952896931)
                  ·
                    refine ⟨40759278261980335429345397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27172852174653556952896931 40759278261980335429345397)
                    ·
                      refine ⟨3821182337060656446501131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40759278261980335429345397 3821182337060656446501131)
                      ·
                        rfl

theorem cell23_7441726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_7441726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441726 prefixEnd_7441726 := by exact prefixLift 7441726
  have htrace : WordTrace (prefixWord ++ tailWord_7441726) baseStart_7441726 baseEnd_7441726 := by
    simpa [prefixWord, tailWord_7441726, baseEnd_7441726] using wordTrace_append hprefix tailTrace_7441726
  have hstable : (prefixWord ++ tailWord_7441726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441726).length < 2 ^ (prefixWord ++ tailWord_7441726).sum := by decide
  have hdescent : baseEnd_7441726 < baseStart_7441726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441760 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 1, 2, 3]
def baseStart_7441760 : Nat := 118140960795 + 7441760 * 2 ^ 59
def prefixEnd_7441760 : Nat := 4983230072969 + 3 ^ 40 * 7441760 * 2
def baseEnd_7441760 : Nat := 3821199795402909313475975

theorem tailTrace_7441760 : CollatzResearch.WordTrace tailWord_7441760 prefixEnd_7441760 3821199795402909313475975 := by
  unfold tailWord_7441760
  simp only [CollatzResearch.WordTrace]
  refine ⟨135711642759890973133749367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180948857013187964178332489 135711642759890973133749367)
  ·
    refine ⟨203567464139836459700624051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135711642759890973133749367 203567464139836459700624051)
    ·
      refine ⟨305351196209754689550936077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203567464139836459700624051 305351196209754689550936077)
      ·
        refine ⟨114506698578658008581601029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305351196209754689550936077 114506698578658008581601029)
        ·
          refine ⟨21470005983498376609050193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114506698578658008581601029 21470005983498376609050193)
          ·
            refine ⟨16102504487623782456787645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21470005983498376609050193 16102504487623782456787645)
            ·
              refine ⟨6038439182858918421295367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16102504487623782456787645 6038439182858918421295367)
              ·
                refine ⟨9057658774288377631943051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6038439182858918421295367 9057658774288377631943051)
                ·
                  refine ⟨13586488161432566447914577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9057658774288377631943051 13586488161432566447914577)
                  ·
                    refine ⟨10189866121074424835935933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13586488161432566447914577 10189866121074424835935933)
                    ·
                      refine ⟨3821199795402909313475975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10189866121074424835935933 3821199795402909313475975)
                      ·
                        rfl

theorem cell23_7441760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_7441760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441760 prefixEnd_7441760 := by exact prefixLift 7441760
  have htrace : WordTrace (prefixWord ++ tailWord_7441760) baseStart_7441760 baseEnd_7441760 := by
    simpa [prefixWord, tailWord_7441760, baseEnd_7441760] using wordTrace_append hprefix tailTrace_7441760
  have hstable : (prefixWord ++ tailWord_7441760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441760).length < 2 ^ (prefixWord ++ tailWord_7441760).sum := by decide
  have hdescent : baseEnd_7441760 < baseStart_7441760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441813 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 1, 4, 2]
def baseStart_7441813 : Nat := 118140960795 + 7441813 * 2 ^ 59
def prefixEnd_7441813 : Nat := 4983230072969 + 3 ^ 40 * 7441813 * 2
def baseEnd_7441813 : Nat := 3821227009877597606113231

theorem tailTrace_7441813 : CollatzResearch.WordTrace tailWord_7441813 prefixEnd_7441813 3821227009877597606113231 := by
  unfold tailWord_7441813
  simp only [CollatzResearch.WordTrace]
  refine ⟨271425218588589936319178093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180950145725726624212785395 271425218588589936319178093)
  ·
    refine ⟨101784456970721226119691785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271425218588589936319178093 101784456970721226119691785)
    ·
      refine ⟨76338342728040919589768839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101784456970721226119691785 76338342728040919589768839)
      ·
        refine ⟨114507514092061379384653259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76338342728040919589768839 114507514092061379384653259)
        ·
          refine ⟨171761271138092069076979889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114507514092061379384653259 171761271138092069076979889)
          ·
            refine ⟨128820953353569051807734917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171761271138092069076979889 128820953353569051807734917)
            ·
              refine ⟨24153928753794197213950297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128820953353569051807734917 24153928753794197213950297)
              ·
                refine ⟨18115446565345647910462723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24153928753794197213950297 18115446565345647910462723)
                ·
                  refine ⟨27173169848018471865694085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18115446565345647910462723 27173169848018471865694085)
                  ·
                    refine ⟨5094969346503463474817641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27173169848018471865694085 5094969346503463474817641)
                    ·
                      refine ⟨3821227009877597606113231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094969346503463474817641 3821227009877597606113231)
                      ·
                        rfl

theorem cell23_7441813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_7441813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441813 prefixEnd_7441813 := by exact prefixLift 7441813
  have htrace : WordTrace (prefixWord ++ tailWord_7441813) baseStart_7441813 baseEnd_7441813 := by
    simpa [prefixWord, tailWord_7441813, baseEnd_7441813] using wordTrace_append hprefix tailTrace_7441813
  have hstable : (prefixWord ++ tailWord_7441813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441813).length < 2 ^ (prefixWord ++ tailWord_7441813).sum := by decide
  have hdescent : baseEnd_7441813 < baseStart_7441813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441817 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 1, 3, 2]
def baseStart_7441817 : Nat := 118140960795 + 7441817 * 2 ^ 59
def prefixEnd_7441817 : Nat := 4983230072969 + 3 ^ 40 * 7441817 * 2
def baseEnd_7441817 : Nat := 3821229063800215590463213

theorem tailTrace_7441817 : CollatzResearch.WordTrace tailWord_7441817 prefixEnd_7441817 3821229063800215590463213 := by
  unfold tailWord_7441817
  simp only [CollatzResearch.WordTrace]
  refine ⟨271425364480575445002323705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180950242987050296668215803 271425364480575445002323705)
  ·
    refine ⟨203569023360431583751742779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271425364480575445002323705 203569023360431583751742779)
    ·
      refine ⟨305353535040647375627614169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203569023360431583751742779 305353535040647375627614169)
      ·
        refine ⟨229015151280485531720710627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305353535040647375627614169 229015151280485531720710627)
        ·
          refine ⟨343522726920728297581065941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229015151280485531720710627 343522726920728297581065941)
          ·
            refine ⟨8051313912204569474556233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 343522726920728297581065941 8051313912204569474556233)
            ·
              refine ⟨6038485434153427105917175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8051313912204569474556233 6038485434153427105917175)
              ·
                refine ⟨9057728151230140658875763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6038485434153427105917175 9057728151230140658875763)
                ·
                  refine ⟨13586592226845210988313645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9057728151230140658875763 13586592226845210988313645)
                  ·
                    refine ⟨5094972085066954120617617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13586592226845210988313645 5094972085066954120617617)
                    ·
                      refine ⟨3821229063800215590463213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094972085066954120617617 3821229063800215590463213)
                      ·
                        rfl

theorem cell23_7441817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 3, 2].length) (baseStart_7441817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441817 prefixEnd_7441817 := by exact prefixLift 7441817
  have htrace : WordTrace (prefixWord ++ tailWord_7441817) baseStart_7441817 baseEnd_7441817 := by
    simpa [prefixWord, tailWord_7441817, baseEnd_7441817] using wordTrace_append hprefix tailTrace_7441817
  have hstable : (prefixWord ++ tailWord_7441817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441817).length < 2 ^ (prefixWord ++ tailWord_7441817).sum := by decide
  have hdescent : baseEnd_7441817 < baseStart_7441817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441829 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_7441829 : Nat := 118140960795 + 7441829 * 2 ^ 59
def prefixEnd_7441829 : Nat := 4983230072969 + 3 ^ 40 * 7441829 * 2
def baseEnd_7441829 : Nat := 3821235225568069543513157

theorem tailTrace_7441829 : CollatzResearch.WordTrace tailWord_7441829 prefixEnd_7441829 3821235225568069543513157 := by
  unfold tailWord_7441829
  simp only [CollatzResearch.WordTrace]
  refine ⟨271425802156531971051760541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180950534771021314034507027 271425802156531971051760541)
  ·
    refine ⟨101784675808699489144410203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271425802156531971051760541 101784675808699489144410203)
    ·
      refine ⟨152677013713049233716615305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101784675808699489144410203 152677013713049233716615305)
      ·
        refine ⟨114507760284786925287461479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152677013713049233716615305 114507760284786925287461479)
        ·
          refine ⟨171761640427180387931192219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114507760284786925287461479 171761640427180387931192219)
          ·
            refine ⟨257642460640770581896788329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171761640427180387931192219 257642460640770581896788329)
            ·
              refine ⟨193231845480577936422591247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257642460640770581896788329 193231845480577936422591247)
              ·
                refine ⟨289847768220866904633886871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193231845480577936422591247 289847768220866904633886871)
                ·
                  refine ⟨434771652331300356950830307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289847768220866904633886871 434771652331300356950830307)
                  ·
                    refine ⟨652157478496950535426245461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 434771652331300356950830307 652157478496950535426245461)
                    ·
                      refine ⟨3821235225568069543513157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 652157478496950535426245461 3821235225568069543513157)
                      ·
                        rfl

theorem cell23_7441829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_7441829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441829 prefixEnd_7441829 := by exact prefixLift 7441829
  have htrace : WordTrace (prefixWord ++ tailWord_7441829) baseStart_7441829 baseEnd_7441829 := by
    simpa [prefixWord, tailWord_7441829, baseEnd_7441829] using wordTrace_append hprefix tailTrace_7441829
  have hstable : (prefixWord ++ tailWord_7441829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441829).length < 2 ^ (prefixWord ++ tailWord_7441829).sum := by decide
  have hdescent : baseEnd_7441829 < baseStart_7441829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441847 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 2, 2, 2]
def baseStart_7441847 : Nat := 118140960795 + 7441847 * 2 ^ 59
def prefixEnd_7441847 : Nat := 4983230072969 + 3 ^ 40 * 7441847 * 2
def baseEnd_7441847 : Nat := 3821244468219850473088075

theorem tailTrace_7441847 : CollatzResearch.WordTrace tailWord_7441847 prefixEnd_7441847 3821244468219850473088075 := by
  unfold tailWord_7441847
  simp only [CollatzResearch.WordTrace]
  refine ⟨271426458670466760125915795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180950972446977840083943863 271426458670466760125915795)
  ·
    refine ⟨407139688005700140188873693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271426458670466760125915795 407139688005700140188873693)
    ·
      refine ⟨152677383002137552570827635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407139688005700140188873693 152677383002137552570827635)
      ·
        refine ⟨229016074503206328856241453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152677383002137552570827635 229016074503206328856241453)
        ·
          refine ⟨85881027938702373321090545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229016074503206328856241453 85881027938702373321090545)
          ·
            refine ⟨64410770954026779990817909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85881027938702373321090545 64410770954026779990817909)
            ·
              refine ⟨6038509776940010624139179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64410770954026779990817909 6038509776940010624139179)
              ·
                refine ⟨9057764665410015936208769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6038509776940010624139179 9057764665410015936208769)
                ·
                  refine ⟨6793323499057511952156577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9057764665410015936208769 6793323499057511952156577)
                  ·
                    refine ⟨5094992624293133964117433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6793323499057511952156577 5094992624293133964117433)
                    ·
                      refine ⟨3821244468219850473088075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094992624293133964117433 3821244468219850473088075)
                      ·
                        rfl

theorem cell23_7441847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 2, 2].length) (baseStart_7441847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441847 prefixEnd_7441847 := by exact prefixLift 7441847
  have htrace : WordTrace (prefixWord ++ tailWord_7441847) baseStart_7441847 baseEnd_7441847 := by
    simpa [prefixWord, tailWord_7441847, baseEnd_7441847] using wordTrace_append hprefix tailTrace_7441847
  have hstable : (prefixWord ++ tailWord_7441847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441847).length < 2 ^ (prefixWord ++ tailWord_7441847).sum := by decide
  have hdescent : baseEnd_7441847 < baseStart_7441847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441866 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_7441866 : Nat := 118140960795 + 7441866 * 2 ^ 59
def prefixEnd_7441866 : Nat := 4983230072969 + 3 ^ 40 * 7441866 * 2
def baseEnd_7441866 : Nat := 1273751408117428632916829

theorem tailTrace_7441866 : CollatzResearch.WordTrace tailWord_7441866 prefixEnd_7441866 1273751408117428632916829 := by
  unfold tailWord_7441866
  simp only [CollatzResearch.WordTrace]
  refine ⟨67856787914349481592714363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180951434438265284247238301 67856787914349481592714363)
  ·
    refine ⟨101785181871524222389071545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67856787914349481592714363 101785181871524222389071545)
    ·
      refine ⟨76338886403643166791803659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101785181871524222389071545 76338886403643166791803659)
      ·
        refine ⟨114508329605464750187705489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76338886403643166791803659 114508329605464750187705489)
        ·
          refine ⟨85881247204098562640779117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114508329605464750187705489 85881247204098562640779117)
          ·
            refine ⟨32205467701536960990292169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85881247204098562640779117 32205467701536960990292169)
            ·
              refine ⟨24154100776152720742719127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32205467701536960990292169 24154100776152720742719127)
              ·
                refine ⟨36231151164229081114078691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24154100776152720742719127 36231151164229081114078691)
                ·
                  refine ⟨54346726746343621671118037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36231151164229081114078691 54346726746343621671118037)
                  ·
                    refine ⟨1273751408117428632916829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54346726746343621671118037 1273751408117428632916829)
                    ·
                      rfl

theorem cell23_7441866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_7441866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441866 prefixEnd_7441866 := by exact prefixLift 7441866
  have htrace : WordTrace (prefixWord ++ tailWord_7441866) baseStart_7441866 baseEnd_7441866 := by
    simpa [prefixWord, tailWord_7441866, baseEnd_7441866] using wordTrace_append hprefix tailTrace_7441866
  have hstable : (prefixWord ++ tailWord_7441866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441866).length < 2 ^ (prefixWord ++ tailWord_7441866).sum := by decide
  have hdescent : baseEnd_7441866 < baseStart_7441866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441893 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_7441893 : Nat := 118140960795 + 7441893 * 2 ^ 59
def prefixEnd_7441893 : Nat := 4983230072969 + 3 ^ 40 * 7441893 * 2
def baseEnd_7441893 : Nat := 3821268088329957293112863

theorem tailTrace_7441893 : CollatzResearch.WordTrace tailWord_7441893 prefixEnd_7441893 3821268088329957293112863 := by
  unfold tailWord_7441893
  simp only [CollatzResearch.WordTrace]
  refine ⟨271428136428300109982090333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180952090952200073321393555 271428136428300109982090333)
  ·
    refine ⟨101785551160612541243283875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271428136428300109982090333 101785551160612541243283875)
    ·
      refine ⟨152678326740918811864925813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101785551160612541243283875 152678326740918811864925813)
      ·
        refine ⟨14313593131961138612336795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152678326740918811864925813 14313593131961138612336795)
        ·
          refine ⟨21470389697941707918505193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14313593131961138612336795 21470389697941707918505193)
          ·
            refine ⟨16102792273456280938878895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21470389697941707918505193 16102792273456280938878895)
            ·
              refine ⟨24154188410184421408318343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16102792273456280938878895 24154188410184421408318343)
              ·
                refine ⟨36231282615276632112477515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24154188410184421408318343 36231282615276632112477515)
                ·
                  refine ⟨54346923922914948168716273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36231282615276632112477515 54346923922914948168716273)
                  ·
                    refine ⟨40760192942186211126537205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54346923922914948168716273 40760192942186211126537205)
                    ·
                      refine ⟨3821268088329957293112863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40760192942186211126537205 3821268088329957293112863)
                      ·
                        rfl

theorem cell23_7441893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_7441893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441893 prefixEnd_7441893 := by exact prefixLift 7441893
  have htrace : WordTrace (prefixWord ++ tailWord_7441893) baseStart_7441893 baseEnd_7441893 := by
    simpa [prefixWord, tailWord_7441893, baseEnd_7441893] using wordTrace_append hprefix tailTrace_7441893
  have hstable : (prefixWord ++ tailWord_7441893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441893).length < 2 ^ (prefixWord ++ tailWord_7441893).sum := by decide
  have hdescent : baseEnd_7441893 < baseStart_7441893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441903 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 2, 4, 2]
def baseStart_7441903 : Nat := 118140960795 + 7441903 * 2 ^ 59
def prefixEnd_7441903 : Nat := 4983230072969 + 3 ^ 40 * 7441903 * 2
def baseEnd_7441903 : Nat := 3821273223136502253987817

theorem tailTrace_7441903 : CollatzResearch.WordTrace tailWord_7441903 prefixEnd_7441903 3821273223136502253987817 := by
  unfold tailWord_7441903
  simp only [CollatzResearch.WordTrace]
  refine ⟨271428501158263881689954363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180952334105509254459969575 271428501158263881689954363)
  ·
    refine ⟨407142751737395822534931545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271428501158263881689954363 407142751737395822534931545)
    ·
      refine ⟨305357063803046866901198659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407142751737395822534931545 305357063803046866901198659)
      ·
        refine ⟨458035595704570300351797989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305357063803046866901198659 458035595704570300351797989)
        ·
          refine ⟨85881674194606931315962123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 458035595704570300351797989 85881674194606931315962123)
          ·
            refine ⟨128822511291910396973943185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85881674194606931315962123 128822511291910396973943185)
            ·
              refine ⟨96616883468932797730457389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128822511291910396973943185 96616883468932797730457389)
              ·
                refine ⟨36231331300849799148921521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96616883468932797730457389 36231331300849799148921521)
                ·
                  refine ⟨27173498475637349361691141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36231331300849799148921521 27173498475637349361691141)
                  ·
                    refine ⟨5095030964182003005317089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27173498475637349361691141 5095030964182003005317089)
                    ·
                      refine ⟨3821273223136502253987817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095030964182003005317089 3821273223136502253987817)
                      ·
                        rfl

theorem cell23_7441903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 4, 2].length) (baseStart_7441903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441903 prefixEnd_7441903 := by exact prefixLift 7441903
  have htrace : WordTrace (prefixWord ++ tailWord_7441903) baseStart_7441903 baseEnd_7441903 := by
    simpa [prefixWord, tailWord_7441903, baseEnd_7441903] using wordTrace_append hprefix tailTrace_7441903
  have hstable : (prefixWord ++ tailWord_7441903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441903).length < 2 ^ (prefixWord ++ tailWord_7441903).sum := by decide
  have hdescent : baseEnd_7441903 < baseStart_7441903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441916 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_7441916 : Nat := 118140960795 + 7441916 * 2 ^ 59
def prefixEnd_7441916 : Nat := 4983230072969 + 3 ^ 40 * 7441916 * 2
def baseEnd_7441916 : Nat := 3821279898385010703125257

theorem tailTrace_7441916 : CollatzResearch.WordTrace tailWord_7441916 prefixEnd_7441916 3821279898385010703125257 := by
  unfold tailWord_7441916
  simp only [CollatzResearch.WordTrace]
  refine ⟨135714487653608392455088801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180952650204811189940118401 135714487653608392455088801)
  ·
    refine ⟨101785865740206294341316601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135714487653608392455088801 101785865740206294341316601)
    ·
      refine ⟨76339399305154720755987451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101785865740206294341316601 76339399305154720755987451)
      ·
        refine ⟨114509098957732081133981177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76339399305154720755987451 114509098957732081133981177)
        ·
          refine ⟨85881824218299060850485883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114509098957732081133981177 85881824218299060850485883)
          ·
            refine ⟨128822736327448591275728825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85881824218299060850485883 128822736327448591275728825)
            ·
              refine ⟨96617052245586443456796619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128822736327448591275728825 96617052245586443456796619)
              ·
                refine ⟨144925578368379665185194929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96617052245586443456796619 144925578368379665185194929)
                ·
                  refine ⟨108694183776284748888896197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144925578368379665185194929 108694183776284748888896197)
                  ·
                    refine ⟨20380159458053390416668037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108694183776284748888896197 20380159458053390416668037)
                    ·
                      refine ⟨3821279898385010703125257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20380159458053390416668037 3821279898385010703125257)
                      ·
                        rfl

theorem cell23_7441916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_7441916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441916 prefixEnd_7441916 := by exact prefixLift 7441916
  have htrace : WordTrace (prefixWord ++ tailWord_7441916) baseStart_7441916 baseEnd_7441916 := by
    simpa [prefixWord, tailWord_7441916, baseEnd_7441916] using wordTrace_append hprefix tailTrace_7441916
  have hstable : (prefixWord ++ tailWord_7441916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441916).length < 2 ^ (prefixWord ++ tailWord_7441916).sum := by decide
  have hdescent : baseEnd_7441916 < baseStart_7441916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441946 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_7441946 : Nat := 118140960795 + 7441946 * 2 ^ 59
def prefixEnd_7441946 : Nat := 4983230072969 + 3 ^ 40 * 7441946 * 2
def baseEnd_7441946 : Nat := 3821295302804645585750119

theorem tailTrace_7441946 : CollatzResearch.WordTrace tailWord_7441946 prefixEnd_7441946 3821295302804645585750119 := by
  unfold tailWord_7441946
  simp only [CollatzResearch.WordTrace]
  refine ⟨67857517374277025008442423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180953379664738733355846461 67857517374277025008442423)
  ·
    refine ⟨101786276061415537512663635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67857517374277025008442423 101786276061415537512663635)
    ·
      refine ⟨152679414092123306268995453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101786276061415537512663635 152679414092123306268995453)
      ·
        refine ⟨57254780284546239850873295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152679414092123306268995453 57254780284546239850873295)
        ·
          refine ⟨85882170426819359776309943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57254780284546239850873295 85882170426819359776309943)
          ·
            refine ⟨128823255640229039664464915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85882170426819359776309943 128823255640229039664464915)
            ·
              refine ⟨193234883460343559496697373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128823255640229039664464915 193234883460343559496697373)
              ·
                refine ⟨72463081297628834811261515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193234883460343559496697373 72463081297628834811261515)
                ·
                  refine ⟨108694621946443252216892273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72463081297628834811261515 108694621946443252216892273)
                  ·
                    refine ⟨81520966459832439162669205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108694621946443252216892273 81520966459832439162669205)
                    ·
                      refine ⟨3821295302804645585750119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81520966459832439162669205 3821295302804645585750119)
                      ·
                        rfl

theorem cell23_7441946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_7441946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441946 prefixEnd_7441946 := by exact prefixLift 7441946
  have htrace : WordTrace (prefixWord ++ tailWord_7441946) baseStart_7441946 baseEnd_7441946 := by
    simpa [prefixWord, tailWord_7441946, baseEnd_7441946] using wordTrace_append hprefix tailTrace_7441946
  have hstable : (prefixWord ++ tailWord_7441946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441946).length < 2 ^ (prefixWord ++ tailWord_7441946).sum := by decide
  have hdescent : baseEnd_7441946 < baseStart_7441946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441973 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_7441973 : Nat := 118140960795 + 7441973 * 2 ^ 59
def prefixEnd_7441973 : Nat := 4983230072969 + 3 ^ 40 * 7441973 * 2
def baseEnd_7441973 : Nat := 1273769722260772326704165

theorem tailTrace_7441973 : CollatzResearch.WordTrace tailWord_7441973 prefixEnd_7441973 1273769722260772326704165 := by
  unfold tailWord_7441973
  simp only [CollatzResearch.WordTrace]
  refine ⟨271431054268010283645002573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180954036178673522430001715 271431054268010283645002573)
  ·
    refine ⟨101786645350503856366875965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271431054268010283645002573 101786645350503856366875965)
    ·
      refine ⟨38169992006438946137578487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101786645350503856366875965 38169992006438946137578487)
      ·
        refine ⟨57254988009658419206367731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38169992006438946137578487 57254988009658419206367731)
        ·
          refine ⟨85882482014487628809551597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57254988009658419206367731 85882482014487628809551597)
          ·
            refine ⟨32205930755432860803581849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85882482014487628809551597 32205930755432860803581849)
            ·
              refine ⟨24154448066574645602686387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32205930755432860803581849 24154448066574645602686387)
              ·
                refine ⟨36231672099861968404029581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24154448066574645602686387 36231672099861968404029581)
                ·
                  refine ⟨13586877037448238151511093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36231672099861968404029581 13586877037448238151511093)
                  ·
                    refine ⟨1273769722260772326704165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13586877037448238151511093 1273769722260772326704165)
                    ·
                      rfl

theorem cell23_7441973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_7441973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441973 prefixEnd_7441973 := by exact prefixLift 7441973
  have htrace : WordTrace (prefixWord ++ tailWord_7441973) baseStart_7441973 baseEnd_7441973 := by
    simpa [prefixWord, tailWord_7441973, baseEnd_7441973] using wordTrace_append hprefix tailTrace_7441973
  have hstable : (prefixWord ++ tailWord_7441973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441973).length < 2 ^ (prefixWord ++ tailWord_7441973).sum := by decide
  have hdescent : baseEnd_7441973 < baseStart_7441973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441974 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_7441974 : Nat := 118140960795 + 7441974 * 2 ^ 59
def prefixEnd_7441974 : Nat := 4983230072969 + 3 ^ 40 * 7441974 * 2
def baseEnd_7441974 : Nat := 3821309680262971476199991

theorem tailTrace_7441974 : CollatzResearch.WordTrace tailWord_7441974 prefixEnd_7441974 3821309680262971476199991 := by
  unfold tailWord_7441974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16964443171312916300986811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180954060494004440543859317 16964443171312916300986811)
  ·
    refine ⟨25446664756969374451480217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16964443171312916300986811 25446664756969374451480217)
    ·
      refine ⟨19084998567727030838610163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25446664756969374451480217 19084998567727030838610163)
      ·
        refine ⟨28627497851590546257915245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19084998567727030838610163 28627497851590546257915245)
        ·
          refine ⟨10735311694346454846718217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28627497851590546257915245 10735311694346454846718217)
          ·
            refine ⟨8051483770759841135038663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10735311694346454846718217 8051483770759841135038663)
            ·
              refine ⟨12077225656139761702557995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051483770759841135038663 12077225656139761702557995)
              ·
                refine ⟨18115838484209642553836993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12077225656139761702557995 18115838484209642553836993)
                ·
                  refine ⟨13586878863157231915377745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18115838484209642553836993 13586878863157231915377745)
                  ·
                    refine ⟨10190159147367923936533309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13586878863157231915377745 10190159147367923936533309)
                    ·
                      refine ⟨3821309680262971476199991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10190159147367923936533309 3821309680262971476199991)
                      ·
                        rfl

theorem cell23_7441974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_7441974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441974 prefixEnd_7441974 := by exact prefixLift 7441974
  have htrace : WordTrace (prefixWord ++ tailWord_7441974) baseStart_7441974 baseEnd_7441974 := by
    simpa [prefixWord, tailWord_7441974, baseEnd_7441974] using wordTrace_append hprefix tailTrace_7441974
  have hstable : (prefixWord ++ tailWord_7441974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441974).length < 2 ^ (prefixWord ++ tailWord_7441974).sum := by decide
  have hdescent : baseEnd_7441974 < baseStart_7441974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7441993 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 1, 8, 2]
def baseStart_7441993 : Nat := 118140960795 + 7441993 * 2 ^ 59
def prefixEnd_7441993 : Nat := 4983230072969 + 3 ^ 40 * 7441993 * 2
def baseEnd_7441993 : Nat := 3821319436395406901862403

theorem tailTrace_7441993 : CollatzResearch.WordTrace tailWord_7441993 prefixEnd_7441993 3821319436395406901862403 := by
  unfold tailWord_7441993
  simp only [CollatzResearch.WordTrace]
  refine ⟨271431783727937827060730633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180954522485291884707153755 271431783727937827060730633)
  ·
    refine ⟨203573837795953370295547975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271431783727937827060730633 203573837795953370295547975)
    ·
      refine ⟨305360756693930055443321963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203573837795953370295547975 305360756693930055443321963)
      ·
        refine ⟨458041135040895083164982945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305360756693930055443321963 458041135040895083164982945)
        ·
          refine ⟨343530851280671312373737209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458041135040895083164982945 343530851280671312373737209)
          ·
            refine ⟨257648138460503484280302907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343530851280671312373737209 257648138460503484280302907)
            ·
              refine ⟨386472207690755226420454361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257648138460503484280302907 386472207690755226420454361)
              ·
                refine ⟨289854155768066419815340771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386472207690755226420454361 289854155768066419815340771)
                ·
                  refine ⟨434781233652099629723011157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289854155768066419815340771 434781233652099629723011157)
                  ·
                    refine ⟨5095092581860542535816537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 434781233652099629723011157 5095092581860542535816537)
                    ·
                      refine ⟨3821319436395406901862403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095092581860542535816537 3821319436395406901862403)
                      ·
                        rfl

theorem cell23_7441993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 8, 2].length) (baseStart_7441993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7441993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7441993 prefixEnd_7441993 := by exact prefixLift 7441993
  have htrace : WordTrace (prefixWord ++ tailWord_7441993) baseStart_7441993 baseEnd_7441993 := by
    simpa [prefixWord, tailWord_7441993, baseEnd_7441993] using wordTrace_append hprefix tailTrace_7441993
  have hstable : (prefixWord ++ tailWord_7441993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7441993).length < 2 ^ (prefixWord ++ tailWord_7441993).sum := by decide
  have hdescent : baseEnd_7441993 < baseStart_7441993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7441993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442016 : List Nat := [2, 1, 1, 3, 2, 1, 1, 12]
def baseStart_7442016 : Nat := 118140960795 + 7442016 * 2 ^ 59
def prefixEnd_7442016 : Nat := 4983230072969 + 3 ^ 40 * 7442016 * 2
def baseEnd_7442016 : Nat := 141530786905572604143511

theorem tailTrace_7442016 : CollatzResearch.WordTrace tailWord_7442016 prefixEnd_7442016 141530786905572604143511 := by
  unfold tailWord_7442016
  simp only [CollatzResearch.WordTrace]
  refine ⟨135716311303427250994408951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180955081737903001325878601 135716311303427250994408951)
  ·
    refine ⟨203574466955140876491613427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135716311303427250994408951 203574466955140876491613427)
    ·
      refine ⟨305361700432711314737420141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203574466955140876491613427 305361700432711314737420141)
      ·
        refine ⟨114510637662266743026532553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305361700432711314737420141 114510637662266743026532553)
        ·
          refine ⟨85882978246700057269899415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114510637662266743026532553 85882978246700057269899415)
          ·
            refine ⟨128824467370050085904849123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85882978246700057269899415 128824467370050085904849123)
            ·
              refine ⟨193236701055075128857273685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128824467370050085904849123 193236701055075128857273685)
              ·
                refine ⟨141530786905572604143511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 193236701055075128857273685 141530786905572604143511)
                ·
                  rfl

theorem cell23_7442016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 12].length) (baseStart_7442016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442016 prefixEnd_7442016 := by exact prefixLift 7442016
  have htrace : WordTrace (prefixWord ++ tailWord_7442016) baseStart_7442016 baseEnd_7442016 := by
    simpa [prefixWord, tailWord_7442016, baseEnd_7442016] using wordTrace_append hprefix tailTrace_7442016
  have hstable : (prefixWord ++ tailWord_7442016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442016).length < 2 ^ (prefixWord ++ tailWord_7442016).sum := by decide
  have hdescent : baseEnd_7442016 < baseStart_7442016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442020 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_7442020 : Nat := 118140960795 + 7442020 * 2 ^ 59
def prefixEnd_7442020 : Nat := 4983230072969 + 3 ^ 40 * 7442020 * 2
def baseEnd_7442020 : Nat := 1273777766791026098741593

theorem tailTrace_7442020 : CollatzResearch.WordTrace tailWord_7442020 prefixEnd_7442020 1273777766791026098741593 := by
  unfold tailWord_7442020
  simp only [CollatzResearch.WordTrace]
  refine ⟨135716384249420005335981757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180955178999226673781309009 135716384249420005335981757)
  ·
    refine ⟨50893644093532502000993159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135716384249420005335981757 50893644093532502000993159)
    ·
      refine ⟨76340466140298753001489739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50893644093532502000993159 76340466140298753001489739)
      ·
        refine ⟨114510699210448129502234609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76340466140298753001489739 114510699210448129502234609)
        ·
          refine ⟨85883024407836097126675957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114510699210448129502234609 85883024407836097126675957)
          ·
            refine ⟨8051533538234634105625871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85883024407836097126675957 8051533538234634105625871)
            ·
              refine ⟨12077300307351951158438807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051533538234634105625871 12077300307351951158438807)
              ·
                refine ⟨18115950461027926737658211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12077300307351951158438807 18115950461027926737658211)
                ·
                  refine ⟨27173925691541890106487317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18115950461027926737658211 27173925691541890106487317)
                  ·
                    refine ⟨1273777766791026098741593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27173925691541890106487317 1273777766791026098741593)
                    ·
                      rfl

theorem cell23_7442020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_7442020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442020 prefixEnd_7442020 := by exact prefixLift 7442020
  have htrace : WordTrace (prefixWord ++ tailWord_7442020) baseStart_7442020 baseEnd_7442020 := by
    simpa [prefixWord, tailWord_7442020, baseEnd_7442020] using wordTrace_append hprefix tailTrace_7442020
  have hstable : (prefixWord ++ tailWord_7442020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442020).length < 2 ^ (prefixWord ++ tailWord_7442020).sum := by decide
  have hdescent : baseEnd_7442020 < baseStart_7442020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442043 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 3]
def baseStart_7442043 : Nat := 118140960795 + 7442043 * 2 ^ 59
def prefixEnd_7442043 : Nat := 4983230072969 + 3 ^ 40 * 7442043 * 2
def baseEnd_7442043 : Nat := 3821345110428131706237173

theorem tailTrace_7442043 : CollatzResearch.WordTrace tailWord_7442043 prefixEnd_7442043 3821345110428131706237173 := by
  unfold tailWord_7442043
  simp only [CollatzResearch.WordTrace]
  refine ⟨271433607377756685600050783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180955738251837790400033855 271433607377756685600050783)
  ·
    refine ⟨407150411066635028400076175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271433607377756685600050783 407150411066635028400076175)
    ·
      refine ⟨610725616599952542600114263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407150411066635028400076175 610725616599952542600114263)
      ·
        refine ⟨916088424899928813900171395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610725616599952542600114263 916088424899928813900171395)
        ·
          refine ⟨1374132637349893220850257093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916088424899928813900171395 1374132637349893220850257093)
          ·
            refine ⟨257649869503104978909423205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1374132637349893220850257093 257649869503104978909423205)
            ·
              refine ⟨48309350531832183545516851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257649869503104978909423205 48309350531832183545516851)
              ·
                refine ⟨72464025797748275318275277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48309350531832183545516851 72464025797748275318275277)
                ·
                  refine ⟨27174009674155603244353229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72464025797748275318275277 27174009674155603244353229)
                  ·
                    refine ⟨10190253627808351216632461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27174009674155603244353229 10190253627808351216632461)
                    ·
                      refine ⟨3821345110428131706237173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10190253627808351216632461 3821345110428131706237173)
                      ·
                        rfl

theorem cell23_7442043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 3].length) (baseStart_7442043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442043 prefixEnd_7442043 := by exact prefixLift 7442043
  have htrace : WordTrace (prefixWord ++ tailWord_7442043) baseStart_7442043 baseEnd_7442043 := by
    simpa [prefixWord, tailWord_7442043, baseEnd_7442043] using wordTrace_append hprefix tailTrace_7442043
  have hstable : (prefixWord ++ tailWord_7442043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442043).length < 2 ^ (prefixWord ++ tailWord_7442043).sum := by decide
  have hdescent : baseEnd_7442043 < baseStart_7442043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442060 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 4, 1, 3]
def baseStart_7442060 : Nat := 118140960795 + 7442060 * 2 ^ 59
def prefixEnd_7442060 : Nat := 4983230072969 + 3 ^ 40 * 7442060 * 2
def baseEnd_7442060 : Nat := 3821353839599258139724595

theorem tailTrace_7442060 : CollatzResearch.WordTrace tailWord_7442060 prefixEnd_7442060 3821353839599258139724595 := by
  unfold tailWord_7442060
  simp only [CollatzResearch.WordTrace]
  refine ⟨135717113709347548751709817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180956151612463398335613089 135717113709347548751709817)
  ·
    refine ⟨101787835282010661563782363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135717113709347548751709817 101787835282010661563782363)
    ·
      refine ⟨152681752923015992345673545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101787835282010661563782363 152681752923015992345673545)
      ·
        refine ⟨114511314692261994259255159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152681752923015992345673545 114511314692261994259255159)
        ·
          refine ⟨171766972038392991388882739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114511314692261994259255159 171766972038392991388882739)
          ·
            refine ⟨257650458057589487083324109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171766972038392991388882739 257650458057589487083324109)
            ·
              refine ⟨96618921771596057656246541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257650458057589487083324109 96618921771596057656246541)
              ·
                refine ⟨36232095664348521621092453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96618921771596057656246541 36232095664348521621092453)
                ·
                  refine ⟨6793517937065347803954835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36232095664348521621092453 6793517937065347803954835)
                  ·
                    refine ⟨10190276905598021705932253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6793517937065347803954835 10190276905598021705932253)
                    ·
                      refine ⟨3821353839599258139724595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10190276905598021705932253 3821353839599258139724595)
                      ·
                        rfl

theorem cell23_7442060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_7442060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442060 prefixEnd_7442060 := by exact prefixLift 7442060
  have htrace : WordTrace (prefixWord ++ tailWord_7442060) baseStart_7442060 baseEnd_7442060 := by
    simpa [prefixWord, tailWord_7442060, baseEnd_7442060] using wordTrace_append hprefix tailTrace_7442060
  have hstable : (prefixWord ++ tailWord_7442060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442060).length < 2 ^ (prefixWord ++ tailWord_7442060).sum := by decide
  have hdescent : baseEnd_7442060 < baseStart_7442060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442094 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_7442094 : Nat := 118140960795 + 7442094 * 2 ^ 59
def prefixEnd_7442094 : Nat := 4983230072969 + 3 ^ 40 * 7442094 * 2
def baseEnd_7442094 : Nat := 3821371297941511006699439

theorem tailTrace_7442094 : CollatzResearch.WordTrace tailWord_7442094 prefixEnd_7442094 3821371297941511006699439 := by
  unfold tailWord_7442094
  simp only [CollatzResearch.WordTrace]
  refine ⟨33929433437571490163769667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180956978333714614206771557 33929433437571490163769667)
  ·
    refine ⟨50894150156357235245654501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33929433437571490163769667 50894150156357235245654501)
    ·
      refine ⟨9542653154316981608560219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50894150156357235245654501 9542653154316981608560219)
      ·
        refine ⟨14313979731475472412840329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9542653154316981608560219 14313979731475472412840329)
        ·
          refine ⟨10735484798606604309630247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14313979731475472412840329 10735484798606604309630247)
          ·
            refine ⟨16103227197909906464445371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10735484798606604309630247 16103227197909906464445371)
            ·
              refine ⟨24154840796864859696668057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16103227197909906464445371 24154840796864859696668057)
              ·
                refine ⟨18116130597648644772501043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24154840796864859696668057 18116130597648644772501043)
                ·
                  refine ⟨27174195896472967158751565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18116130597648644772501043 27174195896472967158751565)
                  ·
                    refine ⟨10190323461177362684531837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27174195896472967158751565 10190323461177362684531837)
                    ·
                      refine ⟨3821371297941511006699439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10190323461177362684531837 3821371297941511006699439)
                      ·
                        rfl

theorem cell23_7442094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_7442094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442094 prefixEnd_7442094 := by exact prefixLift 7442094
  have htrace : WordTrace (prefixWord ++ tailWord_7442094) baseStart_7442094 baseEnd_7442094 := by
    simpa [prefixWord, tailWord_7442094, baseEnd_7442094] using wordTrace_append hprefix tailTrace_7442094
  have hstable : (prefixWord ++ tailWord_7442094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442094).length < 2 ^ (prefixWord ++ tailWord_7442094).sum := by decide
  have hdescent : baseEnd_7442094 < baseStart_7442094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442130 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_7442130 : Nat := 118140960795 + 7442130 * 2 ^ 59
def prefixEnd_7442130 : Nat := 4983230072969 + 3 ^ 40 * 7442130 * 2
def baseEnd_7442130 : Nat := 3821389783245072865849273

theorem tailTrace_7442130 : CollatzResearch.WordTrace tailWord_7442130 prefixEnd_7442130 3821389783245072865849273 := by
  unfold tailWord_7442130
  simp only [CollatzResearch.WordTrace]
  refine ⟨67859195132110374864616961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180957853685627666305645229 67859195132110374864616961)
  ·
    refine ⟨50894396349082781148462721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67859195132110374864616961 50894396349082781148462721)
    ·
      refine ⟨38170797261812085861347041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50894396349082781148462721 38170797261812085861347041)
      ·
        refine ⟨28628097946359064396010281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38170797261812085861347041 28628097946359064396010281)
        ·
          refine ⟨21471073459769298297007711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28628097946359064396010281 21471073459769298297007711)
          ·
            refine ⟨32206610189653947445511567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21471073459769298297007711 32206610189653947445511567)
            ·
              refine ⟨48309915284480921168267351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32206610189653947445511567 48309915284480921168267351)
              ·
                refine ⟨72464872926721381752401027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48309915284480921168267351 72464872926721381752401027)
                ·
                  refine ⟨108697309390082072628601541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72464872926721381752401027 108697309390082072628601541)
                  ·
                    refine ⟨20380745510640388617862789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108697309390082072628601541 20380745510640388617862789)
                    ·
                      refine ⟨3821389783245072865849273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20380745510640388617862789 3821389783245072865849273)
                      ·
                        rfl

theorem cell23_7442130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_7442130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442130 prefixEnd_7442130 := by exact prefixLift 7442130
  have htrace : WordTrace (prefixWord ++ tailWord_7442130) baseStart_7442130 baseEnd_7442130 := by
    simpa [prefixWord, tailWord_7442130, baseEnd_7442130] using wordTrace_append hprefix tailTrace_7442130
  have hstable : (prefixWord ++ tailWord_7442130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442130).length < 2 ^ (prefixWord ++ tailWord_7442130).sum := by decide
  have hdescent : baseEnd_7442130 < baseStart_7442130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442157 : List Nat := [1, 5, 1, 2, 1, 2, 1, 5, 5]
def baseStart_7442157 : Nat := 118140960795 + 7442157 * 2 ^ 59
def prefixEnd_7442157 : Nat := 4983230072969 + 3 ^ 40 * 7442157 * 2
def baseEnd_7442157 : Nat := 424600405246971584467961

theorem tailTrace_7442157 : CollatzResearch.WordTrace tailWord_7442157 prefixEnd_7442157 424600405246971584467961 := by
  unfold tailWord_7442157
  simp only [CollatzResearch.WordTrace]
  refine ⟨271437765299343683069700725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180958510199562455379800483 271437765299343683069700725)
  ·
    refine ⟨25447290496813470287784443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271437765299343683069700725 25447290496813470287784443)
    ·
      refine ⟨38170935745220205431676665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25447290496813470287784443 38170935745220205431676665)
      ·
        refine ⟨28628201808915154073757499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38170935745220205431676665 28628201808915154073757499)
        ·
          refine ⟨42942302713372731110636249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28628201808915154073757499 42942302713372731110636249)
          ·
            refine ⟨32206727035029548332977187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42942302713372731110636249 32206727035029548332977187)
            ·
              refine ⟨48310090552544322499465781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32206727035029548332977187 48310090552544322499465781)
              ·
                refine ⟨4529070989301030234324917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48310090552544322499465781 4529070989301030234324917)
                ·
                  refine ⟨424600405246971584467961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4529070989301030234324917 424600405246971584467961)
                  ·
                    rfl

theorem cell23_7442157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_7442157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442157 prefixEnd_7442157 := by exact prefixLift 7442157
  have htrace : WordTrace (prefixWord ++ tailWord_7442157) baseStart_7442157 baseEnd_7442157 := by
    simpa [prefixWord, tailWord_7442157, baseEnd_7442157] using wordTrace_append hprefix tailTrace_7442157
  have hstable : (prefixWord ++ tailWord_7442157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442157).length < 2 ^ (prefixWord ++ tailWord_7442157).sum := by decide
  have hdescent : baseEnd_7442157 < baseStart_7442157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442160 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 1, 7, 2]
def baseStart_7442160 : Nat := 118140960795 + 7442160 * 2 ^ 59
def prefixEnd_7442160 : Nat := 4983230072969 + 3 ^ 40 * 7442160 * 2
def baseEnd_7442160 : Nat := 3821405187664707748474135

theorem tailTrace_7442160 : CollatzResearch.WordTrace tailWord_7442160 prefixEnd_7442160 3821405187664707748474135 := by
  unfold tailWord_7442160
  simp only [CollatzResearch.WordTrace]
  refine ⟨135718937359166407291029967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180958583145555209721373289 135718937359166407291029967)
  ·
    refine ⟨203578406038749610936544951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135718937359166407291029967 203578406038749610936544951)
    ·
      refine ⟨305367609058124416404817427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203578406038749610936544951 305367609058124416404817427)
      ·
        refine ⟨458051413587186624607226141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305367609058124416404817427 458051413587186624607226141)
        ·
          refine ⟨171769280095194984227709803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458051413587186624607226141 171769280095194984227709803)
          ·
            refine ⟨257653920142792476341564705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171769280095194984227709803 257653920142792476341564705)
            ·
              refine ⟨193240440107094357256173529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257653920142792476341564705 193240440107094357256173529)
              ·
                refine ⟨144930330080320767942130147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193240440107094357256173529 144930330080320767942130147)
                ·
                  refine ⟨217395495120481151913195221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144930330080320767942130147 217395495120481151913195221)
                  ·
                    refine ⟨5095206916886276997965513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 217395495120481151913195221 5095206916886276997965513)
                    ·
                      refine ⟨3821405187664707748474135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095206916886276997965513 3821405187664707748474135)
                      ·
                        rfl

theorem cell23_7442160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 7, 2].length) (baseStart_7442160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442160 prefixEnd_7442160 := by exact prefixLift 7442160
  have htrace : WordTrace (prefixWord ++ tailWord_7442160) baseStart_7442160 baseEnd_7442160 := by
    simpa [prefixWord, tailWord_7442160, baseEnd_7442160] using wordTrace_append hprefix tailTrace_7442160
  have hstable : (prefixWord ++ tailWord_7442160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442160).length < 2 ^ (prefixWord ++ tailWord_7442160).sum := by decide
  have hdescent : baseEnd_7442160 < baseStart_7442160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442163 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 5]
def baseStart_7442163 : Nat := 118140960795 + 7442163 * 2 ^ 59
def prefixEnd_7442163 : Nat := 4983230072969 + 3 ^ 40 * 7442163 * 2
def baseEnd_7442163 : Nat := 3821406728106671236736621

theorem tailTrace_7442163 : CollatzResearch.WordTrace tailWord_7442163 prefixEnd_7442163 3821406728106671236736621 := by
  unfold tailWord_7442163
  simp only [CollatzResearch.WordTrace]
  refine ⟨271437984137321946094419143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180958656091547964062946095 271437984137321946094419143)
  ·
    refine ⟨407156976205982919141628715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271437984137321946094419143 407156976205982919141628715)
    ·
      refine ⟨610735464308974378712443073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407156976205982919141628715 610735464308974378712443073)
      ·
        refine ⟨458051598231730784034332305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610735464308974378712443073 458051598231730784034332305)
        ·
          refine ⟨343538698673798088025749229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458051598231730784034332305 343538698673798088025749229)
          ·
            refine ⟨128827012002674283009655961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343538698673798088025749229 128827012002674283009655961)
            ·
              refine ⟨96620259002005712257241971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128827012002674283009655961 96620259002005712257241971)
              ·
                refine ⟨144930388503008568385862957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96620259002005712257241971 144930388503008568385862957)
                ·
                  refine ⟨54348895688628213144698609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144930388503008568385862957 54348895688628213144698609)
                  ·
                    refine ⟨40761671766471159858523957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54348895688628213144698609 40761671766471159858523957)
                    ·
                      refine ⟨3821406728106671236736621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40761671766471159858523957 3821406728106671236736621)
                      ·
                        rfl

theorem cell23_7442163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_7442163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442163 prefixEnd_7442163 := by exact prefixLift 7442163
  have htrace : WordTrace (prefixWord ++ tailWord_7442163) baseStart_7442163 baseEnd_7442163 := by
    simpa [prefixWord, tailWord_7442163, baseEnd_7442163] using wordTrace_append hprefix tailTrace_7442163
  have hstable : (prefixWord ++ tailWord_7442163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442163).length < 2 ^ (prefixWord ++ tailWord_7442163).sum := by decide
  have hdescent : baseEnd_7442163 < baseStart_7442163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442164 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7442164 : Nat := 118140960795 + 7442164 * 2 ^ 59
def prefixEnd_7442164 : Nat := 4983230072969 + 3 ^ 40 * 7442164 * 2
def baseEnd_7442164 : Nat := 3821407241587325732824117

theorem tailTrace_7442164 : CollatzResearch.WordTrace tailWord_7442164 prefixEnd_7442164 3821407241587325732824117 := by
  unfold tailWord_7442164
  simp only [CollatzResearch.WordTrace]
  refine ⟨135719010305159161632602773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180958680406878882176803697 135719010305159161632602773)
  ·
    refine ⟨6361828608054335701528255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135719010305159161632602773 6361828608054335701528255)
    ·
      refine ⟨9542742912081503552292383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6361828608054335701528255 9542742912081503552292383)
      ·
        refine ⟨14314114368122255328438575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9542742912081503552292383 14314114368122255328438575)
        ·
          refine ⟨21471171552183382992657863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14314114368122255328438575 21471171552183382992657863)
          ·
            refine ⟨32206757328275074488986795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21471171552183382992657863 32206757328275074488986795)
            ·
              refine ⟨48310135992412611733480193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32206757328275074488986795 48310135992412611733480193)
              ·
                refine ⟨36232601994309458800110145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48310135992412611733480193 36232601994309458800110145)
                ·
                  refine ⟨27174451495732094100082609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36232601994309458800110145 27174451495732094100082609)
                  ·
                    refine ⟨20380838621799070575061957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27174451495732094100082609 20380838621799070575061957)
                    ·
                      refine ⟨3821407241587325732824117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20380838621799070575061957 3821407241587325732824117)
                      ·
                        rfl

theorem cell23_7442164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7442164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442164 prefixEnd_7442164 := by exact prefixLift 7442164
  have htrace : WordTrace (prefixWord ++ tailWord_7442164) baseStart_7442164 baseEnd_7442164 := by
    simpa [prefixWord, tailWord_7442164, baseEnd_7442164] using wordTrace_append hprefix tailTrace_7442164
  have hstable : (prefixWord ++ tailWord_7442164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442164).length < 2 ^ (prefixWord ++ tailWord_7442164).sum := by decide
  have hdescent : baseEnd_7442164 < baseStart_7442164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442190 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7442190 : Nat := 118140960795 + 7442190 * 2 ^ 59
def prefixEnd_7442190 : Nat := 4983230072969 + 3 ^ 40 * 7442190 * 2
def baseEnd_7442190 : Nat := 3821420592084342631098997

theorem tailTrace_7442190 : CollatzResearch.WordTrace tailWord_7442190 prefixEnd_7442190 3821420592084342631098997 := by
  unfold tailWord_7442190
  simp only [CollatzResearch.WordTrace]
  refine ⟨33929871113528016213206503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180959312605482753137101349 33929871113528016213206503)
  ·
    refine ⟨50894806670292024319809755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33929871113528016213206503 50894806670292024319809755)
    ·
      refine ⟨76342210005438036479714633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50894806670292024319809755 76342210005438036479714633)
      ·
        refine ⟨57256657504078527359785975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76342210005438036479714633 57256657504078527359785975)
        ·
          refine ⟨85884986256117791039678963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57256657504078527359785975 85884986256117791039678963)
          ·
            refine ⟨128827479384176686559518445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85884986256117791039678963 128827479384176686559518445)
            ·
              refine ⟨48310304769066257459819417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128827479384176686559518445 48310304769066257459819417)
              ·
                refine ⟨36232728576799693094864563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48310304769066257459819417 36232728576799693094864563)
                ·
                  refine ⟨54349092865199539642296845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36232728576799693094864563 54349092865199539642296845)
                  ·
                    refine ⟨20380909824449827365861317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54349092865199539642296845 20380909824449827365861317)
                    ·
                      refine ⟨3821420592084342631098997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20380909824449827365861317 3821420592084342631098997)
                      ·
                        rfl

theorem cell23_7442190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7442190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442190 prefixEnd_7442190 := by exact prefixLift 7442190
  have htrace : WordTrace (prefixWord ++ tailWord_7442190) baseStart_7442190 baseEnd_7442190 := by
    simpa [prefixWord, tailWord_7442190, baseEnd_7442190] using wordTrace_append hprefix tailTrace_7442190
  have hstable : (prefixWord ++ tailWord_7442190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442190).length < 2 ^ (prefixWord ++ tailWord_7442190).sum := by decide
  have hdescent : baseEnd_7442190 < baseStart_7442190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442203 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 6]
def baseStart_7442203 : Nat := 118140960795 + 7442203 * 2 ^ 59
def prefixEnd_7442203 : Nat := 4983230072969 + 3 ^ 40 * 7442203 * 2
def baseEnd_7442203 : Nat := 3821427267332851080236437

theorem tailTrace_7442203 : CollatzResearch.WordTrace tailWord_7442203 prefixEnd_7442203 3821427267332851080236437 := by
  unfold tailWord_7442203
  simp only [CollatzResearch.WordTrace]
  refine ⟨271439443057177032925875263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180959628704784688617250175 271439443057177032925875263)
  ·
    refine ⟨407159164585765549388812895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271439443057177032925875263 407159164585765549388812895)
    ·
      refine ⟨610738746878648324083219343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407159164585765549388812895 610738746878648324083219343)
      ·
        refine ⟨916108120317972486124829015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610738746878648324083219343 916108120317972486124829015)
        ·
          refine ⟨1374162180476958729187243523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916108120317972486124829015 1374162180476958729187243523)
          ·
            refine ⟨2061243270715438093780865285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374162180476958729187243523 2061243270715438093780865285)
            ·
              refine ⟨386483113259144642583912241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2061243270715438093780865285 386483113259144642583912241)
              ·
                refine ⟨289862334944358481937934181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386483113259144642583912241 289862334944358481937934181)
                ·
                  refine ⟨54349187802067215363362659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289862334944358481937934181 54349187802067215363362659)
                  ·
                    refine ⟨81523781703100823045043989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54349187802067215363362659 81523781703100823045043989)
                    ·
                      refine ⟨3821427267332851080236437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81523781703100823045043989 3821427267332851080236437)
                      ·
                        rfl

theorem cell23_7442203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_7442203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442203 prefixEnd_7442203 := by exact prefixLift 7442203
  have htrace : WordTrace (prefixWord ++ tailWord_7442203) baseStart_7442203 baseEnd_7442203 := by
    simpa [prefixWord, tailWord_7442203, baseEnd_7442203] using wordTrace_append hprefix tailTrace_7442203
  have hstable : (prefixWord ++ tailWord_7442203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442203).length < 2 ^ (prefixWord ++ tailWord_7442203).sum := by decide
  have hdescent : baseEnd_7442203 < baseStart_7442203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442234 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 3, 4]
def baseStart_7442234 : Nat := 118140960795 + 7442234 * 2 ^ 59
def prefixEnd_7442234 : Nat := 4983230072969 + 3 ^ 40 * 7442234 * 2
def baseEnd_7442234 : Nat := 1273814395077713486316265

theorem tailTrace_7442234 : CollatzResearch.WordTrace tailWord_7442234 prefixEnd_7442234 1273814395077713486316265 := by
  unfold tailWord_7442234
  simp only [CollatzResearch.WordTrace]
  refine ⟨67860143430016181305063439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180960382480043150146835837 67860143430016181305063439)
  ·
    refine ⟨101790215145024271957595159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67860143430016181305063439 101790215145024271957595159)
    ·
      refine ⟨152685322717536407936392739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101790215145024271957595159 152685322717536407936392739)
      ·
        refine ⟨229027984076304611904589109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152685322717536407936392739 229027984076304611904589109)
        ·
          refine ⟨21471373507153557366055229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229027984076304611904589109 21471373507153557366055229)
          ·
            refine ⟨8051765065182584012270711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21471373507153557366055229 8051765065182584012270711)
            ·
              refine ⟨12077647597773876018406067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051765065182584012270711 12077647597773876018406067)
              ·
                refine ⟨18116471396660814027609101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12077647597773876018406067 18116471396660814027609101)
                ·
                  refine ⟨6793676773747805260353413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18116471396660814027609101 6793676773747805260353413)
                  ·
                    refine ⟨1273814395077713486316265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6793676773747805260353413 1273814395077713486316265)
                    ·
                      rfl

theorem cell23_7442234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_7442234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442234 prefixEnd_7442234 := by exact prefixLift 7442234
  have htrace : WordTrace (prefixWord ++ tailWord_7442234) baseStart_7442234 baseEnd_7442234 := by
    simpa [prefixWord, tailWord_7442234, baseEnd_7442234] using wordTrace_append hprefix tailTrace_7442234
  have hstable : (prefixWord ++ tailWord_7442234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442234).length < 2 ^ (prefixWord ++ tailWord_7442234).sum := by decide
  have hdescent : baseEnd_7442234 < baseStart_7442234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442247 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 6]
def baseStart_7442247 : Nat := 118140960795 + 7442247 * 2 ^ 59
def prefixEnd_7442247 : Nat := 4983230072969 + 3 ^ 40 * 7442247 * 2
def baseEnd_7442247 : Nat := 424605540053516545342915

theorem tailTrace_7442247 : CollatzResearch.WordTrace tailWord_7442247 prefixEnd_7442247 424605540053516545342915 := by
  unfold tailWord_7442247
  simp only [CollatzResearch.WordTrace]
  refine ⟨271441047869017628440476995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180960698579345085626984663 271441047869017628440476995)
  ·
    refine ⟨407161571803526442660715493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271441047869017628440476995 407161571803526442660715493)
    ·
      refine ⟨76342794713161207998884155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407161571803526442660715493 76342794713161207998884155)
      ·
        refine ⟨114514192069741811998326233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76342794713161207998884155 114514192069741811998326233)
        ·
          refine ⟨85885644052306358998744675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114514192069741811998326233 85885644052306358998744675)
          ·
            refine ⟨128828466078459538498117013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85885644052306358998744675 128828466078459538498117013)
            ·
              refine ⟨6038834347427790867099235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128828466078459538498117013 6038834347427790867099235)
              ·
                refine ⟨9058251521141686300648853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6038834347427790867099235 9058251521141686300648853)
                ·
                  refine ⟨424605540053516545342915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9058251521141686300648853 424605540053516545342915)
                  ·
                    rfl

theorem cell23_7442247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 6].length) (baseStart_7442247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442247 prefixEnd_7442247 := by exact prefixLift 7442247
  have htrace : WordTrace (prefixWord ++ tailWord_7442247) baseStart_7442247 baseEnd_7442247 := by
    simpa [prefixWord, tailWord_7442247, baseEnd_7442247] using wordTrace_append hprefix tailTrace_7442247
  have hstable : (prefixWord ++ tailWord_7442247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442247).length < 2 ^ (prefixWord ++ tailWord_7442247).sum := by decide
  have hdescent : baseEnd_7442247 < baseStart_7442247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442284 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 2, 3, 2]
def baseStart_7442284 : Nat := 118140960795 + 7442284 * 2 ^ 59
def prefixEnd_7442284 : Nat := 4983230072969 + 3 ^ 40 * 7442284 * 2
def baseEnd_7442284 : Nat := 3821468859265865263323565

theorem tailTrace_7442284 : CollatzResearch.WordTrace tailWord_7442284 prefixEnd_7442284 3821468859265865263323565 := by
  unfold tailWord_7442284
  simp only [CollatzResearch.WordTrace]
  refine ⟨135721198684941791879786953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180961598246589055839715937 135721198684941791879786953)
  ·
    refine ⟨101790899013706343909840215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135721198684941791879786953 101790899013706343909840215)
    ·
      refine ⟨152686348520559515864760323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101790899013706343909840215 152686348520559515864760323)
      ·
        refine ⟨229029522780839273797140485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152686348520559515864760323 229029522780839273797140485)
        ·
          refine ⟨42943035521407363836963841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229029522780839273797140485 42943035521407363836963841)
          ·
            refine ⟨32207276641055522877722881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42943035521407363836963841 32207276641055522877722881)
            ·
              refine ⟨24155457480791642158292161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32207276641055522877722881 24155457480791642158292161)
              ·
                refine ⟨18116593110593731618719121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24155457480791642158292161 18116593110593731618719121)
                ·
                  refine ⟨13587444832945298714039341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18116593110593731618719121 13587444832945298714039341)
                  ·
                    refine ⟨5095291812354487017764753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13587444832945298714039341 5095291812354487017764753)
                    ·
                      refine ⟨3821468859265865263323565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095291812354487017764753 3821468859265865263323565)
                      ·
                        rfl

theorem cell23_7442284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 3, 2].length) (baseStart_7442284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442284 prefixEnd_7442284 := by exact prefixLift 7442284
  have htrace : WordTrace (prefixWord ++ tailWord_7442284) baseStart_7442284 baseEnd_7442284 := by
    simpa [prefixWord, tailWord_7442284, baseEnd_7442284] using wordTrace_append hprefix tailTrace_7442284
  have hstable : (prefixWord ++ tailWord_7442284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442284).length < 2 ^ (prefixWord ++ tailWord_7442284).sum := by decide
  have hdescent : baseEnd_7442284 < baseStart_7442284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442290 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_7442290 : Nat := 118140960795 + 7442290 * 2 ^ 59
def prefixEnd_7442290 : Nat := 4983230072969 + 3 ^ 40 * 7442290 * 2
def baseEnd_7442290 : Nat := 1273823980049930746616179

theorem tailTrace_7442290 : CollatzResearch.WordTrace tailWord_7442290 prefixEnd_7442290 1273823980049930746616179 := by
  unfold tailWord_7442290
  simp only [CollatzResearch.WordTrace]
  refine ⟨67860654051965461696073081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180961744138574564522861549 67860654051965461696073081)
  ·
    refine ⟨50895490538974096272054811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67860654051965461696073081 50895490538974096272054811)
    ·
      refine ⟨76343235808461144408082217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50895490538974096272054811 76343235808461144408082217)
      ·
        refine ⟨57257426856345858306061663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76343235808461144408082217 57257426856345858306061663)
        ·
          refine ⟨85886140284518787459092495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57257426856345858306061663 85886140284518787459092495)
          ·
            refine ⟨128829210426778181188638743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85886140284518787459092495 128829210426778181188638743)
            ·
              refine ⟨193243815640167271782958115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128829210426778181188638743 193243815640167271782958115)
              ·
                refine ⟨289865723460250907674437173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193243815640167271782958115 289865723460250907674437173)
                ·
                  refine ⟨27174911574398522594478485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289865723460250907674437173 27174911574398522594478485)
                  ·
                    refine ⟨1273823980049930746616179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27174911574398522594478485 1273823980049930746616179)
                    ·
                      rfl

theorem cell23_7442290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_7442290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442290 prefixEnd_7442290 := by exact prefixLift 7442290
  have htrace : WordTrace (prefixWord ++ tailWord_7442290) baseStart_7442290 baseEnd_7442290 := by
    simpa [prefixWord, tailWord_7442290, baseEnd_7442290] using wordTrace_append hprefix tailTrace_7442290
  have hstable : (prefixWord ++ tailWord_7442290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442290).length < 2 ^ (prefixWord ++ tailWord_7442290).sum := by decide
  have hdescent : baseEnd_7442290 < baseStart_7442290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442307 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 1, 6]
def baseStart_7442307 : Nat := 118140960795 + 7442307 * 2 ^ 59
def prefixEnd_7442307 : Nat := 4983230072969 + 3 ^ 40 * 7442307 * 2
def baseEnd_7442307 : Nat := 1273826889773639557778653

theorem tailTrace_7442307 : CollatzResearch.WordTrace tailWord_7442307 prefixEnd_7442307 1273826889773639557778653 := by
  unfold tailWord_7442307
  simp only [CollatzResearch.WordTrace]
  refine ⟨271443236248800258687661175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180962157499200172458440783 271443236248800258687661175)
  ·
    refine ⟨407164854373200388031491763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271443236248800258687661175 407164854373200388031491763)
    ·
      refine ⟨610747281559800582047237645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407164854373200388031491763 610747281559800582047237645)
      ·
        refine ⟨229030230584925218267714117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 610747281559800582047237645 229030230584925218267714117)
        ·
          refine ⟨42943168234673478425196397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229030230584925218267714117 42943168234673478425196397)
          ·
            refine ⟨16103688088002554409448649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42943168234673478425196397 16103688088002554409448649)
            ·
              refine ⟨12077766066001915807086487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16103688088002554409448649 12077766066001915807086487)
              ·
                refine ⟨18116649099002873710629731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12077766066001915807086487 18116649099002873710629731)
                ·
                  refine ⟨27174973648504310565944597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18116649099002873710629731 27174973648504310565944597)
                  ·
                    refine ⟨1273826889773639557778653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27174973648504310565944597 1273826889773639557778653)
                    ·
                      rfl

theorem cell23_7442307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 6].length) (baseStart_7442307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442307 prefixEnd_7442307 := by exact prefixLift 7442307
  have htrace : WordTrace (prefixWord ++ tailWord_7442307) baseStart_7442307 baseEnd_7442307 := by
    simpa [prefixWord, tailWord_7442307, baseEnd_7442307] using wordTrace_append hprefix tailTrace_7442307
  have hstable : (prefixWord ++ tailWord_7442307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442307).length < 2 ^ (prefixWord ++ tailWord_7442307).sum := by decide
  have hdescent : baseEnd_7442307 < baseStart_7442307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442327 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_7442327 : Nat := 118140960795 + 7442327 * 2 ^ 59
def prefixEnd_7442327 : Nat := 4983230072969 + 3 ^ 40 * 7442327 * 2
def baseEnd_7442327 : Nat := 3821490938934008595085867

theorem tailTrace_7442327 : CollatzResearch.WordTrace tailWord_7442327 prefixEnd_7442327 3821490938934008595085867 := by
  unfold tailWord_7442327
  simp only [CollatzResearch.WordTrace]
  refine ⟨271443965708727802103389235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180962643805818534735592823 271443965708727802103389235)
  ·
    refine ⟨407165948563091703155083853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271443965708727802103389235 407165948563091703155083853)
    ·
      refine ⟨152687230711159388683156445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407165948563091703155083853 152687230711159388683156445)
      ·
        refine ⟨57257711516684770756183667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152687230711159388683156445 57257711516684770756183667)
        ·
          refine ⟨85886567275027156134275501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57257711516684770756183667 85886567275027156134275501)
          ·
            refine ⟨32207462728135183550353313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85886567275027156134275501 32207462728135183550353313)
            ·
              refine ⟨24155597046101387662764985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32207462728135183550353313 24155597046101387662764985)
              ·
                refine ⟨18116697784576040747073739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24155597046101387662764985 18116697784576040747073739)
                ·
                  refine ⟨27175046676864061120610609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18116697784576040747073739 27175046676864061120610609)
                  ·
                    refine ⟨20381285007648045840457957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27175046676864061120610609 20381285007648045840457957)
                    ·
                      refine ⟨3821490938934008595085867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20381285007648045840457957 3821490938934008595085867)
                      ·
                        rfl

theorem cell23_7442327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_7442327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442327 prefixEnd_7442327 := by exact prefixLift 7442327
  have htrace : WordTrace (prefixWord ++ tailWord_7442327) baseStart_7442327 baseEnd_7442327 := by
    simpa [prefixWord, tailWord_7442327, baseEnd_7442327] using wordTrace_append hprefix tailTrace_7442327
  have hstable : (prefixWord ++ tailWord_7442327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442327).length < 2 ^ (prefixWord ++ tailWord_7442327).sum := by decide
  have hdescent : baseEnd_7442327 < baseStart_7442327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442328 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 1, 5]
def baseStart_7442328 : Nat := 118140960795 + 7442328 * 2 ^ 59
def prefixEnd_7442328 : Nat := 4983230072969 + 3 ^ 40 * 7442328 * 2
def baseEnd_7442328 : Nat := 1273830484138221030391121

theorem tailTrace_7442328 : CollatzResearch.WordTrace tailWord_7442328 prefixEnd_7442328 1273830484138221030391121 := by
  unfold tailWord_7442328
  simp only [CollatzResearch.WordTrace]
  refine ⟨135722001090862089637087819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180962668121149452849450425 135722001090862089637087819)
  ·
    refine ⟨203583001636293134455631729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135722001090862089637087819 203583001636293134455631729)
    ·
      refine ⟨152687251227219850841723797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203583001636293134455631729 152687251227219850841723797)
      ·
        refine ⟨7157214901275930508205803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152687251227219850841723797 7157214901275930508205803)
        ·
          refine ⟨10735822351913895762308705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7157214901275930508205803 10735822351913895762308705)
          ·
            refine ⟨8051866763935421821731529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10735822351913895762308705 8051866763935421821731529)
            ·
              refine ⟨6038900072951566366298647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8051866763935421821731529 6038900072951566366298647)
              ·
                refine ⟨9058350109427349549447971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6038900072951566366298647 9058350109427349549447971)
                ·
                  refine ⟨13587525164141024324171957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9058350109427349549447971 13587525164141024324171957)
                  ·
                    refine ⟨1273830484138221030391121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13587525164141024324171957 1273830484138221030391121)
                    ·
                      rfl

theorem cell23_7442328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_7442328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442328 prefixEnd_7442328 := by exact prefixLift 7442328
  have htrace : WordTrace (prefixWord ++ tailWord_7442328) baseStart_7442328 baseEnd_7442328 := by
    simpa [prefixWord, tailWord_7442328, baseEnd_7442328] using wordTrace_append hprefix tailTrace_7442328
  have hstable : (prefixWord ++ tailWord_7442328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442328).length < 2 ^ (prefixWord ++ tailWord_7442328).sum := by decide
  have hdescent : baseEnd_7442328 < baseStart_7442328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442337 : List Nat := [1, 2, 3, 4, 2, 1, 10]
def baseStart_7442337 : Nat := 118140960795 + 7442337 * 2 ^ 59
def prefixEnd_7442337 : Nat := 4983230072969 + 3 ^ 40 * 7442337 * 2
def baseEnd_7442337 : Nat := 47178963873340167357541

theorem tailTrace_7442337 : CollatzResearch.WordTrace tailWord_7442337 prefixEnd_7442337 47178963873340167357541 := by
  unfold tailWord_7442337
  simp only [CollatzResearch.WordTrace]
  refine ⟨271444330438691573811253265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180962886959127715874168843 271444330438691573811253265)
  ·
    refine ⟨203583247829018680358439949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271444330438691573811253265 203583247829018680358439949)
    ·
      refine ⟨76343717935882005134414981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203583247829018680358439949 76343717935882005134414981)
      ·
        refine ⟨14314447112977875962702809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76343717935882005134414981 14314447112977875962702809)
        ·
          refine ⟨10735835334733406972027107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14314447112977875962702809 10735835334733406972027107)
          ·
            refine ⟨16103753002100110458040661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10735835334733406972027107 16103753002100110458040661)
            ·
              refine ⟨47178963873340167357541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16103753002100110458040661 47178963873340167357541)
              ·
                rfl

theorem cell23_7442337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 10].length) (baseStart_7442337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442337 prefixEnd_7442337 := by exact prefixLift 7442337
  have htrace : WordTrace (prefixWord ++ tailWord_7442337) baseStart_7442337 baseEnd_7442337 := by
    simpa [prefixWord, tailWord_7442337, baseEnd_7442337] using wordTrace_append hprefix tailTrace_7442337
  have hstable : (prefixWord ++ tailWord_7442337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442337).length < 2 ^ (prefixWord ++ tailWord_7442337).sum := by decide
  have hdescent : baseEnd_7442337 < baseStart_7442337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442444 : List Nat := [2, 2, 1, 2, 3, 1, 2, 5, 5]
def baseStart_7442444 : Nat := 118140960795 + 7442444 * 2 ^ 59
def prefixEnd_7442444 : Nat := 4983230072969 + 3 ^ 40 * 7442444 * 2
def baseEnd_7442444 : Nat := 424616779574509404146981

theorem tailTrace_7442444 : CollatzResearch.WordTrace tailWord_7442444 prefixEnd_7442444 424616779574509404146981 := by
  unfold tailWord_7442444
  simp only [CollatzResearch.WordTrace]
  refine ⟨135724116524651965542699193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180965488699535954056932257 135724116524651965542699193)
  ·
    refine ⟨101793087393488974157024395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135724116524651965542699193 101793087393488974157024395)
    ·
      refine ⟨152689631090233461235536593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101793087393488974157024395 152689631090233461235536593)
      ·
        refine ⟨114517223317675095926652445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152689631090233461235536593 114517223317675095926652445)
        ·
          refine ⟨42943958744128160972494667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114517223317675095926652445 42943958744128160972494667)
          ·
            refine ⟨64415938116192241458742001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42943958744128160972494667 64415938116192241458742001)
            ·
              refine ⟨48311953587144181094056501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64415938116192241458742001 48311953587144181094056501)
              ·
                refine ⟨4529245648794766977567797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48311953587144181094056501 4529245648794766977567797)
                ·
                  refine ⟨424616779574509404146981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4529245648794766977567797 424616779574509404146981)
                  ·
                    rfl

theorem cell23_7442444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_7442444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442444 prefixEnd_7442444 := by exact prefixLift 7442444
  have htrace : WordTrace (prefixWord ++ tailWord_7442444) baseStart_7442444 baseEnd_7442444 := by
    simpa [prefixWord, tailWord_7442444, baseEnd_7442444] using wordTrace_append hprefix tailTrace_7442444
  have hstable : (prefixWord ++ tailWord_7442444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442444).length < 2 ^ (prefixWord ++ tailWord_7442444).sum := by decide
  have hdescent : baseEnd_7442444 < baseStart_7442444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442455 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 2, 2, 2]
def baseStart_7442455 : Nat := 118140960795 + 7442455 * 2 ^ 59
def prefixEnd_7442455 : Nat := 4983230072969 + 3 ^ 40 * 7442455 * 2
def baseEnd_7442455 : Nat := 3821556664457784094285279

theorem tailTrace_7442455 : CollatzResearch.WordTrace tailWord_7442455 prefixEnd_7442455 3821556664457784094285279 := by
  unfold tailWord_7442455
  simp only [CollatzResearch.WordTrace]
  refine ⟨271448634252264079964048819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180965756168176053309365879 271448634252264079964048819)
  ·
    refine ⟨407172951378396119946073229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271448634252264079964048819 407172951378396119946073229)
    ·
      refine ⟨152689856766898544979777461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407172951378396119946073229 152689856766898544979777461)
      ·
        refine ⟨14314674071896738591854137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152689856766898544979777461 14314674071896738591854137)
        ·
          refine ⟨10736005553922553943890603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14314674071896738591854137 10736005553922553943890603)
          ·
            refine ⟨16104008330883830915835905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10736005553922553943890603 16104008330883830915835905)
            ·
              refine ⟨12078006248162873186876929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16104008330883830915835905 12078006248162873186876929)
              ·
                refine ⟨9058504686122154890157697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12078006248162873186876929 9058504686122154890157697)
                ·
                  refine ⟨6793878514591616167618273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9058504686122154890157697 6793878514591616167618273)
                  ·
                    refine ⟨5095408885943712125713705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6793878514591616167618273 5095408885943712125713705)
                    ·
                      refine ⟨3821556664457784094285279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095408885943712125713705 3821556664457784094285279)
                      ·
                        rfl

theorem cell23_7442455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_7442455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442455 prefixEnd_7442455 := by exact prefixLift 7442455
  have htrace : WordTrace (prefixWord ++ tailWord_7442455) baseStart_7442455 baseEnd_7442455 := by
    simpa [prefixWord, tailWord_7442455, baseEnd_7442455] using wordTrace_append hprefix tailTrace_7442455
  have hstable : (prefixWord ++ tailWord_7442455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442455).length < 2 ^ (prefixWord ++ tailWord_7442455).sum := by decide
  have hdescent : baseEnd_7442455 < baseStart_7442455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442461 : List Nat := [1, 4, 2, 2, 2, 2, 1, 4, 5]
def baseStart_7442461 : Nat := 118140960795 + 7442461 * 2 ^ 59
def prefixEnd_7442461 : Nat := 4983230072969 + 3 ^ 40 * 7442461 * 2
def baseEnd_7442461 : Nat := 424617749482412341201139

theorem tailTrace_7442461 : CollatzResearch.WordTrace tailWord_7442461 prefixEnd_7442461 424617749482412341201139 := by
  unfold tailWord_7442461
  simp only [CollatzResearch.WordTrace]
  refine ⟨271448853090242342988767237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180965902060161561992511491 271448853090242342988767237)
  ·
    refine ⟨50896659954420439310393857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271448853090242342988767237 50896659954420439310393857)
    ·
      refine ⟨38172494965815329482795393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50896659954420439310393857 38172494965815329482795393)
      ·
        refine ⟨28629371224361497112096545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38172494965815329482795393 28629371224361497112096545)
        ·
          refine ⟨21472028418271122834072409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28629371224361497112096545 21472028418271122834072409)
          ·
            refine ⟨16104021313703342125554307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21472028418271122834072409 16104021313703342125554307)
            ·
              refine ⟨24156031970555013188331461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16104021313703342125554307 24156031970555013188331461)
              ·
                refine ⟨4529255994479064972812149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24156031970555013188331461 4529255994479064972812149)
                ·
                  refine ⟨424617749482412341201139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4529255994479064972812149 424617749482412341201139)
                  ·
                    rfl

theorem cell23_7442461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_7442461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442461 prefixEnd_7442461 := by exact prefixLift 7442461
  have htrace : WordTrace (prefixWord ++ tailWord_7442461) baseStart_7442461 baseEnd_7442461 := by
    simpa [prefixWord, tailWord_7442461, baseEnd_7442461] using wordTrace_append hprefix tailTrace_7442461
  have hstable : (prefixWord ++ tailWord_7442461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442461).length < 2 ^ (prefixWord ++ tailWord_7442461).sum := by decide
  have hdescent : baseEnd_7442461 < baseStart_7442461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442467 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 5]
def baseStart_7442467 : Nat := 118140960795 + 7442467 * 2 ^ 59
def prefixEnd_7442467 : Nat := 4983230072969 + 3 ^ 40 * 7442467 * 2
def baseEnd_7442467 : Nat := 3821562826225638047335223

theorem tailTrace_7442467 : CollatzResearch.WordTrace tailWord_7442467 prefixEnd_7442467 3821562826225638047335223 := by
  unfold tailWord_7442467
  simp only [CollatzResearch.WordTrace]
  refine ⟨271449071928220606013485655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180966047952147070675657103 271449071928220606013485655)
  ·
    refine ⟨407173607892330909020228483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271449071928220606013485655 407173607892330909020228483)
    ·
      refine ⟨610760411838496363530342725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407173607892330909020228483 610760411838496363530342725)
      ·
        refine ⟨114517577219718068161939261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 610760411838496363530342725 114517577219718068161939261)
        ·
          refine ⟨42944091457394275560727223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114517577219718068161939261 42944091457394275560727223)
          ·
            refine ⟨64416137186091413341090835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42944091457394275560727223 64416137186091413341090835)
            ·
              refine ⟨96624205779137120011636253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64416137186091413341090835 96624205779137120011636253)
              ·
                refine ⟨36234077167176420004363595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96624205779137120011636253 36234077167176420004363595)
                ·
                  refine ⟨54351115750764630006545393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36234077167176420004363595 54351115750764630006545393)
                  ·
                    refine ⟨40763336813073472504909045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54351115750764630006545393 40763336813073472504909045)
                    ·
                      refine ⟨3821562826225638047335223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40763336813073472504909045 3821562826225638047335223)
                      ·
                        rfl

theorem cell23_7442467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_7442467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442467 prefixEnd_7442467 := by exact prefixLift 7442467
  have htrace : WordTrace (prefixWord ++ tailWord_7442467) baseStart_7442467 baseEnd_7442467 := by
    simpa [prefixWord, tailWord_7442467, baseEnd_7442467] using wordTrace_append hprefix tailTrace_7442467
  have hstable : (prefixWord ++ tailWord_7442467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442467).length < 2 ^ (prefixWord ++ tailWord_7442467).sum := by decide
  have hdescent : baseEnd_7442467 < baseStart_7442467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442521 : List Nat := [1, 2, 1, 2, 2, 1, 3, 6, 1, 4]
def baseStart_7442521 : Nat := 118140960795 + 7442521 * 2 ^ 59
def prefixEnd_7442521 : Nat := 4983230072969 + 3 ^ 40 * 7442521 * 2
def baseEnd_7442521 : Nat := 1273863518060326945353325

theorem tailTrace_7442521 : CollatzResearch.WordTrace tailWord_7442521 prefixEnd_7442521 1273863518060326945353325 := by
  unfold tailWord_7442521
  simp only [CollatzResearch.WordTrace]
  refine ⟨271451041470024973235951417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180967360980016648823967611 271451041470024973235951417)
  ·
    refine ⟨203588281102518729926963563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271451041470024973235951417 203588281102518729926963563)
    ·
      refine ⟨305382421653778094890445345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203588281102518729926963563 305382421653778094890445345)
      ·
        refine ⟨229036816240333571167834009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305382421653778094890445345 229036816240333571167834009)
        ·
          refine ⟨171777612180250178375875507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229036816240333571167834009 171777612180250178375875507)
          ·
            refine ⟨257666418270375267563813261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171777612180250178375875507 257666418270375267563813261)
            ·
              refine ⟨96624906851390725336429973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257666418270375267563813261 96624906851390725336429973)
              ·
                refine ⟨4529292508658940250145155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96624906851390725336429973 4529292508658940250145155)
                ·
                  refine ⟨6793938762988410375217733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529292508658940250145155 6793938762988410375217733)
                  ·
                    refine ⟨1273863518060326945353325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6793938762988410375217733 1273863518060326945353325)
                    ·
                      rfl

theorem cell23_7442521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 1, 4].length) (baseStart_7442521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442521 prefixEnd_7442521 := by exact prefixLift 7442521
  have htrace : WordTrace (prefixWord ++ tailWord_7442521) baseStart_7442521 baseEnd_7442521 := by
    simpa [prefixWord, tailWord_7442521, baseEnd_7442521] using wordTrace_append hprefix tailTrace_7442521
  have hstable : (prefixWord ++ tailWord_7442521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442521).length < 2 ^ (prefixWord ++ tailWord_7442521).sum := by decide
  have hdescent : baseEnd_7442521 < baseStart_7442521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442537 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_7442537 : Nat := 118140960795 + 7442537 * 2 ^ 59
def prefixEnd_7442537 : Nat := 4983230072969 + 3 ^ 40 * 7442537 * 2
def baseEnd_7442537 : Nat := 3821598769871452773459901

theorem tailTrace_7442537 : CollatzResearch.WordTrace tailWord_7442537 prefixEnd_7442537 3821598769871452773459901 := by
  unfold tailWord_7442537
  simp only [CollatzResearch.WordTrace]
  refine ⟨271451625037967007968533865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180967750025311338645689243 271451625037967007968533865)
  ·
    refine ⟨203588718778475255976400399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271451625037967007968533865 203588718778475255976400399)
    ·
      refine ⟨305383078167712883964600599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203588718778475255976400399 305383078167712883964600599)
      ·
        refine ⟨458074617251569325946900899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305383078167712883964600599 458074617251569325946900899)
        ·
          refine ⟨687111925877353988920351349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458074617251569325946900899 687111925877353988920351349)
          ·
            refine ⟨64416743051001936461282939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 687111925877353988920351349 64416743051001936461282939)
            ·
              refine ⟨96625114576502904691924409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64416743051001936461282939 96625114576502904691924409)
              ·
                refine ⟨72468835932377178518943307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96625114576502904691924409 72468835932377178518943307)
                ·
                  refine ⟨108703253898565767778414961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72468835932377178518943307 108703253898565767778414961)
                  ·
                    refine ⟨81527440423924325833811221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108703253898565767778414961 81527440423924325833811221)
                    ·
                      refine ⟨3821598769871452773459901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81527440423924325833811221 3821598769871452773459901)
                      ·
                        rfl

theorem cell23_7442537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_7442537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442537 prefixEnd_7442537 := by exact prefixLift 7442537
  have htrace : WordTrace (prefixWord ++ tailWord_7442537) baseStart_7442537 baseEnd_7442537 := by
    simpa [prefixWord, tailWord_7442537, baseEnd_7442537] using wordTrace_append hprefix tailTrace_7442537
  have hstable : (prefixWord ++ tailWord_7442537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442537).length < 2 ^ (prefixWord ++ tailWord_7442537).sum := by decide
  have hdescent : baseEnd_7442537 < baseStart_7442537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442605 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_7442605 : Nat := 118140960795 + 7442605 * 2 ^ 59
def prefixEnd_7442605 : Nat := 4983230072969 + 3 ^ 40 * 7442605 * 2
def baseEnd_7442605 : Nat := 3821633686555958507409589

theorem tailTrace_7442605 : CollatzResearch.WordTrace tailWord_7442605 prefixEnd_7442605 3821633686555958507409589 := by
  unfold tailWord_7442605
  simp only [CollatzResearch.WordTrace]
  refine ⟨271454105201720655582009269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180969403467813770388006179 271454105201720655582009269)
  ·
    refine ⟨25448822362661311460813369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271454105201720655582009269 25448822362661311460813369)
    ·
      refine ⟨19086616771995983595610027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25448822362661311460813369 19086616771995983595610027)
      ·
        refine ⟨28629925157993975393415041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19086616771995983595610027 28629925157993975393415041)
        ·
          refine ⟨21472443868495481545061281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28629925157993975393415041 21472443868495481545061281)
          ·
            refine ⟨16104332901371611158795961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21472443868495481545061281 16104332901371611158795961)
            ·
              refine ⟨12078249676028708369096971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16104332901371611158795961 12078249676028708369096971)
              ·
                refine ⟨18117374514043062553645457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12078249676028708369096971 18117374514043062553645457)
                ·
                  refine ⟨13588030885532296915234093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18117374514043062553645457 13588030885532296915234093)
                  ·
                    refine ⟨5095511582074611343212785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13588030885532296915234093 5095511582074611343212785)
                    ·
                      refine ⟨3821633686555958507409589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095511582074611343212785 3821633686555958507409589)
                      ·
                        rfl

theorem cell23_7442605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_7442605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442605 prefixEnd_7442605 := by exact prefixLift 7442605
  have htrace : WordTrace (prefixWord ++ tailWord_7442605) baseStart_7442605 baseEnd_7442605 := by
    simpa [prefixWord, tailWord_7442605, baseEnd_7442605] using wordTrace_append hprefix tailTrace_7442605
  have hstable : (prefixWord ++ tailWord_7442605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442605).length < 2 ^ (prefixWord ++ tailWord_7442605).sum := by decide
  have hdescent : baseEnd_7442605 < baseStart_7442605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442628 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_7442628 : Nat := 118140960795 + 7442628 * 2 ^ 59
def prefixEnd_7442628 : Nat := 4983230072969 + 3 ^ 40 * 7442628 * 2
def baseEnd_7442628 : Nat := 1273881832203670639140661

theorem tailTrace_7442628 : CollatzResearch.WordTrace tailWord_7442628 prefixEnd_7442628 1273881832203670639140661 := by
  unfold tailWord_7442628
  simp only [CollatzResearch.WordTrace]
  refine ⟨135727472040318665255048269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180969962720424887006731025 135727472040318665255048269)
  ·
    refine ⟨50897802015119499470643101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135727472040318665255048269 50897802015119499470643101)
    ·
      refine ⟨19086675755669812301491163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50897802015119499470643101 19086675755669812301491163)
      ·
        refine ⟨28630013633504718452236745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19086675755669812301491163 28630013633504718452236745)
        ·
          refine ⟨21472510225128538839177559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28630013633504718452236745 21472510225128538839177559)
          ·
            refine ⟨32208765337692808258766339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21472510225128538839177559 32208765337692808258766339)
            ·
              refine ⟨48313148006539212388149509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32208765337692808258766339 48313148006539212388149509)
              ·
                refine ⟨9058715251226102322778033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48313148006539212388149509 9058715251226102322778033)
                ·
                  refine ⟨6794036438419576742083525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9058715251226102322778033 6794036438419576742083525)
                  ·
                    refine ⟨1273881832203670639140661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6794036438419576742083525 1273881832203670639140661)
                    ·
                      rfl

theorem cell23_7442628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_7442628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442628 prefixEnd_7442628 := by exact prefixLift 7442628
  have htrace : WordTrace (prefixWord ++ tailWord_7442628) baseStart_7442628 baseEnd_7442628 := by
    simpa [prefixWord, tailWord_7442628, baseEnd_7442628] using wordTrace_append hprefix tailTrace_7442628
  have hstable : (prefixWord ++ tailWord_7442628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442628).length < 2 ^ (prefixWord ++ tailWord_7442628).sum := by decide
  have hdescent : baseEnd_7442628 < baseStart_7442628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442635 : List Nat := [1, 1, 1, 1, 3, 2, 5, 4, 1, 2, 2]
def baseStart_7442635 : Nat := 118140960795 + 7442635 * 2 ^ 59
def prefixEnd_7442635 : Nat := 4983230072969 + 3 ^ 40 * 7442635 * 2
def baseEnd_7442635 : Nat := 3821649090975593390034451

theorem tailTrace_7442635 : CollatzResearch.WordTrace tailWord_7442635 prefixEnd_7442635 3821649090975593390034451 := by
  unfold tailWord_7442635
  simp only [CollatzResearch.WordTrace]
  refine ⟨271455199391611970705601359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180970132927741313803734239 271455199391611970705601359)
  ·
    refine ⟨407182799087417956058402039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271455199391611970705601359 407182799087417956058402039)
    ·
      refine ⟨610774198631126934087603059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407182799087417956058402039 610774198631126934087603059)
      ·
        refine ⟨916161297946690401131404589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610774198631126934087603059 916161297946690401131404589)
        ·
          refine ⟨343560486730008900424276721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 916161297946690401131404589 343560486730008900424276721)
          ·
            refine ⟨257670365047506675318207541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343560486730008900424276721 257670365047506675318207541)
            ·
              refine ⟨24156596723203750811081957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257670365047506675318207541 24156596723203750811081957)
              ·
                refine ⟨4529361885600703277077867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24156596723203750811081957 4529361885600703277077867)
                ·
                  refine ⟨6794042828401054915616801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529361885600703277077867 6794042828401054915616801)
                  ·
                    refine ⟨5095532121300791186712601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6794042828401054915616801 5095532121300791186712601)
                    ·
                      refine ⟨3821649090975593390034451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095532121300791186712601 3821649090975593390034451)
                      ·
                        rfl

theorem cell23_7442635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 1, 2, 2].length) (baseStart_7442635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442635 prefixEnd_7442635 := by exact prefixLift 7442635
  have htrace : WordTrace (prefixWord ++ tailWord_7442635) baseStart_7442635 baseEnd_7442635 := by
    simpa [prefixWord, tailWord_7442635, baseEnd_7442635] using wordTrace_append hprefix tailTrace_7442635
  have hstable : (prefixWord ++ tailWord_7442635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442635).length < 2 ^ (prefixWord ++ tailWord_7442635).sum := by decide
  have hdescent : baseEnd_7442635 < baseStart_7442635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442669 : List Nat := [1, 5, 1, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_7442669 : Nat := 118140960795 + 7442669 * 2 ^ 59
def prefixEnd_7442669 : Nat := 4983230072969 + 3 ^ 40 * 7442669 * 2
def baseEnd_7442669 : Nat := 3821666549317846257009295

theorem tailTrace_7442669 : CollatzResearch.WordTrace tailWord_7442669 prefixEnd_7442669 3821666549317846257009295 := by
  unfold tailWord_7442669
  simp only [CollatzResearch.WordTrace]
  refine ⟨271456439473488794512339061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180970959648992529674892707 271456439473488794512339061)
  ·
    refine ⟨25449041200639574485531787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271456439473488794512339061 25449041200639574485531787)
    ·
      refine ⟨38173561800959361728297681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25449041200639574485531787 38173561800959361728297681)
      ·
        refine ⟨28630171350719521296223261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38173561800959361728297681 28630171350719521296223261)
        ·
          refine ⟨10736314256519820486083723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28630171350719521296223261 10736314256519820486083723)
          ·
            refine ⟨16104471384779730729125585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10736314256519820486083723 16104471384779730729125585)
            ·
              refine ⟨12078353538584798046844189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16104471384779730729125585 12078353538584798046844189)
              ·
                refine ⟨4529382576969299267566571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12078353538584798046844189 4529382576969299267566571)
                ·
                  refine ⟨6794073865453948901349857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529382576969299267566571 6794073865453948901349857)
                  ·
                    refine ⟨5095555399090461676012393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6794073865453948901349857 5095555399090461676012393)
                    ·
                      refine ⟨3821666549317846257009295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095555399090461676012393 3821666549317846257009295)
                      ·
                        rfl

theorem cell23_7442669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_7442669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442669 prefixEnd_7442669 := by exact prefixLift 7442669
  have htrace : WordTrace (prefixWord ++ tailWord_7442669) baseStart_7442669 baseEnd_7442669 := by
    simpa [prefixWord, tailWord_7442669, baseEnd_7442669] using wordTrace_append hprefix tailTrace_7442669
  have hstable : (prefixWord ++ tailWord_7442669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442669).length < 2 ^ (prefixWord ++ tailWord_7442669).sum := by decide
  have hdescent : baseEnd_7442669 < baseStart_7442669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442728 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_7442728 : Nat := 118140960795 + 7442728 * 2 ^ 59
def prefixEnd_7442728 : Nat := 4983230072969 + 3 ^ 40 * 7442728 * 2
def baseEnd_7442728 : Nat := 3821696844676461526171523

theorem tailTrace_7442728 : CollatzResearch.WordTrace tailWord_7442728 prefixEnd_7442728 3821696844676461526171523 := by
  unfold tailWord_7442728
  simp only [CollatzResearch.WordTrace]
  refine ⟨135729295690137523794368419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180972394253516698392491225 135729295690137523794368419)
  ·
    refine ⟨203593943535206285691552629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135729295690137523794368419 203593943535206285691552629)
    ·
      refine ⟨19086932206425589283583059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203593943535206285691552629 19086932206425589283583059)
      ·
        refine ⟨28630398309638383925374589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19086932206425589283583059 28630398309638383925374589)
        ·
          refine ⟨10736399366114393972015471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28630398309638383925374589 10736399366114393972015471)
          ·
            refine ⟨16104599049171590958023207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10736399366114393972015471 16104599049171590958023207)
            ·
              refine ⟨24156898573757386437034811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16104599049171590958023207 24156898573757386437034811)
              ·
                refine ⟨36235347860636079655552217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24156898573757386437034811 36235347860636079655552217)
                ·
                  refine ⟨27176510895477059741664163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36235347860636079655552217 27176510895477059741664163)
                  ·
                    refine ⟨40764766343215589612496245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27176510895477059741664163 40764766343215589612496245)
                    ·
                      refine ⟨3821696844676461526171523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40764766343215589612496245 3821696844676461526171523)
                      ·
                        rfl

theorem cell23_7442728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_7442728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442728 prefixEnd_7442728 := by exact prefixLift 7442728
  have htrace : WordTrace (prefixWord ++ tailWord_7442728) baseStart_7442728 baseEnd_7442728 := by
    simpa [prefixWord, tailWord_7442728, baseEnd_7442728] using wordTrace_append hprefix tailTrace_7442728
  have hstable : (prefixWord ++ tailWord_7442728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442728).length < 2 ^ (prefixWord ++ tailWord_7442728).sum := by decide
  have hdescent : baseEnd_7442728 < baseStart_7442728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442801 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 3, 4, 3]
def baseStart_7442801 : Nat := 118140960795 + 7442801 * 2 ^ 59
def prefixEnd_7442801 : Nat := 4983230072969 + 3 ^ 40 * 7442801 * 2
def baseEnd_7442801 : Nat := 3821734328764239740558687

theorem tailTrace_7442801 : CollatzResearch.WordTrace tailWord_7442801 prefixEnd_7442801 3821734328764239740558687 := by
  unfold tailWord_7442801
  simp only [CollatzResearch.WordTrace]
  refine ⟨271461253909010581056144257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180974169272673720704096171 271461253909010581056144257)
  ·
    refine ⟨203595940431757935792108193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271461253909010581056144257 203595940431757935792108193)
    ·
      refine ⟨152696955323818451844081145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203595940431757935792108193 152696955323818451844081145)
      ·
        refine ⟨114522716492863838883060859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152696955323818451844081145 114522716492863838883060859)
        ·
          refine ⟨171784074739295758324591289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114522716492863838883060859 171784074739295758324591289)
          ·
            refine ⟨128838056054471818743443467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171784074739295758324591289 128838056054471818743443467)
            ·
              refine ⟨193257084081707728115165201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128838056054471818743443467 193257084081707728115165201)
              ·
                refine ⟨144942813061280796086373901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193257084081707728115165201 144942813061280796086373901)
                ·
                  refine ⟨54353554897980298532390213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144942813061280796086373901 54353554897980298532390213)
                  ·
                    refine ⟨10191291543371305974823165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54353554897980298532390213 10191291543371305974823165)
                    ·
                      refine ⟨3821734328764239740558687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10191291543371305974823165 3821734328764239740558687)
                      ·
                        rfl

theorem cell23_7442801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_7442801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442801 prefixEnd_7442801 := by exact prefixLift 7442801
  have htrace : WordTrace (prefixWord ++ tailWord_7442801) baseStart_7442801 baseEnd_7442801 := by
    simpa [prefixWord, tailWord_7442801, baseEnd_7442801] using wordTrace_append hprefix tailTrace_7442801
  have hstable : (prefixWord ++ tailWord_7442801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442801).length < 2 ^ (prefixWord ++ tailWord_7442801).sum := by decide
  have hdescent : baseEnd_7442801 < baseStart_7442801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442842 : List Nat := [3, 1, 1, 4, 1, 3, 2, 3, 1, 4]
def baseStart_7442842 : Nat := 118140960795 + 7442842 * 2 ^ 59
def prefixEnd_7442842 : Nat := 4983230072969 + 3 ^ 40 * 7442842 * 2
def baseEnd_7442842 : Nat := 1273918460490358026715333

theorem tailTrace_7442842 : CollatzResearch.WordTrace tailWord_7442842 prefixEnd_7442842 1273918460490358026715333 := by
  unfold tailWord_7442842
  simp only [CollatzResearch.WordTrace]
  refine ⟨67865687325465511264596695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180975166201241363372257853 67865687325465511264596695)
  ·
    refine ⟨101798530988198266896895043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67865687325465511264596695 101798530988198266896895043)
    ·
      refine ⟨152697796482297400345342565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101798530988198266896895043 152697796482297400345342565)
      ·
        refine ⟨28630836840430762564751731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152697796482297400345342565 28630836840430762564751731)
        ·
          refine ⟨42946255260646143847127597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28630836840430762564751731 42946255260646143847127597)
          ·
            refine ⟨16104845722742303942672849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42946255260646143847127597 16104845722742303942672849)
            ·
              refine ⟨12078634292056727957004637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16104845722742303942672849 12078634292056727957004637)
              ·
                refine ⟨4529487859521272983876739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12078634292056727957004637 4529487859521272983876739)
                ·
                  refine ⟨6794231789281909475815109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529487859521272983876739 6794231789281909475815109)
                  ·
                    refine ⟨1273918460490358026715333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6794231789281909475815109 1273918460490358026715333)
                    ·
                      rfl

theorem cell23_7442842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_7442842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442842 prefixEnd_7442842 := by exact prefixLift 7442842
  have htrace : WordTrace (prefixWord ++ tailWord_7442842) baseStart_7442842 baseEnd_7442842 := by
    simpa [prefixWord, tailWord_7442842, baseEnd_7442842] using wordTrace_append hprefix tailTrace_7442842
  have hstable : (prefixWord ++ tailWord_7442842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442842).length < 2 ^ (prefixWord ++ tailWord_7442842).sum := by decide
  have hdescent : baseEnd_7442842 < baseStart_7442842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442855 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 6]
def baseStart_7442855 : Nat := 118140960795 + 7442855 * 2 ^ 59
def prefixEnd_7442855 : Nat := 4983230072969 + 3 ^ 40 * 7442855 * 2
def baseEnd_7442855 : Nat := 424640228524398058809271

theorem tailTrace_7442855 : CollatzResearch.WordTrace tailWord_7442855 prefixEnd_7442855 424640228524398058809271 := by
  unfold tailWord_7442855
  simp only [CollatzResearch.WordTrace]
  refine ⟨271463223450814948278610019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180975482300543298852406679 271463223450814948278610019)
  ·
    refine ⟨407194835176222422417915029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271463223450814948278610019 407194835176222422417915029)
    ·
      refine ⟨19087257898885426050839767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 407194835176222422417915029 19087257898885426050839767)
      ·
        refine ⟨28630886848328139076259651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19087257898885426050839767 28630886848328139076259651)
        ·
          refine ⟨42946330272492208614389477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28630886848328139076259651 42946330272492208614389477)
          ·
            refine ⟨8052436926092289115198027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42946330272492208614389477 8052436926092289115198027)
            ·
              refine ⟨12078655389138433672797041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8052436926092289115198027 12078655389138433672797041)
              ·
                refine ⟨9058991541853825254597781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12078655389138433672797041 9058991541853825254597781)
                ·
                  refine ⟨424640228524398058809271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9058991541853825254597781 424640228524398058809271)
                  ·
                    rfl

theorem cell23_7442855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 6].length) (baseStart_7442855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442855 prefixEnd_7442855 := by exact prefixLift 7442855
  have htrace : WordTrace (prefixWord ++ tailWord_7442855) baseStart_7442855 baseEnd_7442855 := by
    simpa [prefixWord, tailWord_7442855, baseEnd_7442855] using wordTrace_append hprefix tailTrace_7442855
  have hstable : (prefixWord ++ tailWord_7442855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442855).length < 2 ^ (prefixWord ++ tailWord_7442855).sum := by decide
  have hdescent : baseEnd_7442855 < baseStart_7442855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442865 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 3, 1, 3]
def baseStart_7442865 : Nat := 118140960795 + 7442865 * 2 ^ 59
def prefixEnd_7442865 : Nat := 4983230072969 + 3 ^ 40 * 7442865 * 2
def baseEnd_7442865 : Nat := 3821767191526127490158393

theorem tailTrace_7442865 : CollatzResearch.WordTrace tailWord_7442865 prefixEnd_7442865 3821767191526127490158393 := by
  unfold tailWord_7442865
  simp only [CollatzResearch.WordTrace]
  refine ⟨271463588180778719986474049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180975725453852479990982699 271463588180778719986474049)
  ·
    refine ⟨203597691135584039989855537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271463588180778719986474049 203597691135584039989855537)
    ·
      refine ⟨152698268351688029992391653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203597691135584039989855537 152698268351688029992391653)
      ·
        refine ⟨28630925315941505623573435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152698268351688029992391653 28630925315941505623573435)
        ·
          refine ⟨42946387973912258435360153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28630925315941505623573435 42946387973912258435360153)
          ·
            refine ⟨32209790980434193826520115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42946387973912258435360153 32209790980434193826520115)
            ·
              refine ⟨48314686470651290739780173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32209790980434193826520115 48314686470651290739780173)
              ·
                refine ⟨18118007426494234027417565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48314686470651290739780173 18118007426494234027417565)
                ·
                  refine ⟨6794252784935337760281587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18118007426494234027417565 6794252784935337760281587)
                  ·
                    refine ⟨10191379177403006640422381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6794252784935337760281587 10191379177403006640422381)
                    ·
                      refine ⟨3821767191526127490158393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10191379177403006640422381 3821767191526127490158393)
                      ·
                        rfl

theorem cell23_7442865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_7442865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442865 prefixEnd_7442865 := by exact prefixLift 7442865
  have htrace : WordTrace (prefixWord ++ tailWord_7442865) baseStart_7442865 baseEnd_7442865 := by
    simpa [prefixWord, tailWord_7442865, baseEnd_7442865] using wordTrace_append hprefix tailTrace_7442865
  have hstable : (prefixWord ++ tailWord_7442865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442865).length < 2 ^ (prefixWord ++ tailWord_7442865).sum := by decide
  have hdescent : baseEnd_7442865 < baseStart_7442865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442891 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 5]
def baseStart_7442891 : Nat := 118140960795 + 7442891 * 2 ^ 59
def prefixEnd_7442891 : Nat := 4983230072969 + 3 ^ 40 * 7442891 * 2
def baseEnd_7442891 : Nat := 3821780542023144388433273

theorem tailTrace_7442891 : CollatzResearch.WordTrace tailWord_7442891 prefixEnd_7442891 3821780542023144388433273 := by
  unfold tailWord_7442891
  simp only [CollatzResearch.WordTrace]
  refine ⟨271464536478684526426920527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180976357652456350951280351 271464536478684526426920527)
  ·
    refine ⟨407196804718026789640380791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271464536478684526426920527 407196804718026789640380791)
    ·
      refine ⟨610795207077040184460571187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407196804718026789640380791 610795207077040184460571187)
      ·
        refine ⟨916192810615560276690856781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610795207077040184460571187 916192810615560276690856781)
        ·
          refine ⟨343572303980835103759071293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 916192810615560276690856781 343572303980835103759071293)
          ·
            refine ⟨128839613992813163909651735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343572303980835103759071293 128839613992813163909651735)
            ·
              refine ⟨193259420989219745864477603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128839613992813163909651735 193259420989219745864477603)
              ·
                refine ⟨289889131483829618796716405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193259420989219745864477603 289889131483829618796716405)
                ·
                  refine ⟨27177106076609026762192163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289889131483829618796716405 27177106076609026762192163)
                  ·
                    refine ⟨40765659114913540143288245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27177106076609026762192163 40765659114913540143288245)
                    ·
                      refine ⟨3821780542023144388433273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40765659114913540143288245 3821780542023144388433273)
                      ·
                        rfl

theorem cell23_7442891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 5].length) (baseStart_7442891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442891 prefixEnd_7442891 := by exact prefixLift 7442891
  have htrace : WordTrace (prefixWord ++ tailWord_7442891) baseStart_7442891 baseEnd_7442891 := by
    simpa [prefixWord, tailWord_7442891, baseEnd_7442891] using wordTrace_append hprefix tailTrace_7442891
  have hstable : (prefixWord ++ tailWord_7442891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442891).length < 2 ^ (prefixWord ++ tailWord_7442891).sum := by decide
  have hdescent : baseEnd_7442891 < baseStart_7442891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442911 : List Nat := [1, 1, 2, 3, 3, 2, 11]
def baseStart_7442911 : Nat := 118140960795 + 7442911 * 2 ^ 59
def prefixEnd_7442911 : Nat := 4983230072969 + 3 ^ 40 * 7442911 * 2
def baseEnd_7442911 : Nat := 47182602612793016175101

theorem tailTrace_7442911 : CollatzResearch.WordTrace tailWord_7442911 prefixEnd_7442911 47182602612793016175101 := by
  unfold tailWord_7442911
  simp only [CollatzResearch.WordTrace]
  refine ⟨271465265938612069842648587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180976843959074713228432391 271465265938612069842648587)
  ·
    refine ⟨407197898907918104763972881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271465265938612069842648587 407197898907918104763972881)
    ·
      refine ⟨305398424180938578572979661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407197898907918104763972881 305398424180938578572979661)
      ·
        refine ⟨114524409067851966964867373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305398424180938578572979661 114524409067851966964867373)
        ·
          refine ⟨42946653400444487611825265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114524409067851966964867373 42946653400444487611825265)
          ·
            refine ⟨32209990050333365708868949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42946653400444487611825265 32209990050333365708868949)
            ·
              refine ⟨47182602612793016175101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32209990050333365708868949 47182602612793016175101)
              ·
                rfl

theorem cell23_7442911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 11].length) (baseStart_7442911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442911 prefixEnd_7442911 := by exact prefixLift 7442911
  have htrace : WordTrace (prefixWord ++ tailWord_7442911) baseStart_7442911 baseEnd_7442911 := by
    simpa [prefixWord, tailWord_7442911, baseEnd_7442911] using wordTrace_append hprefix tailTrace_7442911
  have hstable : (prefixWord ++ tailWord_7442911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442911).length < 2 ^ (prefixWord ++ tailWord_7442911).sum := by decide
  have hdescent : baseEnd_7442911 < baseStart_7442911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442925 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7442925 : Nat := 118140960795 + 7442925 * 2 ^ 59
def prefixEnd_7442925 : Nat := 4983230072969 + 3 ^ 40 * 7442925 * 2
def baseEnd_7442925 : Nat := 3821798000365397255408117

theorem tailTrace_7442925 : CollatzResearch.WordTrace tailWord_7442925 prefixEnd_7442925 3821798000365397255408117 := by
  unfold tailWord_7442925
  simp only [CollatzResearch.WordTrace]
  refine ⟨271465776560561350233658229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180977184373707566822438819 271465776560561350233658229)
  ·
    refine ⟨25449916552552626584405459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271465776560561350233658229 25449916552552626584405459)
    ·
      refine ⟨38174874828828939876608189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25449916552552626584405459 38174874828828939876608189)
      ·
        refine ⟨14315578060810852453728071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38174874828828939876608189 14315578060810852453728071)
        ·
          refine ⟨21473367091216278680592107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14315578060810852453728071 21473367091216278680592107)
          ·
            refine ⟨32210050636824418020888161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21473367091216278680592107 32210050636824418020888161)
            ·
              refine ⟨24157537977618313515666121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32210050636824418020888161 24157537977618313515666121)
              ·
                refine ⟨18118153483213735136749591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24157537977618313515666121 18118153483213735136749591)
                ·
                  refine ⟨27177230224820602705124387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18118153483213735136749591 27177230224820602705124387)
                  ·
                    refine ⟨40765845337230904057686581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27177230224820602705124387 40765845337230904057686581)
                    ·
                      refine ⟨3821798000365397255408117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40765845337230904057686581 3821798000365397255408117)
                      ·
                        rfl

theorem cell23_7442925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7442925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442925 prefixEnd_7442925 := by exact prefixLift 7442925
  have htrace : WordTrace (prefixWord ++ tailWord_7442925) baseStart_7442925 baseEnd_7442925 := by
    simpa [prefixWord, tailWord_7442925, baseEnd_7442925] using wordTrace_append hprefix tailTrace_7442925
  have hstable : (prefixWord ++ tailWord_7442925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442925).length < 2 ^ (prefixWord ++ tailWord_7442925).sum := by decide
  have hdescent : baseEnd_7442925 < baseStart_7442925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442931 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 6]
def baseStart_7442931 : Nat := 118140960795 + 7442931 * 2 ^ 59
def prefixEnd_7442931 : Nat := 4983230072969 + 3 ^ 40 * 7442931 * 2
def baseEnd_7442931 : Nat := 3821801081249324231933089

theorem tailTrace_7442931 : CollatzResearch.WordTrace tailWord_7442931 prefixEnd_7442931 3821801081249324231933089 := by
  unfold tailWord_7442931
  simp only [CollatzResearch.WordTrace]
  refine ⟨271465995398539613258376647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180977330265693075505584431 271465995398539613258376647)
  ·
    refine ⟨407198993097809419887564971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271465995398539613258376647 407198993097809419887564971)
    ·
      refine ⟨610798489646714129831347457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407198993097809419887564971 610798489646714129831347457)
      ·
        refine ⟨458098867235035597373510593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610798489646714129831347457 458098867235035597373510593)
        ·
          refine ⟨343574150426276698030132945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458098867235035597373510593 343574150426276698030132945)
          ·
            refine ⟨257680612819707523522599709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343574150426276698030132945 257680612819707523522599709)
            ·
              refine ⟨96630229807390321320974891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257680612819707523522599709 96630229807390321320974891)
              ·
                refine ⟨144945344711085481981462337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96630229807390321320974891 144945344711085481981462337)
                ·
                  refine ⟨108709008533314111486096753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144945344711085481981462337 108709008533314111486096753)
                  ·
                    refine ⟨81531756399985583614572565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108709008533314111486096753 81531756399985583614572565)
                    ·
                      refine ⟨3821801081249324231933089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81531756399985583614572565 3821801081249324231933089)
                      ·
                        rfl

theorem cell23_7442931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_7442931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442931 prefixEnd_7442931 := by exact prefixLift 7442931
  have htrace : WordTrace (prefixWord ++ tailWord_7442931) baseStart_7442931 baseEnd_7442931 := by
    simpa [prefixWord, tailWord_7442931, baseEnd_7442931] using wordTrace_append hprefix tailTrace_7442931
  have hstable : (prefixWord ++ tailWord_7442931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442931).length < 2 ^ (prefixWord ++ tailWord_7442931).sum := by decide
  have hdescent : baseEnd_7442931 < baseStart_7442931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442955 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 3]
def baseStart_7442955 : Nat := 118140960795 + 7442955 * 2 ^ 59
def prefixEnd_7442955 : Nat := 4983230072969 + 3 ^ 40 * 7442955 * 2
def baseEnd_7442955 : Nat := 3821813404785032138032979

theorem tailTrace_7442955 : CollatzResearch.WordTrace tailWord_7442955 prefixEnd_7442955 3821813404785032138032979 := by
  unfold tailWord_7442955
  simp only [CollatzResearch.WordTrace]
  refine ⟨271466870750452665357250319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180977913833635110238166879 271466870750452665357250319)
  ·
    refine ⟨407200306125678998035875479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271466870750452665357250319 407200306125678998035875479)
    ·
      refine ⟨610800459188518497053813219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407200306125678998035875479 610800459188518497053813219)
      ·
        refine ⟨916200688782777745580719829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610800459188518497053813219 916200688782777745580719829)
        ·
          refine ⟨21473453643346353412048121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 916200688782777745580719829 21473453643346353412048121)
          ·
            refine ⟨16105090232509765059036091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21473453643346353412048121 16105090232509765059036091)
            ·
              refine ⟨24157635348764647588554137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16105090232509765059036091 24157635348764647588554137)
              ·
                refine ⟨18118226511573485691415603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24157635348764647588554137 18118226511573485691415603)
                ·
                  refine ⟨27177339767360228537123405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18118226511573485691415603 27177339767360228537123405)
                  ·
                    refine ⟨10191502412760085701421277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27177339767360228537123405 10191502412760085701421277)
                    ·
                      refine ⟨3821813404785032138032979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10191502412760085701421277 3821813404785032138032979)
                      ·
                        rfl

theorem cell23_7442955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 3].length) (baseStart_7442955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442955 prefixEnd_7442955 := by exact prefixLift 7442955
  have htrace : WordTrace (prefixWord ++ tailWord_7442955) baseStart_7442955 baseEnd_7442955 := by
    simpa [prefixWord, tailWord_7442955, baseEnd_7442955] using wordTrace_append hprefix tailTrace_7442955
  have hstable : (prefixWord ++ tailWord_7442955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442955).length < 2 ^ (prefixWord ++ tailWord_7442955).sum := by decide
  have hdescent : baseEnd_7442955 < baseStart_7442955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442971 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 5, 8]
def baseStart_7442971 : Nat := 118140960795 + 7442971 * 2 ^ 59
def prefixEnd_7442971 : Nat := 4983230072969 + 3 ^ 40 * 7442971 * 2
def baseEnd_7442971 : Nat := 1273940540158501358477635

theorem tailTrace_7442971 : CollatzResearch.WordTrace tailWord_7442971 prefixEnd_7442971 1273940540158501358477635 := by
  unfold tailWord_7442971
  simp only [CollatzResearch.WordTrace]
  refine ⟨271467454318394700089832767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180978302878929800059888511 271467454318394700089832767)
  ·
    refine ⟨407201181477592050134749151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271467454318394700089832767 407201181477592050134749151)
    ·
      refine ⟨610801772216388075202123727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407201181477592050134749151 610801772216388075202123727)
      ·
        refine ⟨916202658324582112803185591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610801772216388075202123727 916202658324582112803185591)
        ·
          refine ⟨1374303987486873169204778387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916202658324582112803185591 1374303987486873169204778387)
          ·
            refine ⟨2061455981230309753807167581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374303987486873169204778387 2061455981230309753807167581)
            ·
              refine ⟨773045992961366157677687843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2061455981230309753807167581 773045992961366157677687843)
              ·
                refine ⟨1159568989442049236516531765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773045992961366157677687843 1159568989442049236516531765)
                ·
                  refine ⟨108709592760192115923424853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1159568989442049236516531765 108709592760192115923424853)
                  ·
                    refine ⟨1273940540158501358477635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108709592760192115923424853 1273940540158501358477635)
                    ·
                      rfl

theorem cell23_7442971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 8].length) (baseStart_7442971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442971 prefixEnd_7442971 := by exact prefixLift 7442971
  have htrace : WordTrace (prefixWord ++ tailWord_7442971) baseStart_7442971 baseEnd_7442971 := by
    simpa [prefixWord, tailWord_7442971, baseEnd_7442971] using wordTrace_append hprefix tailTrace_7442971
  have hstable : (prefixWord ++ tailWord_7442971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442971).length < 2 ^ (prefixWord ++ tailWord_7442971).sum := by decide
  have hdescent : baseEnd_7442971 < baseStart_7442971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442972 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_7442972 : Nat := 118140960795 + 7442972 * 2 ^ 59
def prefixEnd_7442972 : Nat := 4983230072969 + 3 ^ 40 * 7442972 * 2
def baseEnd_7442972 : Nat := 3821822133956158571520401

theorem tailTrace_7442972 : CollatzResearch.WordTrace tailWord_7442972 prefixEnd_7442972 3821822133956158571520401 := by
  unfold tailWord_7442972
  simp only [CollatzResearch.WordTrace]
  refine ⟨135733745395695538630309585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180978327194260718173746113 135733745395695538630309585)
  ·
    refine ⟨101800309046771653972732189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135733745395695538630309585 101800309046771653972732189)
    ·
      refine ⟨38175115892539370239774571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101800309046771653972732189 38175115892539370239774571)
      ·
        refine ⟨57262673838809055359661857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38175115892539370239774571 57262673838809055359661857)
        ·
          refine ⟨42947005379106791519746393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57262673838809055359661857 42947005379106791519746393)
          ·
            refine ⟨32210254034330093639809795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42947005379106791519746393 32210254034330093639809795)
            ·
              refine ⟨48315381051495140459714693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32210254034330093639809795 48315381051495140459714693)
              ·
                refine ⟨9059133947155338836196505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48315381051495140459714693 9059133947155338836196505)
                ·
                  refine ⟨6794350460366504127147379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9059133947155338836196505 6794350460366504127147379)
                  ·
                    refine ⟨10191525690549756190721069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6794350460366504127147379 10191525690549756190721069)
                    ·
                      refine ⟨3821822133956158571520401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10191525690549756190721069 3821822133956158571520401)
                      ·
                        rfl

theorem cell23_7442972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_7442972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442972 prefixEnd_7442972 := by exact prefixLift 7442972
  have htrace : WordTrace (prefixWord ++ tailWord_7442972) baseStart_7442972 baseEnd_7442972 := by
    simpa [prefixWord, tailWord_7442972, baseEnd_7442972] using wordTrace_append hprefix tailTrace_7442972
  have hstable : (prefixWord ++ tailWord_7442972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442972).length < 2 ^ (prefixWord ++ tailWord_7442972).sum := by decide
  have hdescent : baseEnd_7442972 < baseStart_7442972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7442973 : List Nat := [1, 4, 2, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_7442973 : Nat := 118140960795 + 7442973 * 2 ^ 59
def prefixEnd_7442973 : Nat := 4983230072969 + 3 ^ 40 * 7442973 * 2
def baseEnd_7442973 : Nat := 3821822647436813067607897

theorem tailTrace_7442973 : CollatzResearch.WordTrace tailWord_7442973 prefixEnd_7442973 3821822647436813067607897 := by
  unfold tailWord_7442973
  simp only [CollatzResearch.WordTrace]
  refine ⟨271467527264387454431405573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180978351509591636287603715 271467527264387454431405573)
  ·
    refine ⟨50900161362072647705888545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271467527264387454431405573 50900161362072647705888545)
    ·
      refine ⟨38175121021554485779416409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50900161362072647705888545 38175121021554485779416409)
      ·
        refine ⟨28631340766165864334562307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38175121021554485779416409 28631340766165864334562307)
        ·
          refine ⟨42947011149248796501843461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28631340766165864334562307 42947011149248796501843461)
          ·
            refine ⟨8052564590484149344095649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42947011149248796501843461 8052564590484149344095649)
            ·
              refine ⟨6039423442863112008071737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8052564590484149344095649 6039423442863112008071737)
              ·
                refine ⟨4529567582147334006053803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6039423442863112008071737 4529567582147334006053803)
                ·
                  refine ⟨6794351373221001009080705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529567582147334006053803 6794351373221001009080705)
                  ·
                    refine ⟨5095763529915750756810529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6794351373221001009080705 5095763529915750756810529)
                    ·
                      refine ⟨3821822647436813067607897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095763529915750756810529 3821822647436813067607897)
                      ·
                        rfl

theorem cell23_7442973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_7442973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7442973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7442973 prefixEnd_7442973 := by exact prefixLift 7442973
  have htrace : WordTrace (prefixWord ++ tailWord_7442973) baseStart_7442973 baseEnd_7442973 := by
    simpa [prefixWord, tailWord_7442973, baseEnd_7442973] using wordTrace_append hprefix tailTrace_7442973
  have hstable : (prefixWord ++ tailWord_7442973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7442973).length < 2 ^ (prefixWord ++ tailWord_7442973).sum := by decide
  have hdescent : baseEnd_7442973 < baseStart_7442973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7442973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443029 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 2, 2, 2]
def baseStart_7443029 : Nat := 118140960795 + 7443029 * 2 ^ 59
def prefixEnd_7443029 : Nat := 4983230072969 + 3 ^ 40 * 7443029 * 2
def baseEnd_7443029 : Nat := 3821851402353464848507639

theorem tailTrace_7443029 : CollatzResearch.WordTrace tailWord_7443029 prefixEnd_7443029 3821851402353464848507639 := by
  unfold tailWord_7443029
  simp only [CollatzResearch.WordTrace]
  refine ⟨271469569752184575995444141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180979713168123050663629427 271469569752184575995444141)
  ·
    refine ⟨101801088657069215998291553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271469569752184575995444141 101801088657069215998291553)
    ·
      refine ⟨76350816492801911998718665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101801088657069215998291553 76350816492801911998718665)
      ·
        refine ⟨57263112369601433999038999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76350816492801911998718665 57263112369601433999038999)
        ·
          refine ⟨85894668554402150998558499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57263112369601433999038999 85894668554402150998558499)
          ·
            refine ⟨128842002831603226497837749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85894668554402150998558499 128842002831603226497837749)
            ·
              refine ⟨12078937765462802484172289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128842002831603226497837749 12078937765462802484172289)
              ·
                refine ⟨9059203324097101863129217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12078937765462802484172289 9059203324097101863129217)
                ·
                  refine ⟨6794402493072826397346913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9059203324097101863129217 6794402493072826397346913)
                  ·
                    refine ⟨5095801869804619798010185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6794402493072826397346913 5095801869804619798010185)
                    ·
                      refine ⟨3821851402353464848507639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095801869804619798010185 3821851402353464848507639)
                      ·
                        rfl

theorem cell23_7443029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_7443029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443029 prefixEnd_7443029 := by exact prefixLift 7443029
  have htrace : WordTrace (prefixWord ++ tailWord_7443029) baseStart_7443029 baseEnd_7443029 := by
    simpa [prefixWord, tailWord_7443029, baseEnd_7443029] using wordTrace_append hprefix tailTrace_7443029
  have hstable : (prefixWord ++ tailWord_7443029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443029).length < 2 ^ (prefixWord ++ tailWord_7443029).sum := by decide
  have hdescent : baseEnd_7443029 < baseStart_7443029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443055 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 2, 5, 2]
def baseStart_7443055 : Nat := 118140960795 + 7443055 * 2 ^ 59
def prefixEnd_7443055 : Nat := 4983230072969 + 3 ^ 40 * 7443055 * 2
def baseEnd_7443055 : Nat := 3821864752850481746782519

theorem tailTrace_7443055 : CollatzResearch.WordTrace tailWord_7443055 prefixEnd_7443055 3821864752850481746782519 := by
  unfold tailWord_7443055
  simp only [CollatzResearch.WordTrace]
  refine ⟨271470518050090382435890619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180980345366726921623927079 271470518050090382435890619)
  ·
    refine ⟨407205777075135573653835929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271470518050090382435890619 407205777075135573653835929)
    ·
      refine ⟨305404332806351680240376947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407205777075135573653835929 305404332806351680240376947)
      ·
        refine ⟨458106499209527520360565421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305404332806351680240376947 458106499209527520360565421)
        ·
          refine ⟨171789937203572820135212033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458106499209527520360565421 171789937203572820135212033)
          ·
            refine ⟨128842452902679615101409025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171789937203572820135212033 128842452902679615101409025)
            ·
              refine ⟨96631839677009711326056769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128842452902679615101409025 96631839677009711326056769)
              ·
                refine ⟨72473879757757283494542577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96631839677009711326056769 72473879757757283494542577)
                ·
                  refine ⟨54355409818317962620906933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72473879757757283494542577 54355409818317962620906933)
                  ·
                    refine ⟨5095819670467308995710025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54355409818317962620906933 5095819670467308995710025)
                    ·
                      refine ⟨3821864752850481746782519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095819670467308995710025 3821864752850481746782519)
                      ·
                        rfl

theorem cell23_7443055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 5, 2].length) (baseStart_7443055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443055 prefixEnd_7443055 := by exact prefixLift 7443055
  have htrace : WordTrace (prefixWord ++ tailWord_7443055) baseStart_7443055 baseEnd_7443055 := by
    simpa [prefixWord, tailWord_7443055, baseEnd_7443055] using wordTrace_append hprefix tailTrace_7443055
  have hstable : (prefixWord ++ tailWord_7443055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443055).length < 2 ^ (prefixWord ++ tailWord_7443055).sum := by decide
  have hdescent : baseEnd_7443055 < baseStart_7443055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443069 : List Nat := [1, 4, 1, 1, 5, 2, 1, 3, 5]
def baseStart_7443069 : Nat := 118140960795 + 7443069 * 2 ^ 59
def prefixEnd_7443069 : Nat := 4983230072969 + 3 ^ 40 * 7443069 * 2
def baseEnd_7443069 : Nat := 424652437953293854667495

theorem tailTrace_7443069 : CollatzResearch.WordTrace tailWord_7443069 prefixEnd_7443069 424652437953293854667495 := by
  unfold tailWord_7443069
  simp only [CollatzResearch.WordTrace]
  refine ⟨271471028672039662826900261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180980685781359775217933507 271471028672039662826900261)
  ·
    refine ⟨50900817876007436780043799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271471028672039662826900261 50900817876007436780043799)
    ·
      refine ⟨76351226814011155170065699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50900817876007436780043799 76351226814011155170065699)
      ·
        refine ⟨114526840221016732755098549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76351226814011155170065699 114526840221016732755098549)
        ·
          refine ⟨10736891270720318695790489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114526840221016732755098549 10736891270720318695790489)
          ·
            refine ⟨8052668453040239021842867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10736891270720318695790489 8052668453040239021842867)
            ·
              refine ⟨12079002679560358532764301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8052668453040239021842867 12079002679560358532764301)
              ·
                refine ⟨4529626004835134449786613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12079002679560358532764301 4529626004835134449786613)
                ·
                  refine ⟨424652437953293854667495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4529626004835134449786613 424652437953293854667495)
                  ·
                    rfl

theorem cell23_7443069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_7443069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443069 prefixEnd_7443069 := by exact prefixLift 7443069
  have htrace : WordTrace (prefixWord ++ tailWord_7443069) baseStart_7443069 baseEnd_7443069 := by
    simpa [prefixWord, tailWord_7443069, baseEnd_7443069] using wordTrace_append hprefix tailTrace_7443069
  have hstable : (prefixWord ++ tailWord_7443069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443069).length < 2 ^ (prefixWord ++ tailWord_7443069).sum := by decide
  have hdescent : baseEnd_7443069 < baseStart_7443069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443082 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 2, 5]
def baseStart_7443082 : Nat := 118140960795 + 7443082 * 2 ^ 59
def prefixEnd_7443082 : Nat := 4983230072969 + 3 ^ 40 * 7443082 * 2
def baseEnd_7443082 : Nat := 1273959538942717713714965

theorem tailTrace_7443082 : CollatzResearch.WordTrace tailWord_7443082 prefixEnd_7443082 1273959538942717713714965 := by
  unfold tailWord_7443082
  simp only [CollatzResearch.WordTrace]
  refine ⟨67867875705248141511780875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180981001880661710698082333 67867875705248141511780875)
  ·
    refine ⟨101801813557872212267671313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67867875705248141511780875 101801813557872212267671313)
    ·
      refine ⟨76351360168404159200753485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101801813557872212267671313 76351360168404159200753485)
      ·
        refine ⟨28631760063151559700282557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76351360168404159200753485 28631760063151559700282557)
        ·
          refine ⟨10736910023681834887605959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28631760063151559700282557 10736910023681834887605959)
          ·
            refine ⟨16105365035522752331408939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10736910023681834887605959 16105365035522752331408939)
            ·
              refine ⟨24158047553284128497113409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16105365035522752331408939 24158047553284128497113409)
              ·
                refine ⟨18118535664963096372835057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24158047553284128497113409 18118535664963096372835057)
                ·
                  refine ⟨13588901748722322279626293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18118535664963096372835057 13588901748722322279626293)
                  ·
                    refine ⟨1273959538942717713714965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13588901748722322279626293 1273959538942717713714965)
                    ·
                      rfl

theorem cell23_7443082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_7443082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443082 prefixEnd_7443082 := by exact prefixLift 7443082
  have htrace : WordTrace (prefixWord ++ tailWord_7443082) baseStart_7443082 baseEnd_7443082 := by
    simpa [prefixWord, tailWord_7443082, baseEnd_7443082] using wordTrace_append hprefix tailTrace_7443082
  have hstable : (prefixWord ++ tailWord_7443082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443082).length < 2 ^ (prefixWord ++ tailWord_7443082).sum := by decide
  have hdescent : baseEnd_7443082 < baseStart_7443082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443092 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_7443092 : Nat := 118140960795 + 7443092 * 2 ^ 59
def prefixEnd_7443092 : Nat := 4983230072969 + 3 ^ 40 * 7443092 * 2
def baseEnd_7443092 : Nat := 3821883751634698102019849

theorem tailTrace_7443092 : CollatzResearch.WordTrace tailWord_7443092 prefixEnd_7443092 3821883751634698102019849 := by
  unfold tailWord_7443092
  simp only [CollatzResearch.WordTrace]
  refine ⟨135735933775478168877493765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180981245033970891836658353 135735933775478168877493765)
  ·
    refine ⟨25450487582902156664530081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135735933775478168877493765 25450487582902156664530081)
    ·
      refine ⟨19087865687176617498397561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25450487582902156664530081 19087865687176617498397561)
      ·
        refine ⟨14315899265382463123798171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19087865687176617498397561 14315899265382463123798171)
        ·
          refine ⟨21473848898073694685697257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14315899265382463123798171 21473848898073694685697257)
          ·
            refine ⟨16105386673555271014272943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21473848898073694685697257 16105386673555271014272943)
            ·
              refine ⟨24158080010332906521409415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16105386673555271014272943 24158080010332906521409415)
              ·
                refine ⟨36237120015499359782114123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24158080010332906521409415 36237120015499359782114123)
                ·
                  refine ⟨54355680023249039673171185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36237120015499359782114123 54355680023249039673171185)
                  ·
                    refine ⟨40766760017436779754878389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54355680023249039673171185 40766760017436779754878389)
                    ·
                      refine ⟨3821883751634698102019849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40766760017436779754878389 3821883751634698102019849)
                      ·
                        rfl

theorem cell23_7443092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_7443092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443092 prefixEnd_7443092 := by exact prefixLift 7443092
  have htrace : WordTrace (prefixWord ++ tailWord_7443092) baseStart_7443092 baseEnd_7443092 := by
    simpa [prefixWord, tailWord_7443092, baseEnd_7443092] using wordTrace_append hprefix tailTrace_7443092
  have hstable : (prefixWord ++ tailWord_7443092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443092).length < 2 ^ (prefixWord ++ tailWord_7443092).sum := by decide
  have hdescent : baseEnd_7443092 < baseStart_7443092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443102 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_7443102 : Nat := 118140960795 + 7443102 * 2 ^ 59
def prefixEnd_7443102 : Nat := 4983230072969 + 3 ^ 40 * 7443102 * 2
def baseEnd_7443102 : Nat := 3821888886441243062894803

theorem tailTrace_7443102 : CollatzResearch.WordTrace tailWord_7443102 prefixEnd_7443102 3821888886441243062894803 := by
  unfold tailWord_7443102
  simp only [CollatzResearch.WordTrace]
  refine ⟨33934029035115013682856445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180981488187280072975234373 33934029035115013682856445)
  ·
    refine ⟨12725260888168130131071167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33934029035115013682856445 12725260888168130131071167)
    ·
      refine ⟨19087891332252195196606751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12725260888168130131071167 19087891332252195196606751)
      ·
        refine ⟨28631836998378292794910127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19087891332252195196606751 28631836998378292794910127)
        ·
          refine ⟨42947755497567439192365191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28631836998378292794910127 42947755497567439192365191)
          ·
            refine ⟨64421633246351158788547787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42947755497567439192365191 64421633246351158788547787)
            ·
              refine ⟨96632449869526738182821681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64421633246351158788547787 96632449869526738182821681)
              ·
                refine ⟨72474337402145053637116261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96632449869526738182821681 72474337402145053637116261)
                ·
                  refine ⟨13588938262902197556959299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72474337402145053637116261 13588938262902197556959299)
                  ·
                    refine ⟨20383407394353296335438949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13588938262902197556959299 20383407394353296335438949)
                    ·
                      refine ⟨3821888886441243062894803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20383407394353296335438949 3821888886441243062894803)
                      ·
                        rfl

theorem cell23_7443102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_7443102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443102 prefixEnd_7443102 := by exact prefixLift 7443102
  have htrace : WordTrace (prefixWord ++ tailWord_7443102) baseStart_7443102 baseEnd_7443102 := by
    simpa [prefixWord, tailWord_7443102, baseEnd_7443102] using wordTrace_append hprefix tailTrace_7443102
  have hstable : (prefixWord ++ tailWord_7443102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443102).length < 2 ^ (prefixWord ++ tailWord_7443102).sum := by decide
  have hdescent : baseEnd_7443102 < baseStart_7443102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443128 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_7443128 : Nat := 118140960795 + 7443128 * 2 ^ 59
def prefixEnd_7443128 : Nat := 4983230072969 + 3 ^ 40 * 7443128 * 2
def baseEnd_7443128 : Nat := 3821902236938259961169683

theorem tailTrace_7443128 : CollatzResearch.WordTrace tailWord_7443128 prefixEnd_7443128 3821902236938259961169683 := by
  unfold tailWord_7443128
  simp only [CollatzResearch.WordTrace]
  refine ⟨135736590289412957951649019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180982120385883943935532025 135736590289412957951649019)
  ·
    refine ⟨203604885434119436927473529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135736590289412957951649019 203604885434119436927473529)
    ·
      refine ⟨152703664075589577695605147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203604885434119436927473529 152703664075589577695605147)
      ·
        refine ⟨229055496113384366543407721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152703664075589577695605147 229055496113384366543407721)
        ·
          refine ⟨171791622085038274907555791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229055496113384366543407721 171791622085038274907555791)
          ·
            refine ⟨257687433127557412361333687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171791622085038274907555791 257687433127557412361333687)
            ·
              refine ⟨386531149691336118542000531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257687433127557412361333687 386531149691336118542000531)
              ·
                refine ⟨579796724537004177813000797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386531149691336118542000531 579796724537004177813000797)
                ·
                  refine ⟨217423771701376566679875299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579796724537004177813000797 217423771701376566679875299)
                  ·
                    refine ⟨326135657552064850019812949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217423771701376566679875299 326135657552064850019812949)
                    ·
                      refine ⟨3821902236938259961169683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 326135657552064850019812949 3821902236938259961169683)
                      ·
                        rfl

theorem cell23_7443128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_7443128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443128 prefixEnd_7443128 := by exact prefixLift 7443128
  have htrace : WordTrace (prefixWord ++ tailWord_7443128) baseStart_7443128 baseEnd_7443128 := by
    simpa [prefixWord, tailWord_7443128, baseEnd_7443128] using wordTrace_append hprefix tailTrace_7443128
  have hstable : (prefixWord ++ tailWord_7443128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443128).length < 2 ^ (prefixWord ++ tailWord_7443128).sum := by decide
  have hdescent : baseEnd_7443128 < baseStart_7443128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443146 : List Nat := [3, 1, 2, 1, 4, 1, 4, 2, 1, 4]
def baseStart_7443146 : Nat := 118140960795 + 7443146 * 2 ^ 59
def prefixEnd_7443146 : Nat := 4983230072969 + 3 ^ 40 * 7443146 * 2
def baseEnd_7443146 : Nat := 1273970493196680296914867

theorem tailTrace_7443146 : CollatzResearch.WordTrace tailWord_7443146 prefixEnd_7443146 1273970493196680296914867 := by
  unfold tailWord_7443146
  simp only [CollatzResearch.WordTrace]
  refine ⟨67868459273190176244363323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180982558061840469984968861 67868459273190176244363323)
  ·
    refine ⟨101802688909785264366544985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67868459273190176244363323 101802688909785264366544985)
    ·
      refine ⟨76352016682338948274908739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101802688909785264366544985 76352016682338948274908739)
      ·
        refine ⟨114528025023508422412363109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76352016682338948274908739 114528025023508422412363109)
        ·
          refine ⟨21474004691907829202318083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114528025023508422412363109 21474004691907829202318083)
          ·
            refine ⟨32211007037861743803477125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21474004691907829202318083 32211007037861743803477125)
            ·
              refine ⟨6039563819599076963151961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32211007037861743803477125 6039563819599076963151961)
              ·
                refine ⟨4529672864699307722363971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6039563819599076963151961 4529672864699307722363971)
                ·
                  refine ⟨6794509297048961583545957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529672864699307722363971 6794509297048961583545957)
                  ·
                    refine ⟨1273970493196680296914867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6794509297048961583545957 1273970493196680296914867)
                    ·
                      rfl

theorem cell23_7443146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_7443146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443146 prefixEnd_7443146 := by exact prefixLift 7443146
  have htrace : WordTrace (prefixWord ++ tailWord_7443146) baseStart_7443146 baseEnd_7443146 := by
    simpa [prefixWord, tailWord_7443146, baseEnd_7443146] using wordTrace_append hprefix tailTrace_7443146
  have hstable : (prefixWord ++ tailWord_7443146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443146).length < 2 ^ (prefixWord ++ tailWord_7443146).sum := by decide
  have hdescent : baseEnd_7443146 < baseStart_7443146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443162 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2]
def baseStart_7443162 : Nat := 118140960795 + 7443162 * 2 ^ 59
def prefixEnd_7443162 : Nat := 4983230072969 + 3 ^ 40 * 7443162 * 2
def baseEnd_7443162 : Nat := 3821919695280512828144527

theorem tailTrace_7443162 : CollatzResearch.WordTrace tailWord_7443162 prefixEnd_7443162 3821919695280512828144527 := by
  unfold tailWord_7443162
  simp only [CollatzResearch.WordTrace]
  refine ⟨67868605165175684927508935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180982947107135159806690493 67868605165175684927508935)
  ·
    refine ⟨101802907747763527391263403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67868605165175684927508935 101802907747763527391263403)
    ·
      refine ⟨152704361621645291086895105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101802907747763527391263403 152704361621645291086895105)
      ·
        refine ⟨114528271216233968315171329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152704361621645291086895105 114528271216233968315171329)
        ·
          refine ⟨85896203412175476236378497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114528271216233968315171329 85896203412175476236378497)
          ·
            refine ⟨64422152559131607177283873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85896203412175476236378497 64422152559131607177283873)
            ·
              refine ⟨48316614419348705382962905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64422152559131607177283873 48316614419348705382962905)
              ·
                refine ⟨36237460814511529037222179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48316614419348705382962905 36237460814511529037222179)
                ·
                  refine ⟨54356191221767293555833269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36237460814511529037222179 54356191221767293555833269)
                  ·
                    refine ⟨5095892927040683770859369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54356191221767293555833269 5095892927040683770859369)
                    ·
                      refine ⟨3821919695280512828144527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095892927040683770859369 3821919695280512828144527)
                      ·
                        rfl

theorem cell23_7443162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_7443162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443162 prefixEnd_7443162 := by exact prefixLift 7443162
  have htrace : WordTrace (prefixWord ++ tailWord_7443162) baseStart_7443162 baseEnd_7443162 := by
    simpa [prefixWord, tailWord_7443162, baseEnd_7443162] using wordTrace_append hprefix tailTrace_7443162
  have hstable : (prefixWord ++ tailWord_7443162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443162).length < 2 ^ (prefixWord ++ tailWord_7443162).sum := by decide
  have hdescent : baseEnd_7443162 < baseStart_7443162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443169 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_7443169 : Nat := 118140960795 + 7443169 * 2 ^ 59
def prefixEnd_7443169 : Nat := 4983230072969 + 3 ^ 40 * 7443169 * 2
def baseEnd_7443169 : Nat := 3821923289645094300756995

theorem tailTrace_7443169 : CollatzResearch.WordTrace tailWord_7443169 prefixEnd_7443169 3821923289645094300756995 := by
  unfold tailWord_7443169
  simp only [CollatzResearch.WordTrace]
  refine ⟨271474675971677379905540561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180983117314451586603693707 271474675971677379905540561)
  ·
    refine ⟨203606006978758034929155421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271474675971677379905540561 203606006978758034929155421)
    ·
      refine ⟨76352252617034263098433283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203606006978758034929155421 76352252617034263098433283)
      ·
        refine ⟨114528378925551394647649925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76352252617034263098433283 114528378925551394647649925)
        ·
          refine ⟨21474071048540886496434361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114528378925551394647649925 21474071048540886496434361)
          ·
            refine ⟨16105553286405664872325771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21474071048540886496434361 16105553286405664872325771)
            ·
              refine ⟨24158329929608497308488657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16105553286405664872325771 24158329929608497308488657)
              ·
                refine ⟨18118747447206372981366493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24158329929608497308488657 18118747447206372981366493)
                ·
                  refine ⟨6794530292702389868012435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18118747447206372981366493 6794530292702389868012435)
                  ·
                    refine ⟨10191795439053584802018653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6794530292702389868012435 10191795439053584802018653)
                    ·
                      refine ⟨3821923289645094300756995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10191795439053584802018653 3821923289645094300756995)
                      ·
                        rfl

theorem cell23_7443169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_7443169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443169 prefixEnd_7443169 := by exact prefixLift 7443169
  have htrace : WordTrace (prefixWord ++ tailWord_7443169) baseStart_7443169 baseEnd_7443169 := by
    simpa [prefixWord, tailWord_7443169, baseEnd_7443169] using wordTrace_append hprefix tailTrace_7443169
  have hstable : (prefixWord ++ tailWord_7443169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443169).length < 2 ^ (prefixWord ++ tailWord_7443169).sum := by decide
  have hdescent : baseEnd_7443169 < baseStart_7443169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443185 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 1, 6]
def baseStart_7443185 : Nat := 118140960795 + 7443185 * 2 ^ 59
def prefixEnd_7443185 : Nat := 4983230072969 + 3 ^ 40 * 7443185 * 2
def baseEnd_7443185 : Nat := 1273977168445188746052307

theorem tailTrace_7443185 : CollatzResearch.WordTrace tailWord_7443185 prefixEnd_7443185 1273977168445188746052307 := by
  unfold tailWord_7443185
  simp only [CollatzResearch.WordTrace]
  refine ⟨271475259539619414638123009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180983506359746276425415339 271475259539619414638123009)
  ·
    refine ⟨203606444654714560978592257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271475259539619414638123009 203606444654714560978592257)
    ·
      refine ⟨152704833491035920733944193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203606444654714560978592257 152704833491035920733944193)
      ·
        refine ⟨114528625118276940550458145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152704833491035920733944193 114528625118276940550458145)
        ·
          refine ⟨85896468838707705412843609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114528625118276940550458145 85896468838707705412843609)
          ·
            refine ⟨64422351629030779059632707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85896468838707705412843609 64422351629030779059632707)
            ·
              refine ⟨96633527443546168589449061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64422351629030779059632707 96633527443546168589449061)
              ·
                refine ⟨18118786395664906610521699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96633527443546168589449061 18118786395664906610521699)
                ·
                  refine ⟨27178179593497359915782549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18118786395664906610521699 27178179593497359915782549)
                  ·
                    refine ⟨1273977168445188746052307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27178179593497359915782549 1273977168445188746052307)
                    ·
                      rfl

theorem cell23_7443185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_7443185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443185 prefixEnd_7443185 := by exact prefixLift 7443185
  have htrace : WordTrace (prefixWord ++ tailWord_7443185) baseStart_7443185 baseEnd_7443185 := by
    simpa [prefixWord, tailWord_7443185, baseEnd_7443185] using wordTrace_append hprefix tailTrace_7443185
  have hstable : (prefixWord ++ tailWord_7443185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443185).length < 2 ^ (prefixWord ++ tailWord_7443185).sum := by decide
  have hdescent : baseEnd_7443185 < baseStart_7443185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443186 : List Nat := [3, 2, 1, 3, 1, 2, 1, 5, 1, 1, 3]
def baseStart_7443186 : Nat := 118140960795 + 7443186 * 2 ^ 59
def prefixEnd_7443186 : Nat := 4983230072969 + 3 ^ 40 * 7443186 * 2
def baseEnd_7443186 : Nat := 3821932018816220734244417

theorem tailTrace_7443186 : CollatzResearch.WordTrace tailWord_7443186 prefixEnd_7443186 3821932018816220734244417 := by
  unfold tailWord_7443186
  simp only [CollatzResearch.WordTrace]
  refine ⟨67868824003153947952227353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180983530675077194539272941 67868824003153947952227353)
  ·
    refine ⟨50901618002365460964170515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67868824003153947952227353 50901618002365460964170515)
    ·
      refine ⟨76352427003548191446255773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50901618002365460964170515 76352427003548191446255773)
      ·
        refine ⟨28632160126330571792345915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76352427003548191446255773 28632160126330571792345915)
        ·
          refine ⟨42948240189495857688518873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28632160126330571792345915 42948240189495857688518873)
          ·
            refine ⟨32211180142121893266389155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42948240189495857688518873 32211180142121893266389155)
            ·
              refine ⟨48316770213182839899583733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32211180142121893266389155 48316770213182839899583733)
              ·
                refine ⟨4529697207485891240585975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48316770213182839899583733 4529697207485891240585975)
                ·
                  refine ⟨6794545811228836860878963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529697207485891240585975 6794545811228836860878963)
                  ·
                    refine ⟨10191818716843255291318445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6794545811228836860878963 10191818716843255291318445)
                    ·
                      refine ⟨3821932018816220734244417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10191818716843255291318445 3821932018816220734244417)
                      ·
                        rfl

theorem cell23_7443186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_7443186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443186 prefixEnd_7443186 := by exact prefixLift 7443186
  have htrace : WordTrace (prefixWord ++ tailWord_7443186) baseStart_7443186 baseEnd_7443186 := by
    simpa [prefixWord, tailWord_7443186, baseEnd_7443186] using wordTrace_append hprefix tailTrace_7443186
  have hstable : (prefixWord ++ tailWord_7443186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443186).length < 2 ^ (prefixWord ++ tailWord_7443186).sum := by decide
  have hdescent : baseEnd_7443186 < baseStart_7443186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443192 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 1, 1, 4]
def baseStart_7443192 : Nat := 118140960795 + 7443192 * 2 ^ 59
def prefixEnd_7443192 : Nat := 4983230072969 + 3 ^ 40 * 7443192 * 2
def baseEnd_7443192 : Nat := 3821935099700147710769389

theorem tailTrace_7443192 : CollatzResearch.WordTrace tailWord_7443192 prefixEnd_7443192 3821935099700147710769389 := by
  unfold tailWord_7443192
  simp only [CollatzResearch.WordTrace]
  refine ⟨135737757425297027416813915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180983676567062703222418553 135737757425297027416813915)
  ·
    refine ⟨203606636137945541125220873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135737757425297027416813915 203606636137945541125220873)
    ·
      refine ⟨152704977103459155843915655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203606636137945541125220873 152704977103459155843915655)
      ·
        refine ⟨229057465655188733765873483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152704977103459155843915655 229057465655188733765873483)
        ·
          refine ⟨343586198482783100648810225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229057465655188733765873483 343586198482783100648810225)
          ·
            refine ⟨257689648862087325486607669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343586198482783100648810225 257689648862087325486607669)
            ·
              refine ⟨24158404580820686764369469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257689648862087325486607669 24158404580820686764369469)
              ·
                refine ⟨9059401717807757536638551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24158404580820686764369469 9059401717807757536638551)
                ·
                  refine ⟨13589102576711636304957827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9059401717807757536638551 13589102576711636304957827)
                  ·
                    refine ⟨20383653865067454457436741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13589102576711636304957827 20383653865067454457436741)
                    ·
                      refine ⟨3821935099700147710769389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20383653865067454457436741 3821935099700147710769389)
                      ·
                        rfl

theorem cell23_7443192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_7443192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443192 prefixEnd_7443192 := by exact prefixLift 7443192
  have htrace : WordTrace (prefixWord ++ tailWord_7443192) baseStart_7443192 baseEnd_7443192 := by
    simpa [prefixWord, tailWord_7443192, baseEnd_7443192] using wordTrace_append hprefix tailTrace_7443192
  have hstable : (prefixWord ++ tailWord_7443192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443192).length < 2 ^ (prefixWord ++ tailWord_7443192).sum := by decide
  have hdescent : baseEnd_7443192 < baseStart_7443192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443205 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_7443205 : Nat := 118140960795 + 7443205 * 2 ^ 59
def prefixEnd_7443205 : Nat := 4983230072969 + 3 ^ 40 * 7443205 * 2
def baseEnd_7443205 : Nat := 3821941774948656159906829

theorem tailTrace_7443205 : CollatzResearch.WordTrace tailWord_7443205 prefixEnd_7443205 3821941774948656159906829 := by
  unfold tailWord_7443205
  simp only [CollatzResearch.WordTrace]
  refine ⟨271475988999546958053851069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180983992666364638702567379 271475988999546958053851069)
  ·
    refine ⟨101803495874830109270194151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271475988999546958053851069 101803495874830109270194151)
    ·
      refine ⟨152705243812245163905291227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101803495874830109270194151 152705243812245163905291227)
      ·
        refine ⟨229057865718367745857936841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152705243812245163905291227 229057865718367745857936841)
        ·
          refine ⟨171793399288775809393452631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229057865718367745857936841 171793399288775809393452631)
          ·
            refine ⟨257690098933163714090178947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171793399288775809393452631 257690098933163714090178947)
            ·
              refine ⟨386535148399745571135268421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257690098933163714090178947 386535148399745571135268421)
              ·
                refine ⟨72475340324952294587862829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 386535148399745571135268421 72475340324952294587862829)
                ·
                  refine ⟨27178252621857110470448561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72475340324952294587862829 27178252621857110470448561)
                  ·
                    refine ⟨20383689466392832852836421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27178252621857110470448561 20383689466392832852836421)
                    ·
                      refine ⟨3821941774948656159906829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20383689466392832852836421 3821941774948656159906829)
                      ·
                        rfl

theorem cell23_7443205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_7443205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443205 prefixEnd_7443205 := by exact prefixLift 7443205
  have htrace : WordTrace (prefixWord ++ tailWord_7443205) baseStart_7443205 baseEnd_7443205 := by
    simpa [prefixWord, tailWord_7443205, baseEnd_7443205] using wordTrace_append hprefix tailTrace_7443205
  have hstable : (prefixWord ++ tailWord_7443205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443205).length < 2 ^ (prefixWord ++ tailWord_7443205).sum := by decide
  have hdescent : baseEnd_7443205 < baseStart_7443205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443209 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 3, 2, 2]
def baseStart_7443209 : Nat := 118140960795 + 7443209 * 2 ^ 59
def prefixEnd_7443209 : Nat := 4983230072969 + 3 ^ 40 * 7443209 * 2
def baseEnd_7443209 : Nat := 3821943828871274144256811

theorem tailTrace_7443209 : CollatzResearch.WordTrace tailWord_7443209 prefixEnd_7443209 3821943828871274144256811 := by
  unfold tailWord_7443209
  simp only [CollatzResearch.WordTrace]
  refine ⟨271476134891532466736996681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180984089927688311157997787 271476134891532466736996681)
  ·
    refine ⟨203607101168649350052747511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271476134891532466736996681 203607101168649350052747511)
    ·
      refine ⟨305410651752974025079121267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203607101168649350052747511 305410651752974025079121267)
      ·
        refine ⟨458115977629461037618681901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305410651752974025079121267 458115977629461037618681901)
        ·
          refine ⟨171793491611047889107005713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458115977629461037618681901 171793491611047889107005713)
          ·
            refine ⟨128845118708285916830254285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171793491611047889107005713 128845118708285916830254285)
            ·
              refine ⟨48316919515607218811345357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128845118708285916830254285 48316919515607218811345357)
              ·
                refine ⟨18118844818352707054254509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48316919515607218811345357 18118844818352707054254509)
                ·
                  refine ⟨6794566806882265145345441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18118844818352707054254509 6794566806882265145345441)
                  ·
                    refine ⟨5095925105161698859009081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6794566806882265145345441 5095925105161698859009081)
                    ·
                      refine ⟨3821943828871274144256811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095925105161698859009081 3821943828871274144256811)
                      ·
                        rfl

theorem cell23_7443209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 2, 2].length) (baseStart_7443209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443209 prefixEnd_7443209 := by exact prefixLift 7443209
  have htrace : WordTrace (prefixWord ++ tailWord_7443209) baseStart_7443209 baseEnd_7443209 := by
    simpa [prefixWord, tailWord_7443209, baseEnd_7443209] using wordTrace_append hprefix tailTrace_7443209
  have hstable : (prefixWord ++ tailWord_7443209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443209).length < 2 ^ (prefixWord ++ tailWord_7443209).sum := by decide
  have hdescent : baseEnd_7443209 < baseStart_7443209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443219 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 2, 4]
def baseStart_7443219 : Nat := 118140960795 + 7443219 * 2 ^ 59
def prefixEnd_7443219 : Nat := 4983230072969 + 3 ^ 40 * 7443219 * 2
def baseEnd_7443219 : Nat := 1273982987892606368377255

theorem tailTrace_7443219 : CollatzResearch.WordTrace tailWord_7443219 prefixEnd_7443219 1273982987892606368377255 := by
  unfold tailWord_7443219
  simp only [CollatzResearch.WordTrace]
  refine ⟨271476499621496238444860711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180984333080997492296573807 271476499621496238444860711)
  ·
    refine ⟨407214749432244357667291067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271476499621496238444860711 407214749432244357667291067)
    ·
      refine ⟨610822124148366536500936601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407214749432244357667291067 610822124148366536500936601)
      ·
        refine ⟨458116593111274902375702451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610822124148366536500936601 458116593111274902375702451)
        ·
          refine ⟨687174889666912353563553677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458116593111274902375702451 687174889666912353563553677)
          ·
            refine ⟨257690583625092132586332629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 687174889666912353563553677 257690583625092132586332629)
            ·
              refine ⟨6039623053713096857492171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 257690583625092132586332629 6039623053713096857492171)
              ·
                refine ⟨9059434580569645286238257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6039623053713096857492171 9059434580569645286238257)
                ·
                  refine ⟨6794575935427233964678693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9059434580569645286238257 6794575935427233964678693)
                  ·
                    refine ⟨1273982987892606368377255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6794575935427233964678693 1273982987892606368377255)
                    ·
                      rfl

theorem cell23_7443219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 2, 4].length) (baseStart_7443219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443219 prefixEnd_7443219 := by exact prefixLift 7443219
  have htrace : WordTrace (prefixWord ++ tailWord_7443219) baseStart_7443219 baseEnd_7443219 := by
    simpa [prefixWord, tailWord_7443219, baseEnd_7443219] using wordTrace_append hprefix tailTrace_7443219
  have hstable : (prefixWord ++ tailWord_7443219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443219).length < 2 ^ (prefixWord ++ tailWord_7443219).sum := by decide
  have hdescent : baseEnd_7443219 < baseStart_7443219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443232 : List Nat := [2, 1, 1, 5, 1, 2, 4, 7]
def baseStart_7443232 : Nat := 118140960795 + 7443232 * 2 ^ 59
def prefixEnd_7443232 : Nat := 4983230072969 + 3 ^ 40 * 7443232 * 2
def baseEnd_7443232 : Nat := 141553912552826946454415

theorem tailTrace_7443232 : CollatzResearch.WordTrace tailWord_7443232 prefixEnd_7443232 141553912552826946454415 := by
  unfold tailWord_7443232
  simp only [CollatzResearch.WordTrace]
  refine ⟨135738486885224570832541975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180984649180299427776722633 135738486885224570832541975)
  ·
    refine ⟨203607730327836856248812963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135738486885224570832541975 203607730327836856248812963)
    ·
      refine ⟨305411595491755284373219445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203607730327836856248812963 305411595491755284373219445)
      ·
        refine ⟨28632337077352057909989323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 305411595491755284373219445 28632337077352057909989323)
        ·
          refine ⟨42948505616028086864983985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28632337077352057909989323 42948505616028086864983985)
          ·
            refine ⟨32211379212021065148737989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42948505616028086864983985 32211379212021065148737989)
            ·
              refine ⟨6039633602253949715388373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32211379212021065148737989 6039633602253949715388373)
              ·
                refine ⟨141553912552826946454415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6039633602253949715388373 141553912552826946454415)
                ·
                  rfl

theorem cell23_7443232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 7].length) (baseStart_7443232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443232 prefixEnd_7443232 := by exact prefixLift 7443232
  have htrace : WordTrace (prefixWord ++ tailWord_7443232) baseStart_7443232 baseEnd_7443232 := by
    simpa [prefixWord, tailWord_7443232, baseEnd_7443232] using wordTrace_append hprefix tailTrace_7443232
  have hstable : (prefixWord ++ tailWord_7443232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443232).length < 2 ^ (prefixWord ++ tailWord_7443232).sum := by decide
  have hdescent : baseEnd_7443232 < baseStart_7443232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443246 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7443246 : Nat := 118140960795 + 7443246 * 2 ^ 59
def prefixEnd_7443246 : Nat := 4983230072969 + 3 ^ 40 * 7443246 * 2
def baseEnd_7443246 : Nat := 3821962827655490499494141

theorem tailTrace_7443246 : CollatzResearch.WordTrace tailWord_7443246 prefixEnd_7443246 3821962827655490499494141 := by
  unfold tailWord_7443246
  simp only [CollatzResearch.WordTrace]
  refine ⟨33934685549049802757011699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180984989594932281370729061 33934685549049802757011699)
  ·
    refine ⟨50902028323574704135517549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33934685549049802757011699 50902028323574704135517549)
    ·
      refine ⟨19088260621340514050819081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50902028323574704135517549 19088260621340514050819081)
      ·
        refine ⟨14316195466005385538114311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19088260621340514050819081 14316195466005385538114311)
        ·
          refine ⟨21474293199008078307171467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14316195466005385538114311 21474293199008078307171467)
          ·
            refine ⟨32211439798512117460757201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21474293199008078307171467 32211439798512117460757201)
            ·
              refine ⟨24158579848884088095567901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32211439798512117460757201 24158579848884088095567901)
              ·
                refine ⟨9059467443331533035837963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24158579848884088095567901 9059467443331533035837963)
                ·
                  refine ⟨13589201164997299553756945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9059467443331533035837963 13589201164997299553756945)
                  ·
                    refine ⟨10191900873747974665317709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13589201164997299553756945 10191900873747974665317709)
                    ·
                      refine ⟨3821962827655490499494141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10191900873747974665317709 3821962827655490499494141)
                      ·
                        rfl

theorem cell23_7443246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7443246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443246 prefixEnd_7443246 := by exact prefixLift 7443246
  have htrace : WordTrace (prefixWord ++ tailWord_7443246) baseStart_7443246 baseEnd_7443246 := by
    simpa [prefixWord, tailWord_7443246, baseEnd_7443246] using wordTrace_append hprefix tailTrace_7443246
  have hstable : (prefixWord ++ tailWord_7443246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443246).length < 2 ^ (prefixWord ++ tailWord_7443246).sum := by decide
  have hdescent : baseEnd_7443246 < baseStart_7443246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443255 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_7443255 : Nat := 118140960795 + 7443255 * 2 ^ 59
def prefixEnd_7443255 : Nat := 4983230072969 + 3 ^ 40 * 7443255 * 2
def baseEnd_7443255 : Nat := 3821967448981380964281599

theorem tailTrace_7443255 : CollatzResearch.WordTrace tailWord_7443255 prefixEnd_7443255 3821967448981380964281599 := by
  unfold tailWord_7443255
  simp only [CollatzResearch.WordTrace]
  refine ⟨271477812649365816593171219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180985208432910544395447479 271477812649365816593171219)
  ·
    refine ⟨407216718974048724889756829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271477812649365816593171219 407216718974048724889756829)
    ·
      refine ⟨152706269615268271833658811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407216718974048724889756829 152706269615268271833658811)
      ·
        refine ⟨229059404422902407750488217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152706269615268271833658811 229059404422902407750488217)
        ·
          refine ⟨171794553317176805812866163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229059404422902407750488217 171794553317176805812866163)
          ·
            refine ⟨257691829975765208719299245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171794553317176805812866163 257691829975765208719299245)
            ·
              refine ⟨96634436240911953269737217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257691829975765208719299245 96634436240911953269737217)
              ·
                refine ⟨72475827180683964952302913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96634436240911953269737217 72475827180683964952302913)
                ·
                  refine ⟨54356870385512973714227185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72475827180683964952302913 54356870385512973714227185)
                  ·
                    refine ⟨40767652789134730285670389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54356870385512973714227185 40767652789134730285670389)
                    ·
                      refine ⟨3821967448981380964281599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40767652789134730285670389 3821967448981380964281599)
                      ·
                        rfl

theorem cell23_7443255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_7443255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443255 prefixEnd_7443255 := by exact prefixLift 7443255
  have htrace : WordTrace (prefixWord ++ tailWord_7443255) baseStart_7443255 baseEnd_7443255 := by
    simpa [prefixWord, tailWord_7443255, baseEnd_7443255] using wordTrace_append hprefix tailTrace_7443255
  have hstable : (prefixWord ++ tailWord_7443255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443255).length < 2 ^ (prefixWord ++ tailWord_7443255).sum := by decide
  have hdescent : baseEnd_7443255 < baseStart_7443255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443276 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 2, 1, 3]
def baseStart_7443276 : Nat := 118140960795 + 7443276 * 2 ^ 59
def prefixEnd_7443276 : Nat := 4983230072969 + 3 ^ 40 * 7443276 * 2
def baseEnd_7443276 : Nat := 3821978232075125382119003

theorem tailTrace_7443276 : CollatzResearch.WordTrace tailWord_7443276 prefixEnd_7443276 3821978232075125382119003 := by
  unfold tailWord_7443276
  simp only [CollatzResearch.WordTrace]
  refine ⟨135739289291144868589842841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180985719054859824786457121 135739289291144868589842841)
  ·
    refine ⟨101804466968358651442382131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135739289291144868589842841 101804466968358651442382131)
    ·
      refine ⟨152706700452537977163573197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101804466968358651442382131 152706700452537977163573197)
      ·
        refine ⟨57265012669701741436339949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152706700452537977163573197 57265012669701741436339949)
        ·
          refine ⟨21474379751138153038627481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57265012669701741436339949 21474379751138153038627481)
          ·
            refine ⟨16105784813353614778970611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21474379751138153038627481 16105784813353614778970611)
            ·
              refine ⟨24158677220030422168455917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16105784813353614778970611 24158677220030422168455917)
              ·
                refine ⟨9059503957511408313170969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24158677220030422168455917 9059503957511408313170969)
                ·
                  refine ⟨6794627968133556234878227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9059503957511408313170969 6794627968133556234878227)
                  ·
                    refine ⟨10191941952200334352317341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6794627968133556234878227 10191941952200334352317341)
                    ·
                      refine ⟨3821978232075125382119003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10191941952200334352317341 3821978232075125382119003)
                      ·
                        rfl

theorem cell23_7443276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_7443276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443276 prefixEnd_7443276 := by exact prefixLift 7443276
  have htrace : WordTrace (prefixWord ++ tailWord_7443276) baseStart_7443276 baseEnd_7443276 := by
    simpa [prefixWord, tailWord_7443276, baseEnd_7443276] using wordTrace_append hprefix tailTrace_7443276
  have hstable : (prefixWord ++ tailWord_7443276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443276).length < 2 ^ (prefixWord ++ tailWord_7443276).sum := by decide
  have hdescent : baseEnd_7443276 < baseStart_7443276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443299 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 3, 4, 2]
def baseStart_7443299 : Nat := 118140960795 + 7443299 * 2 ^ 59
def prefixEnd_7443299 : Nat := 4983230072969 + 3 ^ 40 * 7443299 * 2
def baseEnd_7443299 : Nat := 3821990042130178792131397

theorem tailTrace_7443299 : CollatzResearch.WordTrace tailWord_7443299 prefixEnd_7443299 3821990042130178792131397 := by
  unfold tailWord_7443299
  simp only [CollatzResearch.WordTrace]
  refine ⟨271479417461206412107772951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180986278307470941405181967 271479417461206412107772951)
  ·
    refine ⟨407219126191809618161659427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271479417461206412107772951 407219126191809618161659427)
    ·
      refine ⟨610828689287714427242489141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407219126191809618161659427 610828689287714427242489141)
      ·
        refine ⟨57265189620723227553983357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 610828689287714427242489141 57265189620723227553983357)
        ·
          refine ⟨21474446107771210332743759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57265189620723227553983357 21474446107771210332743759)
          ·
            refine ⟨32211669161656815499115639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21474446107771210332743759 32211669161656815499115639)
            ·
              refine ⟨48317503742485223248673459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32211669161656815499115639 48317503742485223248673459)
              ·
                refine ⟨72476255613727834873010189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48317503742485223248673459 72476255613727834873010189)
                ·
                  refine ⟨27178595855147938077378821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72476255613727834873010189 27178595855147938077378821)
                  ·
                    refine ⟨5095986722840238389508529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27178595855147938077378821 5095986722840238389508529)
                    ·
                      refine ⟨3821990042130178792131397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095986722840238389508529 3821990042130178792131397)
                      ·
                        rfl

theorem cell23_7443299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_7443299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443299 prefixEnd_7443299 := by exact prefixLift 7443299
  have htrace : WordTrace (prefixWord ++ tailWord_7443299) baseStart_7443299 baseEnd_7443299 := by
    simpa [prefixWord, tailWord_7443299, baseEnd_7443299] using wordTrace_append hprefix tailTrace_7443299
  have hstable : (prefixWord ++ tailWord_7443299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443299).length < 2 ^ (prefixWord ++ tailWord_7443299).sum := by decide
  have hdescent : baseEnd_7443299 < baseStart_7443299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443303 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_7443303 : Nat := 118140960795 + 7443303 * 2 ^ 59
def prefixEnd_7443303 : Nat := 4983230072969 + 3 ^ 40 * 7443303 * 2
def baseEnd_7443303 : Nat := 3821992096052796776481379

theorem tailTrace_7443303 : CollatzResearch.WordTrace tailWord_7443303 prefixEnd_7443303 3821992096052796776481379 := by
  unfold tailWord_7443303
  simp only [CollatzResearch.WordTrace]
  refine ⟨271479563353191920790918563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180986375568794613860612375 271479563353191920790918563)
  ·
    refine ⟨407219345029787881186377845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271479563353191920790918563 407219345029787881186377845)
    ·
      refine ⟨38176813596542613861222923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 407219345029787881186377845 38176813596542613861222923)
      ·
        refine ⟨57265220394813920791834385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38176813596542613861222923 57265220394813920791834385)
        ·
          refine ⟨42948915296110440593875789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57265220394813920791834385 42948915296110440593875789)
          ·
            refine ⟨16105843236041415222703421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42948915296110440593875789 16105843236041415222703421)
            ·
              refine ⟨6039691213515530708513783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16105843236041415222703421 6039691213515530708513783)
              ·
                refine ⟨9059536820273296062770675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6039691213515530708513783 9059536820273296062770675)
                ·
                  refine ⟨13589305230409944094156013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9059536820273296062770675 13589305230409944094156013)
                  ·
                    refine ⟨5095989461403729035308505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13589305230409944094156013 5095989461403729035308505)
                    ·
                      refine ⟨3821992096052796776481379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5095989461403729035308505 3821992096052796776481379)
                      ·
                        rfl

theorem cell23_7443303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_7443303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443303 prefixEnd_7443303 := by exact prefixLift 7443303
  have htrace : WordTrace (prefixWord ++ tailWord_7443303) baseStart_7443303 baseEnd_7443303 := by
    simpa [prefixWord, tailWord_7443303, baseEnd_7443303] using wordTrace_append hprefix tailTrace_7443303
  have hstable : (prefixWord ++ tailWord_7443303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443303).length < 2 ^ (prefixWord ++ tailWord_7443303).sum := by decide
  have hdescent : baseEnd_7443303 < baseStart_7443303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443315 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 7]
def baseStart_7443315 : Nat := 118140960795 + 7443315 * 2 ^ 59
def prefixEnd_7443315 : Nat := 4983230072969 + 3 ^ 40 * 7443315 * 2
def baseEnd_7443315 : Nat := 3821998257820650729531323

theorem tailTrace_7443315 : CollatzResearch.WordTrace tailWord_7443315 prefixEnd_7443315 3821998257820650729531323 := by
  unfold tailWord_7443315
  simp only [CollatzResearch.WordTrace]
  refine ⟨271480001029148446840355399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180986667352765631226903599 271480001029148446840355399)
  ·
    refine ⟨407220001543722670260533099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271480001029148446840355399 407220001543722670260533099)
    ·
      refine ⟨610830002315584005390799649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407220001543722670260533099 610830002315584005390799649)
      ·
        refine ⟨458122501736688004043099737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610830002315584005390799649 458122501736688004043099737)
        ·
          refine ⟨343591876302516003032324803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458122501736688004043099737 343591876302516003032324803)
          ·
            refine ⟨515387814453774004548487205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343591876302516003032324803 515387814453774004548487205)
            ·
              refine ⟨96635215210082625852841351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 515387814453774004548487205 96635215210082625852841351)
              ·
                refine ⟨144952822815123938779262027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96635215210082625852841351 144952822815123938779262027)
                ·
                  refine ⟨217429234222685908168893041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144952822815123938779262027 217429234222685908168893041)
                  ·
                    refine ⟨163071925667014431126669781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217429234222685908168893041 163071925667014431126669781)
                    ·
                      refine ⟨3821998257820650729531323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163071925667014431126669781 3821998257820650729531323)
                      ·
                        rfl

theorem cell23_7443315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_7443315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443315 prefixEnd_7443315 := by exact prefixLift 7443315
  have htrace : WordTrace (prefixWord ++ tailWord_7443315) baseStart_7443315 baseEnd_7443315 := by
    simpa [prefixWord, tailWord_7443315, baseEnd_7443315] using wordTrace_append hprefix tailTrace_7443315
  have hstable : (prefixWord ++ tailWord_7443315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443315).length < 2 ^ (prefixWord ++ tailWord_7443315).sum := by decide
  have hdescent : baseEnd_7443315 < baseStart_7443315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443326 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7443326 : Nat := 118140960795 + 7443326 * 2 ^ 59
def prefixEnd_7443326 : Nat := 4983230072969 + 3 ^ 40 * 7443326 * 2
def baseEnd_7443326 : Nat := 1274001302035950062164591

theorem tailTrace_7443326 : CollatzResearch.WordTrace tailWord_7443326 prefixEnd_7443326 1274001302035950062164591 := by
  unfold tailWord_7443326
  simp only [CollatzResearch.WordTrace]
  refine ⟨33935050279013574464875729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180986934821405730479337221 33935050279013574464875729)
  ·
    refine ⟨25451287709260180848656797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33935050279013574464875729 25451287709260180848656797)
    ·
      refine ⟨9544232890972567818246299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25451287709260180848656797 9544232890972567818246299)
      ·
        refine ⟨14316349336458851727369449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9544232890972567818246299 14316349336458851727369449)
        ·
          refine ⟨10737262002344138795527087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14316349336458851727369449 10737262002344138795527087)
          ·
            refine ⟨16105893003516208193290631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10737262002344138795527087 16105893003516208193290631)
            ·
              refine ⟨24158839505274312289935947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16105893003516208193290631 24158839505274312289935947)
              ·
                refine ⟨36238259257911468434903921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24158839505274312289935947 36238259257911468434903921)
                ·
                  refine ⟨27178694443433601326177941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36238259257911468434903921 27178694443433601326177941)
                  ·
                    refine ⟨1274001302035950062164591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27178694443433601326177941 1274001302035950062164591)
                    ·
                      rfl

theorem cell23_7443326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7443326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443326 prefixEnd_7443326 := by exact prefixLift 7443326
  have htrace : WordTrace (prefixWord ++ tailWord_7443326) baseStart_7443326 baseEnd_7443326 := by
    simpa [prefixWord, tailWord_7443326, baseEnd_7443326] using wordTrace_append hprefix tailTrace_7443326
  have hstable : (prefixWord ++ tailWord_7443326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443326).length < 2 ^ (prefixWord ++ tailWord_7443326).sum := by decide
  have hdescent : baseEnd_7443326 < baseStart_7443326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443350 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7443350 : Nat := 118140960795 + 7443350 * 2 ^ 59
def prefixEnd_7443350 : Nat := 4983230072969 + 3 ^ 40 * 7443350 * 2
def baseEnd_7443350 : Nat := 3822016229643558092593663

theorem tailTrace_7443350 : CollatzResearch.WordTrace tailWord_7443350 prefixEnd_7443350 3822016229643558092593663 := by
  unfold tailWord_7443350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16967579849001352988617469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180987518389347765211919669 16967579849001352988617469)
  ·
    refine ⟨6362842443375507370731551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16967579849001352988617469 6362842443375507370731551)
    ·
      refine ⟨9544263665063261056097327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6362842443375507370731551 9544263665063261056097327)
      ·
        refine ⟨14316395497594891584145991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9544263665063261056097327 14316395497594891584145991)
        ·
          refine ⟨21474593246392337376218987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14316395497594891584145991 21474593246392337376218987)
          ·
            refine ⟨32211889869588506064328481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21474593246392337376218987 32211889869588506064328481)
            ·
              refine ⟨24158917402191379548246361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32211889869588506064328481 24158917402191379548246361)
              ·
                refine ⟨18119188051643534661184771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24158917402191379548246361 18119188051643534661184771)
                ·
                  refine ⟨27178782077465301991777157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18119188051643534661184771 27178782077465301991777157)
                  ·
                    refine ⟨5096021639524744123458217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27178782077465301991777157 5096021639524744123458217)
                    ·
                      refine ⟨3822016229643558092593663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096021639524744123458217 3822016229643558092593663)
                      ·
                        rfl

theorem cell23_7443350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7443350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443350 prefixEnd_7443350 := by exact prefixLift 7443350
  have htrace : WordTrace (prefixWord ++ tailWord_7443350) baseStart_7443350 baseEnd_7443350 := by
    simpa [prefixWord, tailWord_7443350, baseEnd_7443350] using wordTrace_append hprefix tailTrace_7443350
  have hstable : (prefixWord ++ tailWord_7443350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443350).length < 2 ^ (prefixWord ++ tailWord_7443350).sum := by decide
  have hdescent : baseEnd_7443350 < baseStart_7443350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443367 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_7443367 : Nat := 118140960795 + 7443367 * 2 ^ 59
def prefixEnd_7443367 : Nat := 4983230072969 + 3 ^ 40 * 7443367 * 2
def baseEnd_7443367 : Nat := 3822024958814684526081085

theorem tailTrace_7443367 : CollatzResearch.WordTrace tailWord_7443367 prefixEnd_7443367 3822024958814684526081085 := by
  unfold tailWord_7443367
  simp only [CollatzResearch.WordTrace]
  refine ⟨271481897624960059721248355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180987931749973373147498903 271481897624960059721248355)
  ·
    refine ⟨407222846437440089581872533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271481897624960059721248355 407222846437440089581872533)
    ·
      refine ⟨19088570926755004199150275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 407222846437440089581872533 19088570926755004199150275)
      ·
        refine ⟨28632856390132506298725413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19088570926755004199150275 28632856390132506298725413)
        ·
          refine ⟨5368660573149844931011015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28632856390132506298725413 5368660573149844931011015)
          ·
            refine ⟨8052990859724767396516523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5368660573149844931011015 8052990859724767396516523)
            ·
              refine ⟨12079486289587151094774785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8052990859724767396516523 12079486289587151094774785)
              ·
                refine ⟨9059614717190363321081089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12079486289587151094774785 9059614717190363321081089)
                ·
                  refine ⟨6794711037892772490810817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9059614717190363321081089 6794711037892772490810817)
                  ·
                    refine ⟨5096033278419579368108113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6794711037892772490810817 5096033278419579368108113)
                    ·
                      refine ⟨3822024958814684526081085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096033278419579368108113 3822024958814684526081085)
                      ·
                        rfl

theorem cell23_7443367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_7443367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443367 prefixEnd_7443367 := by exact prefixLift 7443367
  have htrace : WordTrace (prefixWord ++ tailWord_7443367) baseStart_7443367 baseEnd_7443367 := by
    simpa [prefixWord, tailWord_7443367, baseEnd_7443367] using wordTrace_append hprefix tailTrace_7443367
  have hstable : (prefixWord ++ tailWord_7443367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443367).length < 2 ^ (prefixWord ++ tailWord_7443367).sum := by decide
  have hdescent : baseEnd_7443367 < baseStart_7443367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443399 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 3, 4]
def baseStart_7443399 : Nat := 118140960795 + 7443399 * 2 ^ 59
def prefixEnd_7443399 : Nat := 4983230072969 + 3 ^ 40 * 7443399 * 2
def baseEnd_7443399 : Nat := 1274013796731876133626979

theorem tailTrace_7443399 : CollatzResearch.WordTrace tailWord_7443399 prefixEnd_7443399 1274013796731876133626979 := by
  unfold tailWord_7443399
  simp only [CollatzResearch.WordTrace]
  refine ⟨271483064760844129186413251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180988709840562752790942167 271483064760844129186413251)
  ·
    refine ⟨407224597141266193779619877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271483064760844129186413251 407224597141266193779619877)
    ·
      refine ⟨76354611963987411333678727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407224597141266193779619877 76354611963987411333678727)
      ·
        refine ⟨114531917945981117000518091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76354611963987411333678727 114531917945981117000518091)
        ·
          refine ⟨171797876918971675500777137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114531917945981117000518091 171797876918971675500777137)
          ·
            refine ⟨128848407689228756625582853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171797876918971675500777137 128848407689228756625582853)
            ·
              refine ⟨24159076441730391867296785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128848407689228756625582853 24159076441730391867296785)
              ·
                refine ⟨18119307331297793900472589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24159076441730391867296785 18119307331297793900472589)
                ·
                  refine ⟨6794740249236672712677221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18119307331297793900472589 6794740249236672712677221)
                  ·
                    refine ⟨1274013796731876133626979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6794740249236672712677221 1274013796731876133626979)
                    ·
                      rfl

theorem cell23_7443399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_7443399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443399 prefixEnd_7443399 := by exact prefixLift 7443399
  have htrace : WordTrace (prefixWord ++ tailWord_7443399) baseStart_7443399 baseEnd_7443399 := by
    simpa [prefixWord, tailWord_7443399, baseEnd_7443399] using wordTrace_append hprefix tailTrace_7443399
  have hstable : (prefixWord ++ tailWord_7443399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443399).length < 2 ^ (prefixWord ++ tailWord_7443399).sum := by decide
  have hdescent : baseEnd_7443399 < baseStart_7443399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443402 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_7443402 : Nat := 118140960795 + 7443402 * 2 ^ 59
def prefixEnd_7443402 : Nat := 4983230072969 + 3 ^ 40 * 7443402 * 2
def baseEnd_7443402 : Nat := 3822042930637591889143423

theorem tailTrace_7443402 : CollatzResearch.WordTrace tailWord_7443402 prefixEnd_7443402 3822042930637591889143423 := by
  unfold tailWord_7443402
  simp only [CollatzResearch.WordTrace]
  refine ⟨67870793544958315174693115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180988782786555507132514973 67870793544958315174693115)
  ·
    refine ⟨101806190317437472762039673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67870793544958315174693115 101806190317437472762039673)
    ·
      refine ⟨76354642738078104571529755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101806190317437472762039673 76354642738078104571529755)
      ·
        refine ⟨114531964107117156857294633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76354642738078104571529755 114531964107117156857294633)
        ·
          refine ⟨85898973080337867642970975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114531964107117156857294633 85898973080337867642970975)
          ·
            refine ⟨128848459620506801464456463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85898973080337867642970975 128848459620506801464456463)
            ·
              refine ⟨193272689430760202196684695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128848459620506801464456463 193272689430760202196684695)
              ·
                refine ⟨289909034146140303295027043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193272689430760202196684695 289909034146140303295027043)
                ·
                  refine ⟨434863551219210454942540565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289909034146140303295027043 434863551219210454942540565)
                  ·
                    refine ⟨20384228963400490075431589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 434863551219210454942540565 20384228963400490075431589)
                    ·
                      refine ⟨3822042930637591889143423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20384228963400490075431589 3822042930637591889143423)
                      ·
                        rfl

theorem cell23_7443402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_7443402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443402 prefixEnd_7443402 := by exact prefixLift 7443402
  have htrace : WordTrace (prefixWord ++ tailWord_7443402) baseStart_7443402 baseEnd_7443402 := by
    simpa [prefixWord, tailWord_7443402, baseEnd_7443402] using wordTrace_append hprefix tailTrace_7443402
  have hstable : (prefixWord ++ tailWord_7443402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443402).length < 2 ^ (prefixWord ++ tailWord_7443402).sum := by decide
  have hdescent : baseEnd_7443402 < baseStart_7443402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443409 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 2, 2, 3]
def baseStart_7443409 : Nat := 118140960795 + 7443409 * 2 ^ 59
def prefixEnd_7443409 : Nat := 4983230072969 + 3 ^ 40 * 7443409 * 2
def baseEnd_7443409 : Nat := 3822046525002173361755891

theorem tailTrace_7443409 : CollatzResearch.WordTrace tailWord_7443409 prefixEnd_7443409 3822046525002173361755891 := by
  unfold tailWord_7443409
  simp only [CollatzResearch.WordTrace]
  refine ⟨271483429490807900894277281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180988952993871933929518187 271483429490807900894277281)
  ·
    refine ⟨203612572118105925670707961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271483429490807900894277281 203612572118105925670707961)
    ·
      refine ⟨152709429088579444253030971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203612572118105925670707961 152709429088579444253030971)
      ·
        refine ⟨229064143632869166379546457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152709429088579444253030971 229064143632869166379546457)
        ·
          refine ⟨171798107724651874784659843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229064143632869166379546457 171798107724651874784659843)
          ·
            refine ⟨257697161586977812176989765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171798107724651874784659843 257697161586977812176989765)
            ·
              refine ⟨48318217797558339783185581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257697161586977812176989765 48318217797558339783185581)
              ·
                refine ⟨18119331674084377418694593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48318217797558339783185581 18119331674084377418694593)
                ·
                  refine ⟨13589498755563283064020945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18119331674084377418694593 13589498755563283064020945)
                  ·
                    refine ⟨10192124066672462298015709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13589498755563283064020945 10192124066672462298015709)
                    ·
                      refine ⟨3822046525002173361755891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10192124066672462298015709 3822046525002173361755891)
                      ·
                        rfl

theorem cell23_7443409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_7443409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443409 prefixEnd_7443409 := by exact prefixLift 7443409
  have htrace : WordTrace (prefixWord ++ tailWord_7443409) baseStart_7443409 baseEnd_7443409 := by
    simpa [prefixWord, tailWord_7443409, baseEnd_7443409] using wordTrace_append hprefix tailTrace_7443409
  have hstable : (prefixWord ++ tailWord_7443409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443409).length < 2 ^ (prefixWord ++ tailWord_7443409).sum := by decide
  have hdescent : baseEnd_7443409 < baseStart_7443409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443432 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_7443432 : Nat := 118140960795 + 7443432 * 2 ^ 59
def prefixEnd_7443432 : Nat := 4983230072969 + 3 ^ 40 * 7443432 * 2
def baseEnd_7443432 : Nat := 3822058335057226771768285

theorem tailTrace_7443432 : CollatzResearch.WordTrace tailWord_7443432 prefixEnd_7443432 3822058335057226771768285 := by
  unfold tailWord_7443432
  simp only [CollatzResearch.WordTrace]
  refine ⟨135742134184862287911182275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180989512246483050548243033 135742134184862287911182275)
  ·
    refine ⟨203613201277293431866773413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135742134184862287911182275 203613201277293431866773413)
    ·
      refine ⟨38177475239492518475020015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203613201277293431866773413 38177475239492518475020015)
      ·
        refine ⟨57266212859238777712530023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38177475239492518475020015 57266212859238777712530023)
        ·
          refine ⟨85899319288858166568795035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57266212859238777712530023 85899319288858166568795035)
          ·
            refine ⟨128848978933287249853192553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85899319288858166568795035 128848978933287249853192553)
            ·
              refine ⟨96636734199965437389894415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128848978933287249853192553 96636734199965437389894415)
              ·
                refine ⟨144955101299948156084841623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96636734199965437389894415 144955101299948156084841623)
                ·
                  refine ⟨217432651949922234127262435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144955101299948156084841623 217432651949922234127262435)
                  ·
                    refine ⟨326148977924883351190893653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217432651949922234127262435 326148977924883351190893653)
                    ·
                      refine ⟨3822058335057226771768285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 326148977924883351190893653 3822058335057226771768285)
                      ·
                        rfl

theorem cell23_7443432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_7443432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443432 prefixEnd_7443432 := by exact prefixLift 7443432
  have htrace : WordTrace (prefixWord ++ tailWord_7443432) baseStart_7443432 baseEnd_7443432 := by
    simpa [prefixWord, tailWord_7443432, baseEnd_7443432] using wordTrace_append hprefix tailTrace_7443432
  have hstable : (prefixWord ++ tailWord_7443432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443432).length < 2 ^ (prefixWord ++ tailWord_7443432).sum := by decide
  have hdescent : baseEnd_7443432 < baseStart_7443432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443446 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_7443446 : Nat := 118140960795 + 7443446 * 2 ^ 59
def prefixEnd_7443446 : Nat := 4983230072969 + 3 ^ 40 * 7443446 * 2
def baseEnd_7443446 : Nat := 424673947087376635221469

theorem tailTrace_7443446 : CollatzResearch.WordTrace tailWord_7443446 prefixEnd_7443446 424673947087376635221469 := by
  unfold tailWord_7443446
  simp only [CollatzResearch.WordTrace]
  refine ⟨16967798686979616013335887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180989852661115904142249461 16967798686979616013335887)
  ·
    refine ⟨25451698030469424020003831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16967798686979616013335887 25451698030469424020003831)
    ·
      refine ⟨38177547045704136030005747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25451698030469424020003831 38177547045704136030005747)
      ·
        refine ⟨57266320568556204045008621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38177547045704136030005747 57266320568556204045008621)
        ·
          refine ⟨21474870213208576516878233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57266320568556204045008621 21474870213208576516878233)
          ·
            refine ⟨16106152659906432387658675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21474870213208576516878233 16106152659906432387658675)
            ·
              refine ⟨24159228989859648581488013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16106152659906432387658675 24159228989859648581488013)
              ·
                refine ⟨9059710871197368218058005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24159228989859648581488013 9059710871197368218058005)
                ·
                  refine ⟨424673947087376635221469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9059710871197368218058005 424673947087376635221469)
                  ·
                    rfl

theorem cell23_7443446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_7443446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443446 prefixEnd_7443446 := by exact prefixLift 7443446
  have htrace : WordTrace (prefixWord ++ tailWord_7443446) baseStart_7443446 baseEnd_7443446 := by
    simpa [prefixWord, tailWord_7443446, baseEnd_7443446] using wordTrace_append hprefix tailTrace_7443446
  have hstable : (prefixWord ++ tailWord_7443446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443446).length < 2 ^ (prefixWord ++ tailWord_7443446).sum := by decide
  have hdescent : baseEnd_7443446 < baseStart_7443446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443490 : List Nat := [3, 3, 1, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_7443490 : Nat := 118140960795 + 7443490 * 2 ^ 59
def prefixEnd_7443490 : Nat := 4983230072969 + 3 ^ 40 * 7443490 * 2
def baseEnd_7443490 : Nat := 3822088116935187544843019

theorem tailTrace_7443490 : CollatzResearch.WordTrace tailWord_7443490 prefixEnd_7443490 3822088116935187544843019 := by
  unfold tailWord_7443490
  simp only [CollatzResearch.WordTrace]
  refine ⟨67871595950878612931993981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180990922535676301151983949 67871595950878612931993981)
  ·
    refine ⟨25451848481579479849497743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67871595950878612931993981 25451848481579479849497743)
    ·
      refine ⟨38177772722369219774246615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25451848481579479849497743 38177772722369219774246615)
      ·
        refine ⟨57266659083553829661369923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38177772722369219774246615 57266659083553829661369923)
        ·
          refine ⟨85899988625330744492054885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57266659083553829661369923 85899988625330744492054885)
          ·
            refine ⟨16106247867249514592260291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85899988625330744492054885 16106247867249514592260291)
            ·
              refine ⟨24159371800874271888390437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16106247867249514592260291 24159371800874271888390437)
              ·
                refine ⟨4529882212663925979073207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24159371800874271888390437 4529882212663925979073207)
                ·
                  refine ⟨6794823318995888968609811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529882212663925979073207 6794823318995888968609811)
                  ·
                    refine ⟨10192234978493833452914717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6794823318995888968609811 10192234978493833452914717)
                    ·
                      refine ⟨3822088116935187544843019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10192234978493833452914717 3822088116935187544843019)
                      ·
                        rfl

theorem cell23_7443490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_7443490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443490 prefixEnd_7443490 := by exact prefixLift 7443490
  have htrace : WordTrace (prefixWord ++ tailWord_7443490) baseStart_7443490 baseEnd_7443490 := by
    simpa [prefixWord, tailWord_7443490, baseEnd_7443490] using wordTrace_append hprefix tailTrace_7443490
  have hstable : (prefixWord ++ tailWord_7443490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443490).length < 2 ^ (prefixWord ++ tailWord_7443490).sum := by decide
  have hdescent : baseEnd_7443490 < baseStart_7443490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443499 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 3]
def baseStart_7443499 : Nat := 118140960795 + 7443499 * 2 ^ 59
def prefixEnd_7443499 : Nat := 4983230072969 + 3 ^ 40 * 7443499 * 2
def baseEnd_7443499 : Nat := 3822092738261078009630477

theorem tailTrace_7443499 : CollatzResearch.WordTrace tailWord_7443499 prefixEnd_7443499 3822092738261078009630477 := by
  unfold tailWord_7443499
  simp only [CollatzResearch.WordTrace]
  refine ⟨271486712060481846265053551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180991141373654564176702367 271486712060481846265053551)
  ·
    refine ⟨407230068090722769397580327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271486712060481846265053551 407230068090722769397580327)
    ·
      refine ⟨610845102136084154096370491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407230068090722769397580327 610845102136084154096370491)
      ·
        refine ⟨916267653204126231144555737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610845102136084154096370491 916267653204126231144555737)
        ·
          refine ⟨687200739903094673358416803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 916267653204126231144555737 687200739903094673358416803)
          ·
            refine ⟨1030801109854642010037625205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687200739903094673358416803 1030801109854642010037625205)
            ·
              refine ⟨96637604048872688441027363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1030801109854642010037625205 96637604048872688441027363)
              ·
                refine ⟨144956406073309032661541045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96637604048872688441027363 144956406073309032661541045)
                ·
                  refine ⟨13589663069372721812019473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144956406073309032661541045 13589663069372721812019473)
                  ·
                    refine ⟨10192247302029541359014605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13589663069372721812019473 10192247302029541359014605)
                    ·
                      refine ⟨3822092738261078009630477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10192247302029541359014605 3822092738261078009630477)
                      ·
                        rfl

theorem cell23_7443499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 3].length) (baseStart_7443499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443499 prefixEnd_7443499 := by exact prefixLift 7443499
  have htrace : WordTrace (prefixWord ++ tailWord_7443499) baseStart_7443499 baseEnd_7443499 := by
    simpa [prefixWord, tailWord_7443499, baseEnd_7443499] using wordTrace_append hprefix tailTrace_7443499
  have hstable : (prefixWord ++ tailWord_7443499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443499).length < 2 ^ (prefixWord ++ tailWord_7443499).sum := by decide
  have hdescent : baseEnd_7443499 < baseStart_7443499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443506 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_7443506 : Nat := 118140960795 + 7443506 * 2 ^ 59
def prefixEnd_7443506 : Nat := 4983230072969 + 3 ^ 40 * 7443506 * 2
def baseEnd_7443506 : Nat := 1274032110875219827414315

theorem tailTrace_7443506 : CollatzResearch.WordTrace tailWord_7443506 prefixEnd_7443506 1274032110875219827414315 := by
  unfold tailWord_7443506
  simp only [CollatzResearch.WordTrace]
  refine ⟨67871741842864121615139593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180991311580970990973705581 67871741842864121615139593)
  ·
    refine ⟨50903806382148091211354695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67871741842864121615139593 50903806382148091211354695)
    ·
      refine ⟨76355709573222136817032043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50903806382148091211354695 76355709573222136817032043)
      ·
        refine ⟨114533564359833205225548065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76355709573222136817032043 114533564359833205225548065)
        ·
          refine ⟨85900173269874903919161049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114533564359833205225548065 85900173269874903919161049)
          ·
            refine ⟨64425129952406177939370787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85900173269874903919161049 64425129952406177939370787)
            ·
              refine ⟨96637694928609266909056181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64425129952406177939370787 96637694928609266909056181)
              ·
                refine ⟨9059783899557118772724017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96637694928609266909056181 9059783899557118772724017)
                ·
                  refine ⟨6794837924667839079543013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9059783899557118772724017 6794837924667839079543013)
                  ·
                    refine ⟨1274032110875219827414315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6794837924667839079543013 1274032110875219827414315)
                    ·
                      rfl

theorem cell23_7443506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_7443506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443506 prefixEnd_7443506 := by exact prefixLift 7443506
  have htrace : WordTrace (prefixWord ++ tailWord_7443506) baseStart_7443506 baseEnd_7443506 := by
    simpa [prefixWord, tailWord_7443506, baseEnd_7443506] using wordTrace_append hprefix tailTrace_7443506
  have hstable : (prefixWord ++ tailWord_7443506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443506).length < 2 ^ (prefixWord ++ tailWord_7443506).sum := by decide
  have hdescent : baseEnd_7443506 < baseStart_7443506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443513 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 5, 2, 2]
def baseStart_7443513 : Nat := 118140960795 + 7443513 * 2 ^ 59
def prefixEnd_7443513 : Nat := 4983230072969 + 3 ^ 40 * 7443513 * 2
def baseEnd_7443513 : Nat := 3822099926990240954855413

theorem tailTrace_7443513 : CollatzResearch.WordTrace tailWord_7443513 prefixEnd_7443513 3822099926990240954855413 := by
  unfold tailWord_7443513
  simp only [CollatzResearch.WordTrace]
  refine ⟨271487222682431126656063193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180991481788287417770708795 271487222682431126656063193)
  ·
    refine ⟨203615417011823344992047395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271487222682431126656063193 203615417011823344992047395)
    ·
      refine ⟨305423125517735017488071093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203615417011823344992047395 305423125517735017488071093)
      ·
        refine ⟨28633418017287657889506665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 305423125517735017488071093 28633418017287657889506665)
        ·
          refine ⟨21475063512965743417129999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28633418017287657889506665 21475063512965743417129999)
          ·
            refine ⟨32212595269448615125694999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21475063512965743417129999 32212595269448615125694999)
            ·
              refine ⟨48318892904172922688542499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32212595269448615125694999 48318892904172922688542499)
              ·
                refine ⟨72478339356259384032813749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48318892904172922688542499 72478339356259384032813749)
                ·
                  refine ⟨6794844314649317253076289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72478339356259384032813749 6794844314649317253076289)
                  ·
                    refine ⟨5096133235986987939807217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6794844314649317253076289 5096133235986987939807217)
                    ·
                      refine ⟨3822099926990240954855413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096133235986987939807217 3822099926990240954855413)
                      ·
                        rfl

theorem cell23_7443513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_7443513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443513 prefixEnd_7443513 := by exact prefixLift 7443513
  have htrace : WordTrace (prefixWord ++ tailWord_7443513) baseStart_7443513 baseEnd_7443513 := by
    simpa [prefixWord, tailWord_7443513, baseEnd_7443513] using wordTrace_append hprefix tailTrace_7443513
  have hstable : (prefixWord ++ tailWord_7443513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443513).length < 2 ^ (prefixWord ++ tailWord_7443513).sum := by decide
  have hdescent : baseEnd_7443513 < baseStart_7443513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443516 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_7443516 : Nat := 118140960795 + 7443516 * 2 ^ 59
def prefixEnd_7443516 : Nat := 4983230072969 + 3 ^ 40 * 7443516 * 2
def baseEnd_7443516 : Nat := 3822101467432204443117899

theorem tailTrace_7443516 : CollatzResearch.WordTrace tailWord_7443516 prefixEnd_7443516 3822101467432204443117899 := by
  unfold tailWord_7443516
  simp only [CollatzResearch.WordTrace]
  refine ⟨135743666050710129084211201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180991554734280172112281601 135743666050710129084211201)
  ·
    refine ⟨101807749538032596813158401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135743666050710129084211201 101807749538032596813158401)
    ·
      refine ⟨76355812153524447609868801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101807749538032596813158401 76355812153524447609868801)
      ·
        refine ⟨57266859115143335707401601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76355812153524447609868801 57266859115143335707401601)
        ·
          refine ⟨42950144336357501780551201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57266859115143335707401601 42950144336357501780551201)
          ·
            refine ⟨32212608252268126335413401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42950144336357501780551201 32212608252268126335413401)
            ·
              refine ⟨24159456189201094751560051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32212608252268126335413401 24159456189201094751560051)
              ·
                refine ⟨36239184283801642127340077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24159456189201094751560051 36239184283801642127340077)
                ·
                  refine ⟨13589694106425615797752529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36239184283801642127340077 13589694106425615797752529)
                  ·
                    refine ⟨10192270579819211848314397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13589694106425615797752529 10192270579819211848314397)
                    ·
                      refine ⟨3822101467432204443117899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10192270579819211848314397 3822101467432204443117899)
                      ·
                        rfl

theorem cell23_7443516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_7443516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443516 prefixEnd_7443516 := by exact prefixLift 7443516
  have htrace : WordTrace (prefixWord ++ tailWord_7443516) baseStart_7443516 baseEnd_7443516 := by
    simpa [prefixWord, tailWord_7443516, baseEnd_7443516] using wordTrace_append hprefix tailTrace_7443516
  have hstable : (prefixWord ++ tailWord_7443516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443516).length < 2 ^ (prefixWord ++ tailWord_7443516).sum := by decide
  have hdescent : baseEnd_7443516 < baseStart_7443516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443529 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 3, 3, 3]
def baseStart_7443529 : Nat := 118140960795 + 7443529 * 2 ^ 59
def prefixEnd_7443529 : Nat := 4983230072969 + 3 ^ 40 * 7443529 * 2
def baseEnd_7443529 : Nat := 3822108142680712892255339

theorem tailTrace_7443529 : CollatzResearch.WordTrace tailWord_7443529 prefixEnd_7443529 3822108142680712892255339 := by
  unfold tailWord_7443529
  simp only [CollatzResearch.WordTrace]
  refine ⟨271487806250373161388645641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180991870833582107592430427 271487806250373161388645641)
  ·
    refine ⟨203615854687779871041484231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271487806250373161388645641 203615854687779871041484231)
    ·
      refine ⟨305423782031669806562226347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203615854687779871041484231 305423782031669806562226347)
      ·
        refine ⟨458135673047504709843339521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305423782031669806562226347 458135673047504709843339521)
        ·
          refine ⟨343601754785628532382504641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458135673047504709843339521 343601754785628532382504641)
          ·
            refine ⟨257701316089221399286878481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343601754785628532382504641 257701316089221399286878481)
            ·
              refine ⟨193275987066916049465158861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257701316089221399286878481 193275987066916049465158861)
              ·
                refine ⟨72478495150093518549434573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193275987066916049465158861 72478495150093518549434573)
                ·
                  refine ⟨27179435681285069456037965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72478495150093518549434573 27179435681285069456037965)
                  ·
                    refine ⟨10192288380481901046014237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27179435681285069456037965 10192288380481901046014237)
                    ·
                      refine ⟨3822108142680712892255339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10192288380481901046014237 3822108142680712892255339)
                      ·
                        rfl

theorem cell23_7443529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3, 3].length) (baseStart_7443529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443529 prefixEnd_7443529 := by exact prefixLift 7443529
  have htrace : WordTrace (prefixWord ++ tailWord_7443529) baseStart_7443529 baseEnd_7443529 := by
    simpa [prefixWord, tailWord_7443529, baseEnd_7443529] using wordTrace_append hprefix tailTrace_7443529
  have hstable : (prefixWord ++ tailWord_7443529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443529).length < 2 ^ (prefixWord ++ tailWord_7443529).sum := by decide
  have hdescent : baseEnd_7443529 < baseStart_7443529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443530 : List Nat := [3, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2]
def baseStart_7443530 : Nat := 118140960795 + 7443530 * 2 ^ 59
def prefixEnd_7443530 : Nat := 4983230072969 + 3 ^ 40 * 7443530 * 2
def baseEnd_7443530 : Nat := 3822108656161367388342835

theorem tailTrace_7443530 : CollatzResearch.WordTrace tailWord_7443530 prefixEnd_7443530 3822108656161367388342835 := by
  unfold tailWord_7443530
  simp only [CollatzResearch.WordTrace]
  refine ⟨67871960680842384639858011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180991895148913025706288029 67871960680842384639858011)
  ·
    refine ⟨101807941021263576959787017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67871960680842384639858011 101807941021263576959787017)
    ·
      refine ⟨76355955765947682719840263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101807941021263576959787017 76355955765947682719840263)
      ·
        refine ⟨114533933648921524079760395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76355955765947682719840263 114533933648921524079760395)
        ·
          refine ⟨171800900473382286119640593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114533933648921524079760395 171800900473382286119640593)
          ·
            refine ⟨128850675355036714589730445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171800900473382286119640593 128850675355036714589730445)
            ·
              refine ⟨48319003258138767971148917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128850675355036714589730445 48319003258138767971148917)
              ·
                refine ⟨4529906555450509497295211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48319003258138767971148917 4529906555450509497295211)
                ·
                  refine ⟨6794859833175764245942817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529906555450509497295211 6794859833175764245942817)
                  ·
                    refine ⟨5096144874881823184457113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6794859833175764245942817 5096144874881823184457113)
                    ·
                      refine ⟨3822108656161367388342835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096144874881823184457113 3822108656161367388342835)
                      ·
                        rfl

theorem cell23_7443530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_7443530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443530 prefixEnd_7443530 := by exact prefixLift 7443530
  have htrace : WordTrace (prefixWord ++ tailWord_7443530) baseStart_7443530 baseEnd_7443530 := by
    simpa [prefixWord, tailWord_7443530, baseEnd_7443530] using wordTrace_append hprefix tailTrace_7443530
  have hstable : (prefixWord ++ tailWord_7443530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443530).length < 2 ^ (prefixWord ++ tailWord_7443530).sum := by decide
  have hdescent : baseEnd_7443530 < baseStart_7443530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443550 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_7443550 : Nat := 118140960795 + 7443550 * 2 ^ 59
def prefixEnd_7443550 : Nat := 4983230072969 + 3 ^ 40 * 7443550 * 2
def baseEnd_7443550 : Nat := 3822118925774457310092743

theorem tailTrace_7443550 : CollatzResearch.WordTrace tailWord_7443550 prefixEnd_7443550 3822118925774457310092743 := by
  unfold tailWord_7443550
  simp only [CollatzResearch.WordTrace]
  refine ⟨33936071522912135246895013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180992381455531387983440069 33936071522912135246895013)
  ·
    refine ⟨6363013410546025358792815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33936071522912135246895013 6363013410546025358792815)
    ·
      refine ⟨9544520115819038038189223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6363013410546025358792815 9544520115819038038189223)
      ·
        refine ⟨14316780173728557057283835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9544520115819038038189223 14316780173728557057283835)
        ·
          refine ⟨21475170260592835585925753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14316780173728557057283835 21475170260592835585925753)
          ·
            refine ⟨16106377695444626689444315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21475170260592835585925753 16106377695444626689444315)
            ·
              refine ⟨24159566543166940034166473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16106377695444626689444315 24159566543166940034166473)
              ·
                refine ⟨18119674907375205025624855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24159566543166940034166473 18119674907375205025624855)
                ·
                  refine ⟨27179512361062807538437283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18119674907375205025624855 27179512361062807538437283)
                  ·
                    refine ⟨40769268541594211307655925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27179512361062807538437283 40769268541594211307655925)
                    ·
                      refine ⟨3822118925774457310092743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40769268541594211307655925 3822118925774457310092743)
                      ·
                        rfl

theorem cell23_7443550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_7443550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443550 prefixEnd_7443550 := by exact prefixLift 7443550
  have htrace : WordTrace (prefixWord ++ tailWord_7443550) baseStart_7443550 baseEnd_7443550 := by
    simpa [prefixWord, tailWord_7443550, baseEnd_7443550] using wordTrace_append hprefix tailTrace_7443550
  have hstable : (prefixWord ++ tailWord_7443550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443550).length < 2 ^ (prefixWord ++ tailWord_7443550).sum := by decide
  have hdescent : baseEnd_7443550 < baseStart_7443550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443560 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7443560 : Nat := 118140960795 + 7443560 * 2 ^ 59
def prefixEnd_7443560 : Nat := 4983230072969 + 3 ^ 40 * 7443560 * 2
def baseEnd_7443560 : Nat := 3822124060581002270967697

theorem tailTrace_7443560 : CollatzResearch.WordTrace tailWord_7443560 prefixEnd_7443560 3822124060581002270967697 := by
  unfold tailWord_7443560
  simp only [CollatzResearch.WordTrace]
  refine ⟨135744468456630426841512067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180992624608840569122016089 135744468456630426841512067)
  ·
    refine ⟨203616702684945640262268101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135744468456630426841512067 203616702684945640262268101)
    ·
      refine ⟨38178131753427307549175269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203616702684945640262268101 38178131753427307549175269)
      ·
        refine ⟨7158399703767620165470363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38178131753427307549175269 7158399703767620165470363)
        ·
          refine ⟨10737599555651430248205545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7158399703767620165470363 10737599555651430248205545)
          ·
            refine ⟨8053199666738572686154159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10737599555651430248205545 8053199666738572686154159)
            ·
              refine ⟨12079799500107859029231239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8053199666738572686154159 12079799500107859029231239)
              ·
                refine ⟨18119699250161788543846859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12079799500107859029231239 18119699250161788543846859)
                ·
                  refine ⟨27179548875242682815770289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18119699250161788543846859 27179548875242682815770289)
                  ·
                    refine ⟨20384661656432012111827717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27179548875242682815770289 20384661656432012111827717)
                    ·
                      refine ⟨3822124060581002270967697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20384661656432012111827717 3822124060581002270967697)
                      ·
                        rfl

theorem cell23_7443560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7443560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443560 prefixEnd_7443560 := by exact prefixLift 7443560
  have htrace : WordTrace (prefixWord ++ tailWord_7443560) baseStart_7443560 baseEnd_7443560 := by
    simpa [prefixWord, tailWord_7443560, baseEnd_7443560] using wordTrace_append hprefix tailTrace_7443560
  have hstable : (prefixWord ++ tailWord_7443560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443560).length < 2 ^ (prefixWord ++ tailWord_7443560).sum := by decide
  have hdescent : baseEnd_7443560 < baseStart_7443560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443603 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 4, 2, 2]
def baseStart_7443603 : Nat := 118140960795 + 7443603 * 2 ^ 59
def prefixEnd_7443603 : Nat := 4983230072969 + 3 ^ 40 * 7443603 * 2
def baseEnd_7443603 : Nat := 3822146140249145602729999

theorem tailTrace_7443603 : CollatzResearch.WordTrace tailWord_7443603 prefixEnd_7443603 3822146140249145602729999 := by
  unfold tailWord_7443603
  simp only [CollatzResearch.WordTrace]
  refine ⟨271490505252105072026839463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180993670168070048017892975 271490505252105072026839463)
  ·
    refine ⟨407235757878157608040259195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271490505252105072026839463 407235757878157608040259195)
    ·
      refine ⟨610853636817236412060388793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407235757878157608040259195 610853636817236412060388793)
      ·
        refine ⟨458140227612927309045291595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610853636817236412060388793 458140227612927309045291595)
        ·
          refine ⟨687210341419390963567937393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458140227612927309045291595 687210341419390963567937393)
          ·
            refine ⟨515407756064543222675953045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687210341419390963567937393 515407756064543222675953045)
            ·
              refine ⟨24159738565525463562935299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 515407756064543222675953045 24159738565525463562935299)
              ·
                refine ⟨36239607848288195344402949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24159738565525463562935299 36239607848288195344402949)
                ·
                  refine ⟨6794926471554036627075553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36239607848288195344402949 6794926471554036627075553)
                  ·
                    refine ⟨5096194853665527470306665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6794926471554036627075553 5096194853665527470306665)
                    ·
                      refine ⟨3822146140249145602729999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096194853665527470306665 3822146140249145602729999)
                      ·
                        rfl

theorem cell23_7443603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 2, 2].length) (baseStart_7443603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443603 prefixEnd_7443603 := by exact prefixLift 7443603
  have htrace : WordTrace (prefixWord ++ tailWord_7443603) baseStart_7443603 baseEnd_7443603 := by
    simpa [prefixWord, tailWord_7443603, baseEnd_7443603] using wordTrace_append hprefix tailTrace_7443603
  have hstable : (prefixWord ++ tailWord_7443603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443603).length < 2 ^ (prefixWord ++ tailWord_7443603).sum := by decide
  have hdescent : baseEnd_7443603 < baseStart_7443603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443614 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_7443614 : Nat := 118140960795 + 7443614 * 2 ^ 59
def prefixEnd_7443614 : Nat := 4983230072969 + 3 ^ 40 * 7443614 * 2
def baseEnd_7443614 : Nat := 3822151788536345059692449

theorem tailTrace_7443614 : CollatzResearch.WordTrace tailWord_7443614 prefixEnd_7443614 3822151788536345059692449 := by
  unfold tailWord_7443614
  simp only [CollatzResearch.WordTrace]
  refine ⟨33936363306883152613186237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180993937636710147270326597 33936363306883152613186237)
  ·
    refine ⟨12726136240081182229944839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33936363306883152613186237 12726136240081182229944839)
    ·
      refine ⟨19089204360121773344917259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12726136240081182229944839 19089204360121773344917259)
      ·
        refine ⟨28633806540182660017375889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19089204360121773344917259 28633806540182660017375889)
        ·
          refine ⟨21475354905136995013031917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28633806540182660017375889 21475354905136995013031917)
          ·
            refine ⟨8053258089426373129886969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21475354905136995013031917 8053258089426373129886969)
            ·
              refine ⟨6039943567069779847415227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8053258089426373129886969 6039943567069779847415227)
              ·
                refine ⟨9059915350604669771122841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6039943567069779847415227 9059915350604669771122841)
                ·
                  refine ⟨6794936512953502328342131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9059915350604669771122841 6794936512953502328342131)
                  ·
                    refine ⟨10192404769430253492513197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6794936512953502328342131 10192404769430253492513197)
                    ·
                      refine ⟨3822151788536345059692449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10192404769430253492513197 3822151788536345059692449)
                      ·
                        rfl

theorem cell23_7443614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_7443614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443614 prefixEnd_7443614 := by exact prefixLift 7443614
  have htrace : WordTrace (prefixWord ++ tailWord_7443614) baseStart_7443614 baseEnd_7443614 := by
    simpa [prefixWord, tailWord_7443614, baseEnd_7443614] using wordTrace_append hprefix tailTrace_7443614
  have hstable : (prefixWord ++ tailWord_7443614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443614).length < 2 ^ (prefixWord ++ tailWord_7443614).sum := by decide
  have hdescent : baseEnd_7443614 < baseStart_7443614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443656 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 2, 5]
def baseStart_7443656 : Nat := 118140960795 + 7443656 * 2 ^ 59
def prefixEnd_7443656 : Nat := 4983230072969 + 3 ^ 40 * 7443656 * 2
def baseEnd_7443656 : Nat := 1274057784907944631789085

theorem tailTrace_7443656 : CollatzResearch.WordTrace tailWord_7443656 prefixEnd_7443656 1274057784907944631789085 := by
  unfold tailWord_7443656
  simp only [CollatzResearch.WordTrace]
  refine ⟨135746219160456531039259411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180994958880608708052345881 135746219160456531039259411)
  ·
    refine ⟨203619328740684796558889117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135746219160456531039259411 203619328740684796558889117)
    ·
      refine ⟨76357248277756798709583419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203619328740684796558889117 76357248277756798709583419)
      ·
        refine ⟨114535872416635198064375129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76357248277756798709583419 114535872416635198064375129)
        ·
          refine ⟨85901904312476398548281347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114535872416635198064375129 85901904312476398548281347)
          ·
            refine ⟨128852856468714597822422021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85901904312476398548281347 128852856468714597822422021)
            ·
              refine ⟨24159910587883987091704129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128852856468714597822422021 24159910587883987091704129)
              ·
                refine ⟨18119932940912990318778097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24159910587883987091704129 18119932940912990318778097)
                ·
                  refine ⟨13589949705684742739083573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18119932940912990318778097 13589949705684742739083573)
                  ·
                    refine ⟨1274057784907944631789085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13589949705684742739083573 1274057784907944631789085)
                    ·
                      rfl

theorem cell23_7443656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_7443656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443656 prefixEnd_7443656 := by exact prefixLift 7443656
  have htrace : WordTrace (prefixWord ++ tailWord_7443656) baseStart_7443656 baseEnd_7443656 := by
    simpa [prefixWord, tailWord_7443656, baseEnd_7443656] using wordTrace_append hprefix tailTrace_7443656
  have hstable : (prefixWord ++ tailWord_7443656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443656).length < 2 ^ (prefixWord ++ tailWord_7443656).sum := by decide
  have hdescent : baseEnd_7443656 < baseStart_7443656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443666 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_7443666 : Nat := 118140960795 + 7443666 * 2 ^ 59
def prefixEnd_7443666 : Nat := 4983230072969 + 3 ^ 40 * 7443666 * 2
def baseEnd_7443666 : Nat := 3822178489530378856242209

theorem tailTrace_7443666 : CollatzResearch.WordTrace tailWord_7443666 prefixEnd_7443666 3822178489530378856242209 := by
  unfold tailWord_7443666
  simp only [CollatzResearch.WordTrace]
  refine ⟨67873200762719208446595713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180995202033917889190921901 67873200762719208446595713)
  ·
    refine ⟨50904900572039406334946785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67873200762719208446595713 50904900572039406334946785)
    ·
      refine ⟨38178675429029554751210089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50904900572039406334946785 38178675429029554751210089)
      ·
        refine ⟨28634006571772166063407567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38178675429029554751210089 28634006571772166063407567)
        ·
          refine ⟨42951009857658249095111351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28634006571772166063407567 42951009857658249095111351)
          ·
            refine ⟨64426514786487373642667027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42951009857658249095111351 64426514786487373642667027)
            ·
              refine ⟨96639772179731060464000541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64426514786487373642667027 96639772179731060464000541)
              ·
                refine ⟨36239914567399147674000203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96639772179731060464000541 36239914567399147674000203)
                ·
                  refine ⟨54359871851098721511000305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36239914567399147674000203 54359871851098721511000305)
                  ·
                    refine ⟨40769903888324041133250229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54359871851098721511000305 40769903888324041133250229)
                    ·
                      refine ⟨3822178489530378856242209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40769903888324041133250229 3822178489530378856242209)
                      ·
                        rfl

theorem cell23_7443666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_7443666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443666 prefixEnd_7443666 := by exact prefixLift 7443666
  have htrace : WordTrace (prefixWord ++ tailWord_7443666) baseStart_7443666 baseEnd_7443666 := by
    simpa [prefixWord, tailWord_7443666, baseEnd_7443666] using wordTrace_append hprefix tailTrace_7443666
  have hstable : (prefixWord ++ tailWord_7443666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443666).length < 2 ^ (prefixWord ++ tailWord_7443666).sum := by decide
  have hdescent : baseEnd_7443666 < baseStart_7443666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443689 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_7443689 : Nat := 118140960795 + 7443689 * 2 ^ 59
def prefixEnd_7443689 : Nat := 4983230072969 + 3 ^ 40 * 7443689 * 2
def baseEnd_7443689 : Nat := 3822190299585432266254603

theorem tailTrace_7443689 : CollatzResearch.WordTrace tailWord_7443689 prefixEnd_7443689 3822190299585432266254603 := by
  unfold tailWord_7443689
  simp only [CollatzResearch.WordTrace]
  refine ⟨271493641929793508714470121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180995761286529005809646747 271493641929793508714470121)
  ·
    refine ⟨203620231447345131535852591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271493641929793508714470121 203620231447345131535852591)
    ·
      refine ⟨305430347171017697303778887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203620231447345131535852591 305430347171017697303778887)
      ·
        refine ⟨458145520756526545955668331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305430347171017697303778887 458145520756526545955668331)
        ·
          refine ⟨687218281134789818933502497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458145520756526545955668331 687218281134789818933502497)
          ·
            refine ⟨515413710851092364200126873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687218281134789818933502497 515413710851092364200126873)
            ·
              refine ⟨386560283138319273150095155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515413710851092364200126873 386560283138319273150095155)
              ·
                refine ⟨579840424707478909725142733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386560283138319273150095155 579840424707478909725142733)
                ·
                  refine ⟨217440159265304591146928525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579840424707478909725142733 217440159265304591146928525)
                  ·
                    refine ⟨81540059724489221680098197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217440159265304591146928525 81540059724489221680098197)
                    ·
                      refine ⟨3822190299585432266254603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81540059724489221680098197 3822190299585432266254603)
                      ·
                        rfl

theorem cell23_7443689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_7443689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443689 prefixEnd_7443689 := by exact prefixLift 7443689
  have htrace : WordTrace (prefixWord ++ tailWord_7443689) baseStart_7443689 baseEnd_7443689 := by
    simpa [prefixWord, tailWord_7443689, baseEnd_7443689] using wordTrace_append hprefix tailTrace_7443689
  have hstable : (prefixWord ++ tailWord_7443689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443689).length < 2 ^ (prefixWord ++ tailWord_7443689).sum := by decide
  have hdescent : baseEnd_7443689 < baseStart_7443689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443693 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_7443693 : Nat := 118140960795 + 7443693 * 2 ^ 59
def prefixEnd_7443693 : Nat := 4983230072969 + 3 ^ 40 * 7443693 * 2
def baseEnd_7443693 : Nat := 3822192353508050250604585

theorem tailTrace_7443693 : CollatzResearch.WordTrace tailWord_7443693 prefixEnd_7443693 3822192353508050250604585 := by
  unfold tailWord_7443693
  simp only [CollatzResearch.WordTrace]
  refine ⟨271493787821779017397615733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180995858547852678265077155 271493787821779017397615733)
  ·
    refine ⟨25452542608291782881026475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271493787821779017397615733 25452542608291782881026475)
    ·
      refine ⟨38178813912437674321539713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25452542608291782881026475 38178813912437674321539713)
      ·
        refine ⟨28634110434328255741154785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38178813912437674321539713 28634110434328255741154785)
        ·
          refine ⟨21475582825746191805866089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28634110434328255741154785 21475582825746191805866089)
          ·
            refine ⟨16106687119309643854399567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21475582825746191805866089 16106687119309643854399567)
            ·
              refine ⟨24160030678964465781599351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16106687119309643854399567 24160030678964465781599351)
              ·
                refine ⟨36240046018446698672399027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24160030678964465781599351 36240046018446698672399027)
                ·
                  refine ⟨54360069027670048008598541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36240046018446698672399027 54360069027670048008598541)
                  ·
                    refine ⟨20385025885376268003224453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54360069027670048008598541 20385025885376268003224453)
                    ·
                      refine ⟨3822192353508050250604585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20385025885376268003224453 3822192353508050250604585)
                      ·
                        rfl

theorem cell23_7443693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_7443693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443693 prefixEnd_7443693 := by exact prefixLift 7443693
  have htrace : WordTrace (prefixWord ++ tailWord_7443693) baseStart_7443693 baseEnd_7443693 := by
    simpa [prefixWord, tailWord_7443693, baseEnd_7443693] using wordTrace_append hprefix tailTrace_7443693
  have hstable : (prefixWord ++ tailWord_7443693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443693).length < 2 ^ (prefixWord ++ tailWord_7443693).sum := by decide
  have hdescent : baseEnd_7443693 < baseStart_7443693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443710 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_7443710 : Nat := 118140960795 + 7443710 * 2 ^ 59
def prefixEnd_7443710 : Nat := 4983230072969 + 3 ^ 40 * 7443710 * 2
def baseEnd_7443710 : Nat := 3822201082679176684092007

theorem tailTrace_7443710 : CollatzResearch.WordTrace tailWord_7443710 prefixEnd_7443710 3822201082679176684092007 := by
  unfold tailWord_7443710
  simp only [CollatzResearch.WordTrace]
  refine ⟨33936800982839678662623073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180996271908478286200656389 33936800982839678662623073)
  ·
    refine ⟨25452600737129758996967305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33936800982839678662623073 25452600737129758996967305)
    ·
      refine ⟨19089450552847319247725479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25452600737129758996967305 19089450552847319247725479)
      ·
        refine ⟨28634175829270978871588219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19089450552847319247725479 28634175829270978871588219)
        ·
          refine ⟨42951263743906468307382329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28634175829270978871588219 42951263743906468307382329)
          ·
            refine ⟨32213447807929851230536747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42951263743906468307382329 32213447807929851230536747)
            ·
              refine ⟨48320171711894776845805121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32213447807929851230536747 48320171711894776845805121)
              ·
                refine ⟨36240128783921082634353841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48320171711894776845805121 36240128783921082634353841)
                ·
                  refine ⟨27180096587940811975765381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36240128783921082634353841 27180096587940811975765381)
                  ·
                    refine ⟨5096268110238902245456009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27180096587940811975765381 5096268110238902245456009)
                    ·
                      refine ⟨3822201082679176684092007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096268110238902245456009 3822201082679176684092007)
                      ·
                        rfl

theorem cell23_7443710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_7443710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443710 prefixEnd_7443710 := by exact prefixLift 7443710
  have htrace : WordTrace (prefixWord ++ tailWord_7443710) baseStart_7443710 baseEnd_7443710 := by
    simpa [prefixWord, tailWord_7443710, baseEnd_7443710] using wordTrace_append hprefix tailTrace_7443710
  have hstable : (prefixWord ++ tailWord_7443710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443710).length < 2 ^ (prefixWord ++ tailWord_7443710).sum := by decide
  have hdescent : baseEnd_7443710 < baseStart_7443710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443720 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 3, 4]
def baseStart_7443720 : Nat := 118140960795 + 7443720 * 2 ^ 59
def prefixEnd_7443720 : Nat := 4983230072969 + 3 ^ 40 * 7443720 * 2
def baseEnd_7443720 : Nat := 1274068739161907214988987

theorem tailTrace_7443720 : CollatzResearch.WordTrace tailWord_7443720 prefixEnd_7443720 1274068739161907214988987 := by
  unfold tailWord_7443720
  simp only [CollatzResearch.WordTrace]
  refine ⟨135747386296340600504424307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180996515061787467339232409 135747386296340600504424307)
  ·
    refine ⟨203621079444510900756636461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135747386296340600504424307 203621079444510900756636461)
    ·
      refine ⟨76357904791691587783738673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203621079444510900756636461 76357904791691587783738673)
      ·
        refine ⟨57268428593768690837804005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76357904791691587783738673 57268428593768690837804005)
        ·
          refine ⟨10737830361331629532088251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57268428593768690837804005 10737830361331629532088251)
          ·
            refine ⟨16106745541997444298132377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10737830361331629532088251 16106745541997444298132377)
            ·
              refine ⟨12080059156498083223599283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16106745541997444298132377 12080059156498083223599283)
              ·
                refine ⟨18120088734747124835398925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12080059156498083223599283 18120088734747124835398925)
                ·
                  refine ⟨6795033275530171813274597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18120088734747124835398925 6795033275530171813274597)
                  ·
                    refine ⟨1274068739161907214988987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6795033275530171813274597 1274068739161907214988987)
                    ·
                      rfl

theorem cell23_7443720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_7443720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443720 prefixEnd_7443720 := by exact prefixLift 7443720
  have htrace : WordTrace (prefixWord ++ tailWord_7443720) baseStart_7443720 baseEnd_7443720 := by
    simpa [prefixWord, tailWord_7443720, baseEnd_7443720] using wordTrace_append hprefix tailTrace_7443720
  have hstable : (prefixWord ++ tailWord_7443720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443720).length < 2 ^ (prefixWord ++ tailWord_7443720).sum := by decide
  have hdescent : baseEnd_7443720 < baseStart_7443720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443754 : List Nat := [3, 1, 4, 2, 1, 3, 1, 3, 1, 4]
def baseStart_7443754 : Nat := 118140960795 + 7443754 * 2 ^ 59
def prefixEnd_7443754 : Nat := 4983230072969 + 3 ^ 40 * 7443754 * 2
def baseEnd_7443754 : Nat := 1274074558609324837313935

theorem tailTrace_7443754 : CollatzResearch.WordTrace tailWord_7443754 prefixEnd_7443754 1274074558609324837313935 := by
  unfold tailWord_7443754
  simp only [CollatzResearch.WordTrace]
  refine ⟨67874003168639506203896579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180997341783038683210390877 67874003168639506203896579)
  ·
    refine ⟨101811004752959259305844869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67874003168639506203896579 101811004752959259305844869)
    ·
      refine ⟨19089563391179861119845913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101811004752959259305844869 19089563391179861119845913)
      ·
        refine ⟨14317172543384895839884435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19089563391179861119845913 14317172543384895839884435)
        ·
          refine ⟨21475758815077343759826653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14317172543384895839884435 21475758815077343759826653)
          ·
            refine ⟨8053409555654003909934995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21475758815077343759826653 8053409555654003909934995)
            ·
              refine ⟨12080114333481005864902493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8053409555654003909934995 12080114333481005864902493)
              ·
                refine ⟨4530042875055377199338435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12080114333481005864902493 4530042875055377199338435)
                ·
                  refine ⟨6795064312583065799007653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530042875055377199338435 6795064312583065799007653)
                  ·
                    refine ⟨1274074558609324837313935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6795064312583065799007653 1274074558609324837313935)
                    ·
                      rfl

theorem cell23_7443754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_7443754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443754 prefixEnd_7443754 := by exact prefixLift 7443754
  have htrace : WordTrace (prefixWord ++ tailWord_7443754) baseStart_7443754 baseEnd_7443754 := by
    simpa [prefixWord, tailWord_7443754, baseEnd_7443754] using wordTrace_append hprefix tailTrace_7443754
  have hstable : (prefixWord ++ tailWord_7443754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443754).length < 2 ^ (prefixWord ++ tailWord_7443754).sum := by decide
  have hdescent : baseEnd_7443754 < baseStart_7443754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443763 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 1, 5]
def baseStart_7443763 : Nat := 118140960795 + 7443763 * 2 ^ 59
def prefixEnd_7443763 : Nat := 4983230072969 + 3 ^ 40 * 7443763 * 2
def baseEnd_7443763 : Nat := 1274076099051288325576421

theorem tailTrace_7443763 : CollatzResearch.WordTrace tailWord_7443763 prefixEnd_7443763 1274076099051288325576421 := by
  unfold tailWord_7443763
  simp only [CollatzResearch.WordTrace]
  refine ⟨271496340931525419352663943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180997560621016946235109295 271496340931525419352663943)
  ·
    refine ⟨407244511397288129028995915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271496340931525419352663943 407244511397288129028995915)
    ·
      refine ⟨610866767095932193543493873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407244511397288129028995915 610866767095932193543493873)
      ·
        refine ⟨458150075321949145157620405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610866767095932193543493873 458150075321949145157620405)
        ·
          refine ⟨42951569561432732358526913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 458150075321949145157620405 42951569561432732358526913)
          ·
            refine ⟨32213677171074549268895185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42951569561432732358526913 32213677171074549268895185)
            ·
              refine ⟨24160257878305911951671389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32213677171074549268895185 24160257878305911951671389)
              ·
                refine ⟨9060096704364716981876771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24160257878305911951671389 9060096704364716981876771)
                ·
                  refine ⟨13590145056547075472815157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9060096704364716981876771 13590145056547075472815157)
                  ·
                    refine ⟨1274076099051288325576421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13590145056547075472815157 1274076099051288325576421)
                    ·
                      rfl

theorem cell23_7443763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 5].length) (baseStart_7443763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443763 prefixEnd_7443763 := by exact prefixLift 7443763
  have htrace : WordTrace (prefixWord ++ tailWord_7443763) baseStart_7443763 baseEnd_7443763 := by
    simpa [prefixWord, tailWord_7443763, baseEnd_7443763] using wordTrace_append hprefix tailTrace_7443763
  have hstable : (prefixWord ++ tailWord_7443763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443763).length < 2 ^ (prefixWord ++ tailWord_7443763).sum := by decide
  have hdescent : baseEnd_7443763 < baseStart_7443763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443770 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2]
def baseStart_7443770 : Nat := 118140960795 + 7443770 * 2 ^ 59
def prefixEnd_7443770 : Nat := 4983230072969 + 3 ^ 40 * 7443770 * 2
def baseEnd_7443770 : Nat := 3822231891518446449341731

theorem tailTrace_7443770 : CollatzResearch.WordTrace tailWord_7443770 prefixEnd_7443770 3822231891518446449341731 := by
  unfold tailWord_7443770
  simp only [CollatzResearch.WordTrace]
  refine ⟨67874149060625014887042191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180997730828333373032112509 67874149060625014887042191)
  ·
    refine ⟨101811223590937522330563287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67874149060625014887042191 101811223590937522330563287)
    ·
      refine ⟨152716835386406283495844931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101811223590937522330563287 152716835386406283495844931)
      ·
        refine ⟨229075253079609425243767397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152716835386406283495844931 229075253079609425243767397)
        ·
          refine ⟨42951609952426767233206387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229075253079609425243767397 42951609952426767233206387)
          ·
            refine ⟨64427414928640150849809581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42951609952426767233206387 64427414928640150849809581)
            ·
              refine ⟨24160280598240056568678593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64427414928640150849809581 24160280598240056568678593)
              ·
                refine ⟨18120210448680042426508945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24160280598240056568678593 18120210448680042426508945)
                ·
                  refine ⟨13590157836510031819881709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18120210448680042426508945 13590157836510031819881709)
                  ·
                    refine ⟨5096309188691261932455641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13590157836510031819881709 5096309188691261932455641)
                    ·
                      refine ⟨3822231891518446449341731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096309188691261932455641 3822231891518446449341731)
                      ·
                        rfl

theorem cell23_7443770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2].length) (baseStart_7443770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443770 prefixEnd_7443770 := by exact prefixLift 7443770
  have htrace : WordTrace (prefixWord ++ tailWord_7443770) baseStart_7443770 baseEnd_7443770 := by
    simpa [prefixWord, tailWord_7443770, baseEnd_7443770] using wordTrace_append hprefix tailTrace_7443770
  have hstable : (prefixWord ++ tailWord_7443770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443770).length < 2 ^ (prefixWord ++ tailWord_7443770).sum := by decide
  have hdescent : baseEnd_7443770 < baseStart_7443770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443777 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_7443777 : Nat := 118140960795 + 7443777 * 2 ^ 59
def prefixEnd_7443777 : Nat := 4983230072969 + 3 ^ 40 * 7443777 * 2
def baseEnd_7443777 : Nat := 3822235485883027921954199

theorem tailTrace_7443777 : CollatzResearch.WordTrace tailWord_7443777 prefixEnd_7443777 3822235485883027921954199 := by
  unfold tailWord_7443777
  simp only [CollatzResearch.WordTrace]
  refine ⟨271496851553474699743673585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180997901035649799829115723 271496851553474699743673585)
  ·
    refine ⟨203622638665106024807755189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271496851553474699743673585 203622638665106024807755189)
    ·
      refine ⟨19089622374853689825727049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203622638665106024807755189 19089622374853689825727049)
      ·
        refine ⟨14317216781140267369295287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19089622374853689825727049 14317216781140267369295287)
        ·
          refine ⟨21475825171710401053942931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14317216781140267369295287 21475825171710401053942931)
          ·
            refine ⟨32213737757565601580914397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21475825171710401053942931 32213737757565601580914397)
            ·
              refine ⟨12080151659087100592842899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32213737757565601580914397 12080151659087100592842899)
              ·
                refine ⟨18120227488630650889264349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12080151659087100592842899 18120227488630650889264349)
                ·
                  refine ⟨6795085308236494083474131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18120227488630650889264349 6795085308236494083474131)
                  ·
                    refine ⟨10192627962354741125211197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6795085308236494083474131 10192627962354741125211197)
                    ·
                      refine ⟨3822235485883027921954199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10192627962354741125211197 3822235485883027921954199)
                      ·
                        rfl

theorem cell23_7443777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_7443777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443777 prefixEnd_7443777 := by exact prefixLift 7443777
  have htrace : WordTrace (prefixWord ++ tailWord_7443777) baseStart_7443777 baseEnd_7443777 := by
    simpa [prefixWord, tailWord_7443777, baseEnd_7443777] using wordTrace_append hprefix tailTrace_7443777
  have hstable : (prefixWord ++ tailWord_7443777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443777).length < 2 ^ (prefixWord ++ tailWord_7443777).sum := by decide
  have hdescent : baseEnd_7443777 < baseStart_7443777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443800 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 5, 2, 2]
def baseStart_7443800 : Nat := 118140960795 + 7443800 * 2 ^ 59
def prefixEnd_7443800 : Nat := 4983230072969 + 3 ^ 40 * 7443800 * 2
def baseEnd_7443800 : Nat := 3822247295938081331966593

theorem tailTrace_7443800 : CollatzResearch.WordTrace tailWord_7443800 prefixEnd_7443800 3822247295938081331966593 := by
  unfold tailWord_7443800
  simp only [CollatzResearch.WordTrace]
  refine ⟨135748845216195687335880427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180998460288260916447840569 135748845216195687335880427)
  ·
    refine ⟨203623267824293531003820641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135748845216195687335880427 203623267824293531003820641)
    ·
      refine ⟨152717450868220148252865481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203623267824293531003820641 152717450868220148252865481)
      ·
        refine ⟨114538088151165111189649111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152717450868220148252865481 114538088151165111189649111)
        ·
          refine ⟨171807132226747666784473667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114538088151165111189649111 171807132226747666784473667)
          ·
            refine ⟨257710698340121500176710501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171807132226747666784473667 257710698340121500176710501)
            ·
              refine ⟨48320755938772781283133219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257710698340121500176710501 48320755938772781283133219)
              ·
                refine ⟨72481133908159171924699829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48320755938772781283133219 72481133908159171924699829)
                ·
                  refine ⟨6795106303889922367940609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72481133908159171924699829 6795106303889922367940609)
                  ·
                    refine ⟨5096329727917441775955457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795106303889922367940609 5096329727917441775955457)
                    ·
                      refine ⟨3822247295938081331966593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096329727917441775955457 3822247295938081331966593)
                      ·
                        rfl

theorem cell23_7443800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_7443800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443800 prefixEnd_7443800 := by exact prefixLift 7443800
  have htrace : WordTrace (prefixWord ++ tailWord_7443800) baseStart_7443800 baseEnd_7443800 := by
    simpa [prefixWord, tailWord_7443800, baseEnd_7443800] using wordTrace_append hprefix tailTrace_7443800
  have hstable : (prefixWord ++ tailWord_7443800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443800).length < 2 ^ (prefixWord ++ tailWord_7443800).sum := by decide
  have hdescent : baseEnd_7443800 < baseStart_7443800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443813 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_7443813 : Nat := 118140960795 + 7443813 * 2 ^ 59
def prefixEnd_7443813 : Nat := 4983230072969 + 3 ^ 40 * 7443813 * 2
def baseEnd_7443813 : Nat := 3822253971186589781104033

theorem tailTrace_7443813 : CollatzResearch.WordTrace tailWord_7443813 prefixEnd_7443813 3822253971186589781104033 := by
  unfold tailWord_7443813
  simp only [CollatzResearch.WordTrace]
  refine ⟨271498164581344277891984093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180998776387562851927989395 271498164581344277891984093)
  ·
    refine ⟨101811811718004104209494035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271498164581344277891984093 101811811718004104209494035)
    ·
      refine ⟨152717717577006156314241053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101811811718004104209494035 152717717577006156314241053)
      ·
        refine ⟨57269144091377308617840395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152717717577006156314241053 57269144091377308617840395)
        ·
          refine ⟨85903716137065962926760593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57269144091377308617840395 85903716137065962926760593)
          ·
            refine ⟨64427787102799472195070445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85903716137065962926760593 64427787102799472195070445)
            ·
              refine ⟨24160420163549802073151417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64427787102799472195070445 24160420163549802073151417)
              ·
                refine ⟨18120315122662351554863563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24160420163549802073151417 18120315122662351554863563)
                ·
                  refine ⟨27180472683993527332295345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18120315122662351554863563 27180472683993527332295345)
                  ·
                    refine ⟨20385354512995145499221509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27180472683993527332295345 20385354512995145499221509)
                    ·
                      refine ⟨3822253971186589781104033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20385354512995145499221509 3822253971186589781104033)
                      ·
                        rfl

theorem cell23_7443813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_7443813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443813 prefixEnd_7443813 := by exact prefixLift 7443813
  have htrace : WordTrace (prefixWord ++ tailWord_7443813) baseStart_7443813 baseEnd_7443813 := by
    simpa [prefixWord, tailWord_7443813, baseEnd_7443813] using wordTrace_append hprefix tailTrace_7443813
  have hstable : (prefixWord ++ tailWord_7443813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443813).length < 2 ^ (prefixWord ++ tailWord_7443813).sum := by decide
  have hdescent : baseEnd_7443813 < baseStart_7443813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443820 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 5]
def baseStart_7443820 : Nat := 118140960795 + 7443820 * 2 ^ 59
def prefixEnd_7443820 : Nat := 4983230072969 + 3 ^ 40 * 7443820 * 2
def baseEnd_7443820 : Nat := 3822257565551171253716501

theorem tailTrace_7443820 : CollatzResearch.WordTrace tailWord_7443820 prefixEnd_7443820 3822257565551171253716501 := by
  unfold tailWord_7443820
  simp only [CollatzResearch.WordTrace]
  refine ⟨135749209946159459043744457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180998946594879278724992609 135749209946159459043744457)
  ·
    refine ⟨101811907459619594282808343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135749209946159459043744457 101811907459619594282808343)
    ·
      refine ⟨152717861189429391424212515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101811907459619594282808343 152717861189429391424212515)
      ·
        refine ⟨229076791784144087136318773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152717861189429391424212515 229076791784144087136318773)
        ·
          refine ⟨21475949229763508169029885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229076791784144087136318773 21475949229763508169029885)
          ·
            refine ⟨8053480961161315563386207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21475949229763508169029885 8053480961161315563386207)
            ·
              refine ⟨12080221441741973345079311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8053480961161315563386207 12080221441741973345079311)
              ·
                refine ⟨18120332162612960017618967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12080221441741973345079311 18120332162612960017618967)
                ·
                  refine ⟨27180498243919440026428451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18120332162612960017618967 27180498243919440026428451)
                  ·
                    refine ⟨40770747365879160039642677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27180498243919440026428451 40770747365879160039642677)
                    ·
                      refine ⟨3822257565551171253716501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40770747365879160039642677 3822257565551171253716501)
                      ·
                        rfl

theorem cell23_7443820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_7443820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443820 prefixEnd_7443820 := by exact prefixLift 7443820
  have htrace : WordTrace (prefixWord ++ tailWord_7443820) baseStart_7443820 baseEnd_7443820 := by
    simpa [prefixWord, tailWord_7443820, baseEnd_7443820] using wordTrace_append hprefix tailTrace_7443820
  have hstable : (prefixWord ++ tailWord_7443820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443820).length < 2 ^ (prefixWord ++ tailWord_7443820).sum := by decide
  have hdescent : baseEnd_7443820 < baseStart_7443820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443836 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_7443836 : Nat := 118140960795 + 7443836 * 2 ^ 59
def prefixEnd_7443836 : Nat := 4983230072969 + 3 ^ 40 * 7443836 * 2
def baseEnd_7443836 : Nat := 1274088593747214397038809

theorem tailTrace_7443836 : CollatzResearch.WordTrace tailWord_7443836 prefixEnd_7443836 1274088593747214397038809 := by
  unfold tailWord_7443836
  simp only [CollatzResearch.WordTrace]
  refine ⟨135749501730130476410035681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180999335640173968546714241 135749501730130476410035681)
  ·
    refine ⟨101812126297597857307526761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135749501730130476410035681 101812126297597857307526761)
    ·
      refine ⟨76359094723198392980645071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101812126297597857307526761 76359094723198392980645071)
      ·
        refine ⟨114538642084797589470967607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76359094723198392980645071 114538642084797589470967607)
        ·
          refine ⟨171807963127196384206451411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114538642084797589470967607 171807963127196384206451411)
          ·
            refine ⟨257711944690794576309677117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171807963127196384206451411 257711944690794576309677117)
            ·
              refine ⟨96641979259047966116128919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257711944690794576309677117 96641979259047966116128919)
              ·
                refine ⟨144962968888571949174193379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96641979259047966116128919 144962968888571949174193379)
                ·
                  refine ⟨217444453332857923761290069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144962968888571949174193379 217444453332857923761290069)
                  ·
                    refine ⟨1274088593747214397038809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 217444453332857923761290069 1274088593747214397038809)
                    ·
                      rfl

theorem cell23_7443836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_7443836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443836 prefixEnd_7443836 := by exact prefixLift 7443836
  have htrace : WordTrace (prefixWord ++ tailWord_7443836) baseStart_7443836 baseEnd_7443836 := by
    simpa [prefixWord, tailWord_7443836, baseEnd_7443836] using wordTrace_append hprefix tailTrace_7443836
  have hstable : (prefixWord ++ tailWord_7443836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443836).length < 2 ^ (prefixWord ++ tailWord_7443836).sum := by decide
  have hdescent : baseEnd_7443836 < baseStart_7443836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443868 : List Nat := [2, 2, 3, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7443868 : Nat := 118140960795 + 7443868 * 2 ^ 59
def prefixEnd_7443868 : Nat := 4983230072969 + 3 ^ 40 * 7443868 * 2
def baseEnd_7443868 : Nat := 3822282212622587065916281

theorem tailTrace_7443868 : CollatzResearch.WordTrace tailWord_7443868 prefixEnd_7443868 3822282212622587065916281 := by
  unfold tailWord_7443868
  simp only [CollatzResearch.WordTrace]
  refine ⟨135750085298072511142618129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181000113730763348190157505 135750085298072511142618129)
  ·
    refine ⟨101812563973554383356963597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135750085298072511142618129 101812563973554383356963597)
    ·
      refine ⟨38179711490082893758861349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101812563973554383356963597 38179711490082893758861349)
      ·
        refine ⟨7158695904390542579786503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38179711490082893758861349 7158695904390542579786503)
        ·
          refine ⟨10738043856585813869679755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7158695904390542579786503 10738043856585813869679755)
          ·
            refine ⟨16107065784878720804519633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10738043856585813869679755 16107065784878720804519633)
            ·
              refine ⟨12080299338659040603389725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16107065784878720804519633 12080299338659040603389725)
              ·
                refine ⟨4530112251997140226271147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12080299338659040603389725 4530112251997140226271147)
                ·
                  refine ⟨6795168377995710339406721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530112251997140226271147 6795168377995710339406721)
                  ·
                    refine ⟨5096376283496782754555041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795168377995710339406721 5096376283496782754555041)
                    ·
                      refine ⟨3822282212622587065916281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096376283496782754555041 3822282212622587065916281)
                      ·
                        rfl

theorem cell23_7443868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7443868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443868 prefixEnd_7443868 := by exact prefixLift 7443868
  have htrace : WordTrace (prefixWord ++ tailWord_7443868) baseStart_7443868 baseEnd_7443868 := by
    simpa [prefixWord, tailWord_7443868, baseEnd_7443868] using wordTrace_append hprefix tailTrace_7443868
  have hstable : (prefixWord ++ tailWord_7443868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443868).length < 2 ^ (prefixWord ++ tailWord_7443868).sum := by decide
  have hdescent : baseEnd_7443868 < baseStart_7443868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443907 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 2, 2, 2]
def baseStart_7443907 : Nat := 118140960795 + 7443907 * 2 ^ 59
def prefixEnd_7443907 : Nat := 4983230072969 + 3 ^ 40 * 7443907 * 2
def baseEnd_7443907 : Nat := 3822302238368112413328601

theorem tailTrace_7443907 : CollatzResearch.WordTrace tailWord_7443907 prefixEnd_7443907 3822302238368112413328601 := by
  unfold tailWord_7443907
  simp only [CollatzResearch.WordTrace]
  refine ⟨271501593043003731945905975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181001062028669154630603983 271501593043003731945905975)
  ·
    refine ⟨407252389564505597918858963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271501593043003731945905975 407252389564505597918858963)
    ·
      refine ⟨610878584346758396878288445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407252389564505597918858963 610878584346758396878288445)
      ·
        refine ⟨229079469130034398829358167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 610878584346758396878288445 229079469130034398829358167)
        ·
          refine ⟨343619203695051598244037251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229079469130034398829358167 343619203695051598244037251)
          ·
            refine ⟨515428805542577397366055877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343619203695051598244037251 515428805542577397366055877)
            ·
              refine ⟨96642901039233262006135477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 515428805542577397366055877 96642901039233262006135477)
              ·
                refine ⟨9060271972428118313075201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96642901039233262006135477 9060271972428118313075201)
                ·
                  refine ⟨6795203979321088734806401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9060271972428118313075201 6795203979321088734806401)
                  ·
                    refine ⟨5096402984490816551104801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795203979321088734806401 5096402984490816551104801)
                    ·
                      refine ⟨3822302238368112413328601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096402984490816551104801 3822302238368112413328601)
                      ·
                        rfl

theorem cell23_7443907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 2, 2].length) (baseStart_7443907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443907 prefixEnd_7443907 := by exact prefixLift 7443907
  have htrace : WordTrace (prefixWord ++ tailWord_7443907) baseStart_7443907 baseEnd_7443907 := by
    simpa [prefixWord, tailWord_7443907, baseEnd_7443907] using wordTrace_append hprefix tailTrace_7443907
  have hstable : (prefixWord ++ tailWord_7443907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443907).length < 2 ^ (prefixWord ++ tailWord_7443907).sum := by decide
  have hdescent : baseEnd_7443907 < baseStart_7443907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443953 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_7443953 : Nat := 118140960795 + 7443953 * 2 ^ 59
def prefixEnd_7443953 : Nat := 4983230072969 + 3 ^ 40 * 7443953 * 2
def baseEnd_7443953 : Nat := 3822325858478219233353389

theorem tailTrace_7443953 : CollatzResearch.WordTrace tailWord_7443953 prefixEnd_7443953 3822325858478219233353389 := by
  unfold tailWord_7443953
  simp only [CollatzResearch.WordTrace]
  refine ⟨271503270800837081802080513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181002180533891387868053675 271503270800837081802080513)
  ·
    refine ⟨203627453100627811351560385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271503270800837081802080513 203627453100627811351560385)
    ·
      refine ⟨152720589825470858513670289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203627453100627811351560385 152720589825470858513670289)
      ·
        refine ⟨114540442369103143885252717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152720589825470858513670289 114540442369103143885252717)
        ·
          refine ⟨42952665888413678956969769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114540442369103143885252717 42952665888413678956969769)
          ·
            refine ⟨32214499416310259217727327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42952665888413678956969769 32214499416310259217727327)
            ·
              refine ⟨48321749124465388826590991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32214499416310259217727327 48321749124465388826590991)
              ·
                refine ⟨72482623686698083239886487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48321749124465388826590991 72482623686698083239886487)
                ·
                  refine ⟨108723935530047124859829731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72482623686698083239886487 108723935530047124859829731)
                  ·
                    refine ⟨163085903295070687289744597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108723935530047124859829731 163085903295070687289744597)
                    ·
                      refine ⟨3822325858478219233353389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163085903295070687289744597 3822325858478219233353389)
                      ·
                        rfl

theorem cell23_7443953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_7443953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443953 prefixEnd_7443953 := by exact prefixLift 7443953
  have htrace : WordTrace (prefixWord ++ tailWord_7443953) baseStart_7443953 baseEnd_7443953 := by
    simpa [prefixWord, tailWord_7443953, baseEnd_7443953] using wordTrace_append hprefix tailTrace_7443953
  have hstable : (prefixWord ++ tailWord_7443953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443953).length < 2 ^ (prefixWord ++ tailWord_7443953).sum := by decide
  have hdescent : baseEnd_7443953 < baseStart_7443953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443958 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_7443958 : Nat := 118140960795 + 7443958 * 2 ^ 59
def prefixEnd_7443958 : Nat := 4983230072969 + 3 ^ 40 * 7443958 * 2
def baseEnd_7443958 : Nat := 3822328425881491713790867

theorem tailTrace_7443958 : CollatzResearch.WordTrace tailWord_7443958 prefixEnd_7443958 3822328425881491713790867 := by
  unfold tailWord_7443958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16968965822863685478500783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181002302110545978437341685 16968965822863685478500783)
  ·
    refine ⟨25453448734295528217751175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16968965822863685478500783 25453448734295528217751175)
    ·
      refine ⟨38180173101443292326626763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25453448734295528217751175 38180173101443292326626763)
      ·
        refine ⟨57270259652164938489940145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38180173101443292326626763 57270259652164938489940145)
        ·
          refine ⟨42952694739123703867455109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57270259652164938489940145 42952694739123703867455109)
          ·
            refine ⟨8053630263585694475147833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42952694739123703867455109 8053630263585694475147833)
            ·
              refine ⟨6040222697689270856360875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8053630263585694475147833 6040222697689270856360875)
              ·
                refine ⟨9060334046533906284541313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040222697689270856360875 9060334046533906284541313)
                ·
                  refine ⟨6795250534900429713405985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9060334046533906284541313 6795250534900429713405985)
                  ·
                    refine ⟨5096437901175322285054489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795250534900429713405985 5096437901175322285054489)
                    ·
                      refine ⟨3822328425881491713790867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096437901175322285054489 3822328425881491713790867)
                      ·
                        rfl

theorem cell23_7443958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_7443958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443958 prefixEnd_7443958 := by exact prefixLift 7443958
  have htrace : WordTrace (prefixWord ++ tailWord_7443958) baseStart_7443958 baseEnd_7443958 := by
    simpa [prefixWord, tailWord_7443958, baseEnd_7443958] using wordTrace_append hprefix tailTrace_7443958
  have hstable : (prefixWord ++ tailWord_7443958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443958).length < 2 ^ (prefixWord ++ tailWord_7443958).sum := by decide
  have hdescent : baseEnd_7443958 < baseStart_7443958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443997 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_7443997 : Nat := 118140960795 + 7443997 * 2 ^ 59
def prefixEnd_7443997 : Nat := 4983230072969 + 3 ^ 40 * 7443997 * 2
def baseEnd_7443997 : Nat := 3822348451627017061203187

theorem tailTrace_7443997 : CollatzResearch.WordTrace tailWord_7443997 prefixEnd_7443997 3822348451627017061203187 := by
  unfold tailWord_7443997
  simp only [CollatzResearch.WordTrace]
  refine ⟨271504875612677677316682245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181003250408451784877788163 271504875612677677316682245)
  ·
    refine ⟨50907164177377064496877921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271504875612677677316682245 50907164177377064496877921)
    ·
      refine ⟨38180373133032798372658441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50907164177377064496877921 38180373133032798372658441)
      ·
        refine ⟨28635279849774598779493831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38180373133032798372658441 28635279849774598779493831)
        ·
          refine ⟨42952919774661898169240747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28635279849774598779493831 42952919774661898169240747)
          ·
            refine ⟨64429379661992847253861121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42952919774661898169240747 64429379661992847253861121)
            ·
              refine ⟨48322034746494635440395841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64429379661992847253861121 48322034746494635440395841)
              ·
                refine ⟨36241526059870976580296881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48322034746494635440395841 36241526059870976580296881)
                ·
                  refine ⟨27181144544903232435222661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36241526059870976580296881 27181144544903232435222661)
                  ·
                    refine ⟨5096464602169356081604249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27181144544903232435222661 5096464602169356081604249)
                    ·
                      refine ⟨3822348451627017061203187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096464602169356081604249 3822348451627017061203187)
                      ·
                        rfl

theorem cell23_7443997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_7443997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443997 prefixEnd_7443997 := by exact prefixLift 7443997
  have htrace : WordTrace (prefixWord ++ tailWord_7443997) baseStart_7443997 baseEnd_7443997 := by
    simpa [prefixWord, tailWord_7443997, baseEnd_7443997] using wordTrace_append hprefix tailTrace_7443997
  have hstable : (prefixWord ++ tailWord_7443997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443997).length < 2 ^ (prefixWord ++ tailWord_7443997).sum := by decide
  have hdescent : baseEnd_7443997 < baseStart_7443997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7443998 : List Nat := [4, 3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_7443998 : Nat := 118140960795 + 7443998 * 2 ^ 59
def prefixEnd_7443998 : Nat := 4983230072969 + 3 ^ 40 * 7443998 * 2
def baseEnd_7443998 : Nat := 424705440567519061921187

theorem tailTrace_7443998 : CollatzResearch.WordTrace tailWord_7443998 prefixEnd_7443998 424705440567519061921187 := by
  unfold tailWord_7443998
  simp only [CollatzResearch.WordTrace]
  refine ⟨33938114010709256810933581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181003274723782702991645765 33938114010709256810933581)
  ·
    refine ⟨12726792754015971304100093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33938114010709256810933581 12726792754015971304100093)
    ·
      refine ⟨4772547282755989239037535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12726792754015971304100093 4772547282755989239037535)
      ·
        refine ⟨7158820924133983858556303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4772547282755989239037535 7158820924133983858556303)
        ·
          refine ⟨10738231386200975787834455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7158820924133983858556303 10738231386200975787834455)
          ·
            refine ⟨16107347079301463681751683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10738231386200975787834455 16107347079301463681751683)
            ·
              refine ⟨24161020618952195522627525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16107347079301463681751683 24161020618952195522627525)
              ·
                refine ⟨4530191366053536660492661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24161020618952195522627525 4530191366053536660492661)
                ·
                  refine ⟨424705440567519061921187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4530191366053536660492661 424705440567519061921187)
                  ·
                    rfl

theorem cell23_7443998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_7443998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7443998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7443998 prefixEnd_7443998 := by exact prefixLift 7443998
  have htrace : WordTrace (prefixWord ++ tailWord_7443998) baseStart_7443998 baseEnd_7443998 := by
    simpa [prefixWord, tailWord_7443998, baseEnd_7443998] using wordTrace_append hprefix tailTrace_7443998
  have hstable : (prefixWord ++ tailWord_7443998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7443998).length < 2 ^ (prefixWord ++ tailWord_7443998).sum := by decide
  have hdescent : baseEnd_7443998 < baseStart_7443998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7443998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444014 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_7444014 : Nat := 118140960795 + 7444014 * 2 ^ 59
def prefixEnd_7444014 : Nat := 4983230072969 + 3 ^ 40 * 7444014 * 2
def baseEnd_7444014 : Nat := 3822357180798143494690609

theorem tailTrace_7444014 : CollatzResearch.WordTrace tailWord_7444014 prefixEnd_7444014 3822357180798143494690609 := by
  unfold tailWord_7444014
  simp only [CollatzResearch.WordTrace]
  refine ⟨33938186956702011152506387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181003663769077392813367397 33938186956702011152506387)
  ·
    refine ⟨50907280435053016728759581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33938186956702011152506387 50907280435053016728759581)
    ·
      refine ⟨19090230163144881273284843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50907280435053016728759581 19090230163144881273284843)
      ·
        refine ⟨28635345244717321909927265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19090230163144881273284843 28635345244717321909927265)
        ·
          refine ⟨21476508933537991432445449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28635345244717321909927265 21476508933537991432445449)
          ·
            refine ⟨16107381700153493574334087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21476508933537991432445449 16107381700153493574334087)
            ·
              refine ⟨24161072550230240361501131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16107381700153493574334087 24161072550230240361501131)
              ·
                refine ⟨36241608825345360542251697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24161072550230240361501131 36241608825345360542251697)
                ·
                  refine ⟨27181206619009020406688773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36241608825345360542251697 27181206619009020406688773)
                  ·
                    refine ⟨5096476241064191326254145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27181206619009020406688773 5096476241064191326254145)
                    ·
                      refine ⟨3822357180798143494690609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096476241064191326254145 3822357180798143494690609)
                      ·
                        rfl

theorem cell23_7444014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_7444014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444014 prefixEnd_7444014 := by exact prefixLift 7444014
  have htrace : WordTrace (prefixWord ++ tailWord_7444014) baseStart_7444014 baseEnd_7444014 := by
    simpa [prefixWord, tailWord_7444014, baseEnd_7444014] using wordTrace_append hprefix tailTrace_7444014
  have hstable : (prefixWord ++ tailWord_7444014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444014).length < 2 ^ (prefixWord ++ tailWord_7444014).sum := by decide
  have hdescent : baseEnd_7444014 < baseStart_7444014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444043 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 5]
def baseStart_7444043 : Nat := 118140960795 + 7444043 * 2 ^ 59
def prefixEnd_7444043 : Nat := 4983230072969 + 3 ^ 40 * 7444043 * 2
def baseEnd_7444043 : Nat := 3822372071737123881227975

theorem tailTrace_7444043 : CollatzResearch.WordTrace tailWord_7444043 prefixEnd_7444043 3822372071737123881227975 := by
  unfold tailWord_7444043
  simp only [CollatzResearch.WordTrace]
  refine ⟨271506553370511027172856783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181004368913674018115237855 271506553370511027172856783)
  ·
    refine ⟨407259830055766540759285175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271506553370511027172856783 407259830055766540759285175)
    ·
      refine ⟨610889745083649811138927763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407259830055766540759285175 610889745083649811138927763)
      ·
        refine ⟨916334617625474716708391645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610889745083649811138927763 916334617625474716708391645)
        ·
          refine ⟨343625481609553018765646867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 916334617625474716708391645 343625481609553018765646867)
          ·
            refine ⟨515438222414329528148470301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343625481609553018765646867 515438222414329528148470301)
            ·
              refine ⟨193289333405373573055676363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 515438222414329528148470301 193289333405373573055676363)
              ·
                refine ⟨289934000108060359583514545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193289333405373573055676363 289934000108060359583514545)
                ·
                  refine ⟨217450500081045269687635909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289934000108060359583514545 217450500081045269687635909)
                  ·
                    refine ⟨40771968765195988066431733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217450500081045269687635909 40771968765195988066431733)
                    ·
                      refine ⟨3822372071737123881227975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40771968765195988066431733 3822372071737123881227975)
                      ·
                        rfl

theorem cell23_7444043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_7444043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444043 prefixEnd_7444043 := by exact prefixLift 7444043
  have htrace : WordTrace (prefixWord ++ tailWord_7444043) baseStart_7444043 baseEnd_7444043 := by
    simpa [prefixWord, tailWord_7444043, baseEnd_7444043] using wordTrace_append hprefix tailTrace_7444043
  have hstable : (prefixWord ++ tailWord_7444043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444043).length < 2 ^ (prefixWord ++ tailWord_7444043).sum := by decide
  have hdescent : baseEnd_7444043 < baseStart_7444043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444057 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 2, 3, 2]
def baseStart_7444057 : Nat := 118140960795 + 7444057 * 2 ^ 59
def prefixEnd_7444057 : Nat := 4983230072969 + 3 ^ 40 * 7444057 * 2
def baseEnd_7444057 : Nat := 3822379260466286826452911

theorem tailTrace_7444057 : CollatzResearch.WordTrace tailWord_7444057 prefixEnd_7444057 3822379260466286826452911 := by
  unfold tailWord_7444057
  simp only [CollatzResearch.WordTrace]
  refine ⟨271507063992460307563866425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181004709328306871709244283 271507063992460307563866425)
  ·
    refine ⟨203630297994345230672899819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271507063992460307563866425 203630297994345230672899819)
    ·
      refine ⟨305445446991517846009349729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203630297994345230672899819 305445446991517846009349729)
      ·
        refine ⟨229084085243638384507012297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305445446991517846009349729 229084085243638384507012297)
        ·
          refine ⟨171813063932728788380259223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229084085243638384507012297 171813063932728788380259223)
          ·
            refine ⟨257719595899093182570388835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171813063932728788380259223 257719595899093182570388835)
            ·
              refine ⟨386579393848639773855583253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257719595899093182570388835 386579393848639773855583253)
              ·
                refine ⟨18120909086654989399480465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 386579393848639773855583253 18120909086654989399480465)
                ·
                  refine ⟨13590681814991242049610349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18120909086654989399480465 13590681814991242049610349)
                  ·
                    refine ⟨5096505680621715768603881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13590681814991242049610349 5096505680621715768603881)
                    ·
                      refine ⟨3822379260466286826452911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096505680621715768603881 3822379260466286826452911)
                      ·
                        rfl

theorem cell23_7444057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 3, 2].length) (baseStart_7444057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444057 prefixEnd_7444057 := by exact prefixLift 7444057
  have htrace : WordTrace (prefixWord ++ tailWord_7444057) baseStart_7444057 baseEnd_7444057 := by
    simpa [prefixWord, tailWord_7444057, baseEnd_7444057] using wordTrace_append hprefix tailTrace_7444057
  have hstable : (prefixWord ++ tailWord_7444057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444057).length < 2 ^ (prefixWord ++ tailWord_7444057).sum := by decide
  have hdescent : baseEnd_7444057 < baseStart_7444057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444063 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 2, 10]
def baseStart_7444063 : Nat := 118140960795 + 7444063 * 2 ^ 59
def prefixEnd_7444063 : Nat := 4983230072969 + 3 ^ 40 * 7444063 * 2
def baseEnd_7444063 : Nat := 1274127447116737934325961

theorem tailTrace_7444063 : CollatzResearch.WordTrace tailWord_7444063 prefixEnd_7444063 1274127447116737934325961 := by
  unfold tailWord_7444063
  simp only [CollatzResearch.WordTrace]
  refine ⟨271507282830438570588584843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181004855220292380392389895 271507282830438570588584843)
  ·
    refine ⟨407260924245657855882877265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271507282830438570588584843 407260924245657855882877265)
    ·
      refine ⟨305445693184243391912157949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407260924245657855882877265 305445693184243391912157949)
      ·
        refine ⟨114542134944091271967059231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305445693184243391912157949 114542134944091271967059231)
        ·
          refine ⟨171813202416136907950588847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114542134944091271967059231 171813202416136907950588847)
          ·
            refine ⟨257719803624205361925883271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171813202416136907950588847 257719803624205361925883271)
            ·
              refine ⟨386579705436308042888824907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257719803624205361925883271 386579705436308042888824907)
              ·
                refine ⟨579869558154462064333237361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386579705436308042888824907 579869558154462064333237361)
                ·
                  refine ⟨434902168615846548249928021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579869558154462064333237361 434902168615846548249928021)
                  ·
                    refine ⟨1274127447116737934325961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 434902168615846548249928021 1274127447116737934325961)
                    ·
                      rfl

theorem cell23_7444063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_7444063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444063 prefixEnd_7444063 := by exact prefixLift 7444063
  have htrace : WordTrace (prefixWord ++ tailWord_7444063) baseStart_7444063 baseEnd_7444063 := by
    simpa [prefixWord, tailWord_7444063, baseEnd_7444063] using wordTrace_append hprefix tailTrace_7444063
  have hstable : (prefixWord ++ tailWord_7444063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444063).length < 2 ^ (prefixWord ++ tailWord_7444063).sum := by decide
  have hdescent : baseEnd_7444063 < baseStart_7444063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444097 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 4, 4]
def baseStart_7444097 : Nat := 118140960795 + 7444097 * 2 ^ 59
def prefixEnd_7444097 : Nat := 4983230072969 + 3 ^ 40 * 7444097 * 2
def baseEnd_7444097 : Nat := 1274133266564155556650909

theorem tailTrace_7444097 : CollatzResearch.WordTrace tailWord_7444097 prefixEnd_7444097 1274133266564155556650909 := by
  unfold tailWord_7444097
  simp only [CollatzResearch.WordTrace]
  refine ⟨271508522912315394395322545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181005681941543596263548363 271508522912315394395322545)
  ·
    refine ⟨203631392184236545796491909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271508522912315394395322545 203631392184236545796491909)
    ·
      refine ⟨38180886034544352336842233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203631392184236545796491909 38180886034544352336842233)
      ·
        refine ⟨28635664525908264252631675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38180886034544352336842233 28635664525908264252631675)
        ·
          refine ⟨42953496788862396378947513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28635664525908264252631675 42953496788862396378947513)
          ·
            refine ⟨32215122591646797284210635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42953496788862396378947513 32215122591646797284210635)
            ·
              refine ⟨48322683887470195926315953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32215122591646797284210635 48322683887470195926315953)
              ·
                refine ⟨36242012915602646944736965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48322683887470195926315953 36242012915602646944736965)
                ·
                  refine ⟨6795377421675496302138181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36242012915602646944736965 6795377421675496302138181)
                  ·
                    refine ⟨1274133266564155556650909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6795377421675496302138181 1274133266564155556650909)
                    ·
                      rfl

theorem cell23_7444097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_7444097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444097 prefixEnd_7444097 := by exact prefixLift 7444097
  have htrace : WordTrace (prefixWord ++ tailWord_7444097) baseStart_7444097 baseEnd_7444097 := by
    simpa [prefixWord, tailWord_7444097, baseEnd_7444097] using wordTrace_append hprefix tailTrace_7444097
  have hstable : (prefixWord ++ tailWord_7444097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444097).length < 2 ^ (prefixWord ++ tailWord_7444097).sum := by decide
  have hdescent : baseEnd_7444097 < baseStart_7444097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444107 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 1, 2, 3]
def baseStart_7444107 : Nat := 118140960795 + 7444107 * 2 ^ 59
def prefixEnd_7444107 : Nat := 4983230072969 + 3 ^ 40 * 7444107 * 2
def baseEnd_7444107 : Nat := 3822404934499011630827681

theorem tailTrace_7444107 : CollatzResearch.WordTrace tailWord_7444107 prefixEnd_7444107 3822404934499011630827681 := by
  unfold tailWord_7444107
  simp only [CollatzResearch.WordTrace]
  refine ⟨271508887642279166103186575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181005925094852777402124383 271508887642279166103186575)
  ·
    refine ⟨407263331463418749154779863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271508887642279166103186575 407263331463418749154779863)
    ·
      refine ⟨610894997195128123732169795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407263331463418749154779863 610894997195128123732169795)
      ·
        refine ⟨916342495792692185598254693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610894997195128123732169795 916342495792692185598254693)
        ·
          refine ⟨171814217961129784799672755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 916342495792692185598254693 171814217961129784799672755)
          ·
            refine ⟨257721326941694677199509133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171814217961129784799672755 257721326941694677199509133)
            ·
              refine ⟨96645497603135503949815925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257721326941694677199509133 96645497603135503949815925)
              ·
                refine ⟨9060515400293953495295243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96645497603135503949815925 9060515400293953495295243)
                ·
                  refine ⟨13590773100440930242942865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9060515400293953495295243 13590773100440930242942865)
                  ·
                    refine ⟨10193079825330697682207149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13590773100440930242942865 10193079825330697682207149)
                    ·
                      refine ⟨3822404934499011630827681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10193079825330697682207149 3822404934499011630827681)
                      ·
                        rfl

theorem cell23_7444107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 2, 3].length) (baseStart_7444107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444107 prefixEnd_7444107 := by exact prefixLift 7444107
  have htrace : WordTrace (prefixWord ++ tailWord_7444107) baseStart_7444107 baseEnd_7444107 := by
    simpa [prefixWord, tailWord_7444107, baseEnd_7444107] using wordTrace_append hprefix tailTrace_7444107
  have hstable : (prefixWord ++ tailWord_7444107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444107).length < 2 ^ (prefixWord ++ tailWord_7444107).sum := by decide
  have hdescent : baseEnd_7444107 < baseStart_7444107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444110 : List Nat := [4, 1, 1, 3, 1, 2, 11]
def baseStart_7444110 : Nat := 118140960795 + 7444110 * 2 ^ 59
def prefixEnd_7444110 : Nat := 4983230072969 + 3 ^ 40 * 7444110 * 2
def baseEnd_7444110 : Nat := 47190203394333026161607

theorem tailTrace_7444110 : CollatzResearch.WordTrace tailWord_7444110 prefixEnd_7444110 47190203394333026161607 := by
  unfold tailWord_7444110
  simp only [CollatzResearch.WordTrace]
  refine ⟨33938624632658537201943223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181005998040845531743697189 33938624632658537201943223)
  ·
    refine ⟨50907936948987805802914835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33938624632658537201943223 50907936948987805802914835)
    ·
      refine ⟨76361905423481708704372253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50907936948987805802914835 76361905423481708704372253)
      ·
        refine ⟨28635714533805640764139595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76361905423481708704372253 28635714533805640764139595)
        ·
          refine ⟨42953571800708461146209393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28635714533805640764139595 42953571800708461146209393)
          ·
            refine ⟨32215178850531345859657045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42953571800708461146209393 32215178850531345859657045)
            ·
              refine ⟨47190203394333026161607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32215178850531345859657045 47190203394333026161607)
              ·
                rfl

theorem cell23_7444110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 11].length) (baseStart_7444110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444110 prefixEnd_7444110 := by exact prefixLift 7444110
  have htrace : WordTrace (prefixWord ++ tailWord_7444110) baseStart_7444110 baseEnd_7444110 := by
    simpa [prefixWord, tailWord_7444110, baseEnd_7444110] using wordTrace_append hprefix tailTrace_7444110
  have hstable : (prefixWord ++ tailWord_7444110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444110).length < 2 ^ (prefixWord ++ tailWord_7444110).sum := by decide
  have hdescent : baseEnd_7444110 < baseStart_7444110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444172 : List Nat := [2, 2, 1, 5, 2, 2, 2, 2, 1, 2, 2]
def baseStart_7444172 : Nat := 118140960795 + 7444172 * 2 ^ 59
def prefixEnd_7444172 : Nat := 4983230072969 + 3 ^ 40 * 7444172 * 2
def baseEnd_7444172 : Nat := 3822438310741553876514883

theorem tailTrace_7444172 : CollatzResearch.WordTrace tailWord_7444172 prefixEnd_7444172 3822438310741553876514883 := by
  unfold tailWord_7444172
  simp only [CollatzResearch.WordTrace]
  refine ⟨135755629193521841102151385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181007505591362454802868513 135755629193521841102151385)
  ·
    refine ⟨101816721895141380826613539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135755629193521841102151385 101816721895141380826613539)
    ·
      refine ⟨152725082842712071239920309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101816721895141380826613539 152725082842712071239920309)
      ·
        refine ⟨14317976516504256678742529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152725082842712071239920309 14317976516504256678742529)
        ·
          refine ⟨10738482387378192509056897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14317976516504256678742529 10738482387378192509056897)
          ·
            refine ⟨8053861790533644381792673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10738482387378192509056897 8053861790533644381792673)
            ·
              refine ⟨6040396342900233286344505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8053861790533644381792673 6040396342900233286344505)
              ·
                refine ⟨4530297257175174964758379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6040396342900233286344505 4530297257175174964758379)
                ·
                  refine ⟨6795445885762762447137569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530297257175174964758379 6795445885762762447137569)
                  ·
                    refine ⟨5096584414322071835353177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795445885762762447137569 5096584414322071835353177)
                    ·
                      refine ⟨3822438310741553876514883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096584414322071835353177 3822438310741553876514883)
                      ·
                        rfl

theorem cell23_7444172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_7444172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444172 prefixEnd_7444172 := by exact prefixLift 7444172
  have htrace : WordTrace (prefixWord ++ tailWord_7444172) baseStart_7444172 baseEnd_7444172 := by
    simpa [prefixWord, tailWord_7444172, baseEnd_7444172] using wordTrace_append hprefix tailTrace_7444172
  have hstable : (prefixWord ++ tailWord_7444172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444172).length < 2 ^ (prefixWord ++ tailWord_7444172).sum := by decide
  have hdescent : baseEnd_7444172 < baseStart_7444172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444197 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 2, 4, 3]
def baseStart_7444197 : Nat := 118140960795 + 7444197 * 2 ^ 59
def prefixEnd_7444197 : Nat := 4983230072969 + 3 ^ 40 * 7444197 * 2
def baseEnd_7444197 : Nat := 3822451147757916278702267

theorem tailTrace_7444197 : CollatzResearch.WordTrace tailWord_7444197 prefixEnd_7444197 3822451147757916278702267 := by
  unfold tailWord_7444197
  simp only [CollatzResearch.WordTrace]
  refine ⟨271512170211953111473962845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181008113474635407649308563 271512170211953111473962845)
  ·
    refine ⟨101817063829482416802736067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271512170211953111473962845 101817063829482416802736067)
    ·
      refine ⟨152725595744223625204104101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101817063829482416802736067 152725595744223625204104101)
      ·
        refine ⟨28636049202041929725769519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152725595744223625204104101 28636049202041929725769519)
        ·
          refine ⟨42954073803062894588654279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28636049202041929725769519 42954073803062894588654279)
          ·
            refine ⟨64431110704594341882981419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42954073803062894588654279 64431110704594341882981419)
            ·
              refine ⟨96646666056891512824472129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64431110704594341882981419 96646666056891512824472129)
              ·
                refine ⟨72484999542668634618354097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96646666056891512824472129 72484999542668634618354097)
                ·
                  refine ⟨54363749657001475963765573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72484999542668634618354097 54363749657001475963765573)
                  ·
                    refine ⟨10193203060687776743206045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54363749657001475963765573 10193203060687776743206045)
                    ·
                      refine ⟨3822451147757916278702267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10193203060687776743206045 3822451147757916278702267)
                      ·
                        rfl

theorem cell23_7444197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_7444197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444197 prefixEnd_7444197 := by exact prefixLift 7444197
  have htrace : WordTrace (prefixWord ++ tailWord_7444197) baseStart_7444197 baseEnd_7444197 := by
    simpa [prefixWord, tailWord_7444197, baseEnd_7444197] using wordTrace_append hprefix tailTrace_7444197
  have hstable : (prefixWord ++ tailWord_7444197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444197).length < 2 ^ (prefixWord ++ tailWord_7444197).sum := by decide
  have hdescent : baseEnd_7444197 < baseStart_7444197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444227 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 3]
def baseStart_7444227 : Nat := 118140960795 + 7444227 * 2 ^ 59
def prefixEnd_7444227 : Nat := 4983230072969 + 3 ^ 40 * 7444227 * 2
def baseEnd_7444227 : Nat := 3822466552177551161327129

theorem tailTrace_7444227 : CollatzResearch.WordTrace tailWord_7444227 prefixEnd_7444227 3822466552177551161327129 := by
  unfold tailWord_7444227
  simp only [CollatzResearch.WordTrace]
  refine ⟨271513264401844426597554935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181008842934562951065036623 271513264401844426597554935)
  ·
    refine ⟨407269896602766639896332403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271513264401844426597554935 407269896602766639896332403)
    ·
      refine ⟨610904844904149959844498605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407269896602766639896332403 610904844904149959844498605)
      ·
        refine ⟨229089316839056234941686977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 610904844904149959844498605 229089316839056234941686977)
        ·
          refine ⟨171816987629292176206265233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229089316839056234941686977 171816987629292176206265233)
          ·
            refine ⟨128862740721969132154698925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171816987629292176206265233 128862740721969132154698925)
            ·
              refine ⟨48323527770738424558012097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128862740721969132154698925 48323527770738424558012097)
              ·
                refine ⟨36242645828053818418509073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48323527770738424558012097 36242645828053818418509073)
                ·
                  refine ⟨27181984371040363813881805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36242645828053818418509073 27181984371040363813881805)
                  ·
                    refine ⟨10193244139140136430205677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27181984371040363813881805 10193244139140136430205677)
                    ·
                      refine ⟨3822466552177551161327129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10193244139140136430205677 3822466552177551161327129)
                      ·
                        rfl

theorem cell23_7444227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_7444227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444227 prefixEnd_7444227 := by exact prefixLift 7444227
  have htrace : WordTrace (prefixWord ++ tailWord_7444227) baseStart_7444227 baseEnd_7444227 := by
    simpa [prefixWord, tailWord_7444227, baseEnd_7444227] using wordTrace_append hprefix tailTrace_7444227
  have hstable : (prefixWord ++ tailWord_7444227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444227).length < 2 ^ (prefixWord ++ tailWord_7444227).sum := by decide
  have hdescent : baseEnd_7444227 < baseStart_7444227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444228 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_7444228 : Nat := 118140960795 + 7444228 * 2 ^ 59
def prefixEnd_7444228 : Nat := 4983230072969 + 3 ^ 40 * 7444228 * 2
def baseEnd_7444228 : Nat := 3822467065658205657414625

theorem tailTrace_7444228 : CollatzResearch.WordTrace tailWord_7444228 prefixEnd_7444228 3822467065658205657414625 := by
  unfold tailWord_7444228
  simp only [CollatzResearch.WordTrace]
  refine ⟨135756650437420401884170669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181008867249893869178894225 135756650437420401884170669)
  ·
    refine ⟨50908743914032650706564001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135756650437420401884170669 50908743914032650706564001)
    ·
      refine ⟨38181557935524488029923001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50908743914032650706564001 38181557935524488029923001)
      ·
        refine ⟨28636168451643366022442251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38181557935524488029923001 28636168451643366022442251)
        ·
          refine ⟨42954252677465049033663377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28636168451643366022442251 42954252677465049033663377)
          ·
            refine ⟨32215689508098786775247533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42954252677465049033663377 32215689508098786775247533)
            ·
              refine ⟨12080883565537045040717825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32215689508098786775247533 12080883565537045040717825)
              ·
                refine ⟨9060662674152783780538369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12080883565537045040717825 9060662674152783780538369)
                ·
                  refine ⟨6795497005614587835403777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9060662674152783780538369 6795497005614587835403777)
                  ·
                    refine ⟨5096622754210940876552833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795497005614587835403777 5096622754210940876552833)
                    ·
                      refine ⟨3822467065658205657414625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096622754210940876552833 3822467065658205657414625)
                      ·
                        rfl

theorem cell23_7444228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_7444228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444228 prefixEnd_7444228 := by exact prefixLift 7444228
  have htrace : WordTrace (prefixWord ++ tailWord_7444228) baseStart_7444228 baseEnd_7444228 := by
    simpa [prefixWord, tailWord_7444228, baseEnd_7444228] using wordTrace_append hprefix tailTrace_7444228
  have hstable : (prefixWord ++ tailWord_7444228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444228).length < 2 ^ (prefixWord ++ tailWord_7444228).sum := by decide
  have hdescent : baseEnd_7444228 < baseStart_7444228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444234 : List Nat := [3, 1, 2, 2, 1, 3, 2, 4, 5]
def baseStart_7444234 : Nat := 118140960795 + 7444234 * 2 ^ 59
def prefixEnd_7444234 : Nat := 4983230072969 + 3 ^ 40 * 7444234 * 2
def baseEnd_7444234 : Nat := 424718905171348070437733

theorem tailTrace_7444234 : CollatzResearch.WordTrace tailWord_7444234 prefixEnd_7444234 424718905171348070437733 := by
  unfold tailWord_7444234
  simp only [CollatzResearch.WordTrace]
  refine ⟨67878379928204766698264939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181009013141879377862039837 67878379928204766698264939)
  ·
    refine ⟨101817569892307150047397409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67878379928204766698264939 101817569892307150047397409)
    ·
      refine ⟨76363177419230362535548057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101817569892307150047397409 76363177419230362535548057)
      ·
        refine ⟨57272383064422771901661043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76363177419230362535548057 57272383064422771901661043)
        ·
          refine ⟨85908574596634157852491565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57272383064422771901661043 85908574596634157852491565)
          ·
            refine ⟨32215715473737809194684337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85908574596634157852491565 32215715473737809194684337)
            ·
              refine ⟨24161786605303356896013253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32215715473737809194684337 24161786605303356896013253)
              ·
                refine ⟨4530334988494379418002485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24161786605303356896013253 4530334988494379418002485)
                ·
                  refine ⟨424718905171348070437733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4530334988494379418002485 424718905171348070437733)
                  ·
                    rfl

theorem cell23_7444234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_7444234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444234 prefixEnd_7444234 := by exact prefixLift 7444234
  have htrace : WordTrace (prefixWord ++ tailWord_7444234) baseStart_7444234 baseEnd_7444234 := by
    simpa [prefixWord, tailWord_7444234, baseEnd_7444234] using wordTrace_append hprefix tailTrace_7444234
  have hstable : (prefixWord ++ tailWord_7444234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444234).length < 2 ^ (prefixWord ++ tailWord_7444234).sum := by decide
  have hdescent : baseEnd_7444234 < baseStart_7444234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444247 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 1, 7]
def baseStart_7444247 : Nat := 118140960795 + 7444247 * 2 ^ 59
def prefixEnd_7444247 : Nat := 4983230072969 + 3 ^ 40 * 7444247 * 2
def baseEnd_7444247 : Nat := 1274158940596880361025679

theorem tailTrace_7444247 : CollatzResearch.WordTrace tailWord_7444247 prefixEnd_7444247 1274158940596880361025679 := by
  unfold tailWord_7444247
  simp only [CollatzResearch.WordTrace]
  refine ⟨271513993861771970013282995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181009329241181313342188663 271513993861771970013282995)
  ·
    refine ⟨407270990792657955019924493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271513993861771970013282995 407270990792657955019924493)
    ·
      refine ⟨152726621547246733132471685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407270990792657955019924493 152726621547246733132471685)
      ·
        refine ⟨28636241540108762462338441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152726621547246733132471685 28636241540108762462338441)
        ·
          refine ⟨21477181155081571846753831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28636241540108762462338441 21477181155081571846753831)
          ·
            refine ⟨32215771732622357770130747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21477181155081571846753831 32215771732622357770130747)
            ·
              refine ⟨48323657598933536655196121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32215771732622357770130747 48323657598933536655196121)
              ·
                refine ⟨36242743199200152491397091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48323657598933536655196121 36242743199200152491397091)
                ·
                  refine ⟨54364114798800228737095637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36242743199200152491397091 54364114798800228737095637)
                  ·
                    refine ⟨1274158940596880361025679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54364114798800228737095637 1274158940596880361025679)
                    ·
                      rfl

theorem cell23_7444247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_7444247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444247 prefixEnd_7444247 := by exact prefixLift 7444247
  have htrace : WordTrace (prefixWord ++ tailWord_7444247) baseStart_7444247 baseEnd_7444247 := by
    simpa [prefixWord, tailWord_7444247, baseEnd_7444247] using wordTrace_append hprefix tailTrace_7444247
  have hstable : (prefixWord ++ tailWord_7444247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444247).length < 2 ^ (prefixWord ++ tailWord_7444247).sum := by decide
  have hdescent : baseEnd_7444247 < baseStart_7444247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444281 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 2, 5]
def baseStart_7444281 : Nat := 118140960795 + 7444281 * 2 ^ 59
def prefixEnd_7444281 : Nat := 4983230072969 + 3 ^ 40 * 7444281 * 2
def baseEnd_7444281 : Nat := 1274164760044297983350627

theorem tailTrace_7444281 : CollatzResearch.WordTrace tailWord_7444281 prefixEnd_7444281 1274164760044297983350627 := by
  unfold tailWord_7444281
  simp only [CollatzResearch.WordTrace]
  refine ⟨271515233943648793820020697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181010155962432529213347131 271515233943648793820020697)
  ·
    refine ⟨203636425457736595365015523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271515233943648793820020697 203636425457736595365015523)
    ·
      refine ⟨305454638186604893047523285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203636425457736595365015523 305454638186604893047523285)
      ·
        refine ⟨7159093082498552180801327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 305454638186604893047523285 7159093082498552180801327)
        ·
          refine ⟨10738639623747828271201991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7159093082498552180801327 10738639623747828271201991)
          ·
            refine ⟨16107959435621742406802987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10738639623747828271201991 16107959435621742406802987)
            ·
              refine ⟨24161939153432613610204481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16107959435621742406802987 24161939153432613610204481)
              ·
                refine ⟨18121454365074460207653361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24161939153432613610204481 18121454365074460207653361)
                ·
                  refine ⟨13591090773805845155740021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18121454365074460207653361 13591090773805845155740021)
                  ·
                    refine ⟨1274164760044297983350627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13591090773805845155740021 1274164760044297983350627)
                    ·
                      rfl

theorem cell23_7444281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 5].length) (baseStart_7444281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444281 prefixEnd_7444281 := by exact prefixLift 7444281
  have htrace : WordTrace (prefixWord ++ tailWord_7444281) baseStart_7444281 baseEnd_7444281 := by
    simpa [prefixWord, tailWord_7444281, baseEnd_7444281] using wordTrace_append hprefix tailTrace_7444281
  have hstable : (prefixWord ++ tailWord_7444281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444281).length < 2 ^ (prefixWord ++ tailWord_7444281).sum := by decide
  have hdescent : baseEnd_7444281 < baseStart_7444281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444284 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 4, 4, 2]
def baseStart_7444284 : Nat := 118140960795 + 7444284 * 2 ^ 59
def prefixEnd_7444284 : Nat := 4983230072969 + 3 ^ 40 * 7444284 * 2
def baseEnd_7444284 : Nat := 3822495820574857438314367

theorem tailTrace_7444284 : CollatzResearch.WordTrace tailWord_7444284 prefixEnd_7444284 3822495820574857438314367 := by
  unfold tailWord_7444284
  simp only [CollatzResearch.WordTrace]
  refine ⟨135757671681318962666189953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181010228908425283554919937 135757671681318962666189953)
  ·
    refine ⟨101818253760989221999642465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135757671681318962666189953 101818253760989221999642465)
    ·
      refine ⟨76363690320741916499731849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101818253760989221999642465 76363690320741916499731849)
      ·
        refine ⟨57272767740556437374798887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76363690320741916499731849 57272767740556437374798887)
        ·
          refine ⟨85909151610834656062198331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57272767740556437374798887 85909151610834656062198331)
          ·
            refine ⟨128863727416251984093297497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85909151610834656062198331 128863727416251984093297497)
            ·
              refine ⟨96647795562188988069973123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128863727416251984093297497 96647795562188988069973123)
              ·
                refine ⟨144971693343283482104959685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96647795562188988069973123 144971693343283482104959685)
                ·
                  refine ⟨27182192501865652894679941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144971693343283482104959685 27182192501865652894679941)
                  ·
                    refine ⟨5096661094099809917752489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27182192501865652894679941 5096661094099809917752489)
                    ·
                      refine ⟨3822495820574857438314367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096661094099809917752489 3822495820574857438314367)
                      ·
                        rfl

theorem cell23_7444284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_7444284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444284 prefixEnd_7444284 := by exact prefixLift 7444284
  have htrace : WordTrace (prefixWord ++ tailWord_7444284) baseStart_7444284 baseEnd_7444284 := by
    simpa [prefixWord, tailWord_7444284, baseEnd_7444284] using wordTrace_append hprefix tailTrace_7444284
  have hstable : (prefixWord ++ tailWord_7444284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444284).length < 2 ^ (prefixWord ++ tailWord_7444284).sum := by decide
  have hdescent : baseEnd_7444284 < baseStart_7444284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444378 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2]
def baseStart_7444378 : Nat := 118140960795 + 7444378 * 2 ^ 59
def prefixEnd_7444378 : Nat := 4983230072969 + 3 ^ 40 * 7444378 * 2
def baseEnd_7444378 : Nat := 3822544087756380070538935

theorem tailTrace_7444378 : CollatzResearch.WordTrace tailWord_7444378 prefixEnd_7444378 3822544087756380070538935 := by
  unfold tailWord_7444378
  simp only [CollatzResearch.WordTrace]
  refine ⟨67879692956074344846575447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181012514549531586257534525 67879692956074344846575447)
  ·
    refine ⟨101819539434111517269863171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67879692956074344846575447 101819539434111517269863171)
    ·
      refine ⟨152729309151167275904794757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101819539434111517269863171 152729309151167275904794757)
      ·
        refine ⟨28636745465843864232149017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152729309151167275904794757 28636745465843864232149017)
        ·
          refine ⟨21477559099382898174111763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28636745465843864232149017 21477559099382898174111763)
          ·
            refine ⟨32216338649074347261167645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21477559099382898174111763 32216338649074347261167645)
            ·
              refine ⟨12081126993402880222937867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32216338649074347261167645 12081126993402880222937867)
              ·
                refine ⟨18121690490104320334406801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12081126993402880222937867 18121690490104320334406801)
                ·
                  refine ⟨13591267867578240250805101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18121690490104320334406801 13591267867578240250805101)
                  ·
                    refine ⟨5096725450341840094051913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13591267867578240250805101 5096725450341840094051913)
                    ·
                      refine ⟨3822544087756380070538935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096725450341840094051913 3822544087756380070538935)
                      ·
                        rfl

theorem cell23_7444378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_7444378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444378 prefixEnd_7444378 := by exact prefixLift 7444378
  have htrace : WordTrace (prefixWord ++ tailWord_7444378) baseStart_7444378 baseEnd_7444378 := by
    simpa [prefixWord, tailWord_7444378, baseEnd_7444378] using wordTrace_append hprefix tailTrace_7444378
  have hstable : (prefixWord ++ tailWord_7444378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444378).length < 2 ^ (prefixWord ++ tailWord_7444378).sum := by decide
  have hdescent : baseEnd_7444378 < baseStart_7444378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444384 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 4, 4]
def baseStart_7444384 : Nat := 118140960795 + 7444384 * 2 ^ 59
def prefixEnd_7444384 : Nat := 4983230072969 + 3 ^ 40 * 7444384 * 2
def baseEnd_7444384 : Nat := 1274182389546769015687969

theorem tailTrace_7444384 : CollatzResearch.WordTrace tailWord_7444384 prefixEnd_7444384 1274182389546769015687969 := by
  unfold tailWord_7444384
  simp only [CollatzResearch.WordTrace]
  refine ⟨135759495331137821205510103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181012660441517094940680137 135759495331137821205510103)
  ·
    refine ⟨203639242996706731808265155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135759495331137821205510103 203639242996706731808265155)
    ·
      refine ⟨305458864495060097712397733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203639242996706731808265155 305458864495060097712397733)
      ·
        refine ⟨57273537092823768321074575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305458864495060097712397733 57273537092823768321074575)
        ·
          refine ⟨85910305639235652481611863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57273537092823768321074575 85910305639235652481611863)
          ·
            refine ⟨128865458458853478722417795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85910305639235652481611863 128865458458853478722417795)
            ·
              refine ⟨193298187688280218083626693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128865458458853478722417795 193298187688280218083626693)
              ·
                refine ⟨36243410191552540890680005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193298187688280218083626693 36243410191552540890680005)
                ·
                  refine ⟨6795639410916101417002501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36243410191552540890680005 6795639410916101417002501)
                  ·
                    refine ⟨1274182389546769015687969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6795639410916101417002501 1274182389546769015687969)
                    ·
                      rfl

theorem cell23_7444384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4, 4].length) (baseStart_7444384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444384 prefixEnd_7444384 := by exact prefixLift 7444384
  have htrace : WordTrace (prefixWord ++ tailWord_7444384) baseStart_7444384 baseEnd_7444384 := by
    simpa [prefixWord, tailWord_7444384, baseEnd_7444384] using wordTrace_append hprefix tailTrace_7444384
  have hstable : (prefixWord ++ tailWord_7444384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444384).length < 2 ^ (prefixWord ++ tailWord_7444384).sum := by decide
  have hdescent : baseEnd_7444384 < baseStart_7444384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444387 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 6]
def baseStart_7444387 : Nat := 118140960795 + 7444387 * 2 ^ 59
def prefixEnd_7444387 : Nat := 4983230072969 + 3 ^ 40 * 7444387 * 2
def baseEnd_7444387 : Nat := 3822548709082270535326393

theorem tailTrace_7444387 : CollatzResearch.WordTrace tailWord_7444387 prefixEnd_7444387 3822548709082270535326393 := by
  unfold tailWord_7444387
  simp only [CollatzResearch.WordTrace]
  refine ⟨271519100081264773923379415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181012733387509849282252943 271519100081264773923379415)
  ·
    refine ⟨407278650121897160885069123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271519100081264773923379415 407278650121897160885069123)
    ·
      refine ⟨610917975182845741327603685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407278650121897160885069123 610917975182845741327603685)
      ·
        refine ⟨114547120346783576498925691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 610917975182845741327603685 114547120346783576498925691)
        ·
          refine ⟨171820680520175364748388537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114547120346783576498925691 171820680520175364748388537)
          ·
            refine ⟨128865510390131523561291403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171820680520175364748388537 128865510390131523561291403)
            ·
              refine ⟨193298265585197285341937105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128865510390131523561291403 193298265585197285341937105)
              ·
                refine ⟨144973699188897964006452829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193298265585197285341937105 144973699188897964006452829)
                ·
                  refine ⟨54365137195836736502419811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144973699188897964006452829 54365137195836736502419811)
                  ·
                    refine ⟨81547705793755104753629717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54365137195836736502419811 81547705793755104753629717)
                    ·
                      refine ⟨3822548709082270535326393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81547705793755104753629717 3822548709082270535326393)
                      ·
                        rfl

theorem cell23_7444387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_7444387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444387 prefixEnd_7444387 := by exact prefixLift 7444387
  have htrace : WordTrace (prefixWord ++ tailWord_7444387) baseStart_7444387 baseEnd_7444387 := by
    simpa [prefixWord, tailWord_7444387, baseEnd_7444387] using wordTrace_append hprefix tailTrace_7444387
  have hstable : (prefixWord ++ tailWord_7444387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444387).length < 2 ^ (prefixWord ++ tailWord_7444387).sum := by decide
  have hdescent : baseEnd_7444387 < baseStart_7444387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444388 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_7444388 : Nat := 118140960795 + 7444388 * 2 ^ 59
def prefixEnd_7444388 : Nat := 4983230072969 + 3 ^ 40 * 7444388 * 2
def baseEnd_7444388 : Nat := 1274183074187641677137963

theorem tailTrace_7444388 : CollatzResearch.WordTrace tailWord_7444388 prefixEnd_7444388 1274183074187641677137963 := by
  unfold tailWord_7444388
  simp only [CollatzResearch.WordTrace]
  refine ⟨135759568277130575547082909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181012757702840767396110545 135759568277130575547082909)
  ·
    refine ⟨50909838103923965830156091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135759568277130575547082909 50909838103923965830156091)
    ·
      refine ⟨76364757155885948745234137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50909838103923965830156091 76364757155885948745234137)
      ·
        refine ⟨57273567866914461558925603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76364757155885948745234137 57273567866914461558925603)
        ·
          refine ⟨85910351800371692338388405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57273567866914461558925603 85910351800371692338388405)
          ·
            refine ⟨8054095481284846156723913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85910351800371692338388405 8054095481284846156723913)
            ·
              refine ⟨6040571610963634617542935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8054095481284846156723913 6040571610963634617542935)
              ·
                refine ⟨9060857416445451926314403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040571610963634617542935 9060857416445451926314403)
                ·
                  refine ⟨13591286124668177889471605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9060857416445451926314403 13591286124668177889471605)
                  ·
                    refine ⟨1274183074187641677137963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13591286124668177889471605 1274183074187641677137963)
                    ·
                      rfl

theorem cell23_7444388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_7444388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444388 prefixEnd_7444388 := by exact prefixLift 7444388
  have htrace : WordTrace (prefixWord ++ tailWord_7444388) baseStart_7444388 baseEnd_7444388 := by
    simpa [prefixWord, tailWord_7444388, baseEnd_7444388] using wordTrace_append hprefix tailTrace_7444388
  have hstable : (prefixWord ++ tailWord_7444388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444388).length < 2 ^ (prefixWord ++ tailWord_7444388).sum := by decide
  have hdescent : baseEnd_7444388 < baseStart_7444388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444401 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 4, 4]
def baseStart_7444401 : Nat := 118140960795 + 7444401 * 2 ^ 59
def prefixEnd_7444401 : Nat := 4983230072969 + 3 ^ 40 * 7444401 * 2
def baseEnd_7444401 : Nat := 1274185299270477826850443

theorem tailTrace_7444401 : CollatzResearch.WordTrace tailWord_7444401 prefixEnd_7444401 1274185299270477826850443 := by
  unfold tailWord_7444401
  simp only [CollatzResearch.WordTrace]
  refine ⟨271519610703214054314389057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181013073802142702876259371 271519610703214054314389057)
  ·
    refine ⟨203639708027410540735791793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271519610703214054314389057 203639708027410540735791793)
    ·
      refine ⟨152729781020557905551843845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203639708027410540735791793 152729781020557905551843845)
      ·
        refine ⟨28636833941354607290970721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152729781020557905551843845 28636833941354607290970721)
        ·
          refine ⟨21477625456015955468228041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28636833941354607290970721 21477625456015955468228041)
          ·
            refine ⟨16108219092011966601171031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21477625456015955468228041 16108219092011966601171031)
            ·
              refine ⟨24162328638017949901756547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16108219092011966601171031 24162328638017949901756547)
              ·
                refine ⟨36243492957026924852634821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24162328638017949901756547 36243492957026924852634821)
                ·
                  refine ⟨6795654929442548409869029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36243492957026924852634821 6795654929442548409869029)
                  ·
                    refine ⟨1274185299270477826850443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6795654929442548409869029 1274185299270477826850443)
                    ·
                      rfl

theorem cell23_7444401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_7444401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444401 prefixEnd_7444401 := by exact prefixLift 7444401
  have htrace : WordTrace (prefixWord ++ tailWord_7444401) baseStart_7444401 baseEnd_7444401 := by
    simpa [prefixWord, tailWord_7444401, baseEnd_7444401] using wordTrace_append hprefix tailTrace_7444401
  have hstable : (prefixWord ++ tailWord_7444401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444401).length < 2 ^ (prefixWord ++ tailWord_7444401).sum := by decide
  have hdescent : baseEnd_7444401 < baseStart_7444401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444407 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_7444407 : Nat := 118140960795 + 7444407 * 2 ^ 59
def prefixEnd_7444407 : Nat := 4983230072969 + 3 ^ 40 * 7444407 * 2
def baseEnd_7444407 : Nat := 3822558978695360457076301

theorem tailTrace_7444407 : CollatzResearch.WordTrace tailWord_7444407 prefixEnd_7444407 3822558978695360457076301 := by
  unfold tailWord_7444407
  simp only [CollatzResearch.WordTrace]
  refine ⟨271519829541192317339107475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181013219694128211559404983 271519829541192317339107475)
  ·
    refine ⟨407279744311788476008661213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271519829541192317339107475 407279744311788476008661213)
    ·
      refine ⟨152729904116920678503247955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407279744311788476008661213 152729904116920678503247955)
      ·
        refine ⟨229094856175381017754871933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152729904116920678503247955 229094856175381017754871933)
        ·
          refine ⟨85910571065767881658076975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229094856175381017754871933 85910571065767881658076975)
          ·
            refine ⟨128865856598651822487115463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85910571065767881658076975 128865856598651822487115463)
            ·
              refine ⟨193298784897977733730673195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128865856598651822487115463 193298784897977733730673195)
              ·
                refine ⟨289948177346966600596009793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193298784897977733730673195 289948177346966600596009793)
                ·
                  refine ⟨217461133010224950447007345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289948177346966600596009793 217461133010224950447007345)
                  ·
                    refine ⟨163095849757668712835255509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217461133010224950447007345 163095849757668712835255509)
                    ·
                      refine ⟨3822558978695360457076301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163095849757668712835255509 3822558978695360457076301)
                      ·
                        rfl

theorem cell23_7444407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_7444407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444407 prefixEnd_7444407 := by exact prefixLift 7444407
  have htrace : WordTrace (prefixWord ++ tailWord_7444407) baseStart_7444407 baseEnd_7444407 := by
    simpa [prefixWord, tailWord_7444407, baseEnd_7444407] using wordTrace_append hprefix tailTrace_7444407
  have hstable : (prefixWord ++ tailWord_7444407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444407).length < 2 ^ (prefixWord ++ tailWord_7444407).sum := by decide
  have hdescent : baseEnd_7444407 < baseStart_7444407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444408 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 3, 2, 2]
def baseStart_7444408 : Nat := 118140960795 + 7444408 * 2 ^ 59
def prefixEnd_7444408 : Nat := 4983230072969 + 3 ^ 40 * 7444408 * 2
def baseEnd_7444408 : Nat := 3822559492176014953163797

theorem tailTrace_7444408 : CollatzResearch.WordTrace tailWord_7444408 prefixEnd_7444408 3822559492176014953163797 := by
  unfold tailWord_7444408
  simp only [CollatzResearch.WordTrace]
  refine ⟨135759933007094347254946939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181013244009459129673262585 135759933007094347254946939)
  ·
    refine ⟨203639899510641520882420409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135759933007094347254946939 203639899510641520882420409)
    ·
      refine ⟨152729924632981140661815307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203639899510641520882420409 152729924632981140661815307)
      ·
        refine ⟨229094886949471710992722961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152729924632981140661815307 229094886949471710992722961)
        ·
          refine ⟨171821165212103783244542221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229094886949471710992722961 171821165212103783244542221)
          ·
            refine ⟨64432936954538918716703333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171821165212103783244542221 64432936954538918716703333)
            ·
              refine ⟨12081175678976047259381875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64432936954538918716703333 12081175678976047259381875)
              ·
                refine ⟨18121763518464070889072813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12081175678976047259381875 18121763518464070889072813)
                ·
                  refine ⟨6795661319424026583402305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18121763518464070889072813 6795661319424026583402305)
                  ·
                    refine ⟨5096745989568019937551729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795661319424026583402305 5096745989568019937551729)
                    ·
                      refine ⟨3822559492176014953163797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096745989568019937551729 3822559492176014953163797)
                      ·
                        rfl

theorem cell23_7444408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3, 2, 2].length) (baseStart_7444408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444408 prefixEnd_7444408 := by exact prefixLift 7444408
  have htrace : WordTrace (prefixWord ++ tailWord_7444408) baseStart_7444408 baseEnd_7444408 := by
    simpa [prefixWord, tailWord_7444408, baseEnd_7444408] using wordTrace_append hprefix tailTrace_7444408
  have hstable : (prefixWord ++ tailWord_7444408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444408).length < 2 ^ (prefixWord ++ tailWord_7444408).sum := by decide
  have hdescent : baseEnd_7444408 < baseStart_7444408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444428 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 1, 2, 3]
def baseStart_7444428 : Nat := 118140960795 + 7444428 * 2 ^ 59
def prefixEnd_7444428 : Nat := 4983230072969 + 3 ^ 40 * 7444428 * 2
def baseEnd_7444428 : Nat := 3822569761789104874913705

theorem tailTrace_7444428 : CollatzResearch.WordTrace tailWord_7444428 prefixEnd_7444428 3822569761789104874913705 := by
  unfold tailWord_7444428
  simp only [CollatzResearch.WordTrace]
  refine ⟨135760297737058118962810969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181013730316077491950414625 135760297737058118962810969)
  ·
    refine ⟨101820223302793589222108227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135760297737058118962810969 101820223302793589222108227)
    ·
      refine ⟨152730334954190383833162341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101820223302793589222108227 152730334954190383833162341)
      ·
        refine ⟨28636937803910696968717939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152730334954190383833162341 28636937803910696968717939)
        ·
          refine ⟨42955406705866045453076909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28636937803910696968717939 42955406705866045453076909)
          ·
            refine ⟨16108277514699767044903841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42955406705866045453076909 16108277514699767044903841)
            ·
              refine ⟨12081208136024825283677881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16108277514699767044903841 12081208136024825283677881)
              ·
                refine ⟨9060906102018618962758411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12081208136024825283677881 9060906102018618962758411)
                ·
                  refine ⟨13591359153027928444137617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9060906102018618962758411 13591359153027928444137617)
                  ·
                    refine ⟨10193519364770946333103213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13591359153027928444137617 10193519364770946333103213)
                    ·
                      refine ⟨3822569761789104874913705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10193519364770946333103213 3822569761789104874913705)
                      ·
                        rfl

theorem cell23_7444428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_7444428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444428 prefixEnd_7444428 := by exact prefixLift 7444428
  have htrace : WordTrace (prefixWord ++ tailWord_7444428) baseStart_7444428 baseEnd_7444428 := by
    simpa [prefixWord, tailWord_7444428, baseEnd_7444428] using wordTrace_append hprefix tailTrace_7444428
  have hstable : (prefixWord ++ tailWord_7444428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444428).length < 2 ^ (prefixWord ++ tailWord_7444428).sum := by decide
  have hdescent : baseEnd_7444428 < baseStart_7444428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444458 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_7444458 : Nat := 118140960795 + 7444458 * 2 ^ 59
def prefixEnd_7444458 : Nat := 4983230072969 + 3 ^ 40 * 7444458 * 2
def baseEnd_7444458 : Nat := 3822585166208739757538567

theorem tailTrace_7444458 : CollatzResearch.WordTrace tailWord_7444458 prefixEnd_7444458 3822585166208739757538567 := by
  unfold tailWord_7444458
  simp only [CollatzResearch.WordTrace]
  refine ⟨67880422416001888262303507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181014459776005035366142685 67880422416001888262303507)
  ·
    refine ⟨101820633624002832393455261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67880422416001888262303507 101820633624002832393455261)
    ·
      refine ⟨38182737609001062147545723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101820633624002832393455261 38182737609001062147545723)
      ·
        refine ⟨57274106413501593221318585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38182737609001062147545723 57274106413501593221318585)
        ·
          refine ⟨42955579810126194915988939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57274106413501593221318585 42955579810126194915988939)
          ·
            refine ⟨64433369715189292373983409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42955579810126194915988939 64433369715189292373983409)
            ·
              refine ⟨48325027286391969280487557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64433369715189292373983409 48325027286391969280487557)
              ·
                refine ⟨9060942616198494240091417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48325027286391969280487557 9060942616198494240091417)
                ·
                  refine ⟨6795706962148870680068563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9060942616198494240091417 6795706962148870680068563)
                  ·
                    refine ⟨10193560443223306020102845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6795706962148870680068563 10193560443223306020102845)
                    ·
                      refine ⟨3822585166208739757538567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10193560443223306020102845 3822585166208739757538567)
                      ·
                        rfl

theorem cell23_7444458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_7444458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444458 prefixEnd_7444458 := by exact prefixLift 7444458
  have htrace : WordTrace (prefixWord ++ tailWord_7444458) baseStart_7444458 baseEnd_7444458 := by
    simpa [prefixWord, tailWord_7444458, baseEnd_7444458] using wordTrace_append hprefix tailTrace_7444458
  have hstable : (prefixWord ++ tailWord_7444458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444458).length < 2 ^ (prefixWord ++ tailWord_7444458).sum := by decide
  have hdescent : baseEnd_7444458 < baseStart_7444458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444485 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 1, 3, 2]
def baseStart_7444485 : Nat := 118140960795 + 7444485 * 2 ^ 59
def prefixEnd_7444485 : Nat := 4983230072969 + 3 ^ 40 * 7444485 * 2
def baseEnd_7444485 : Nat := 3822599030186411151900943

theorem tailTrace_7444485 : CollatzResearch.WordTrace tailWord_7444485 prefixEnd_7444485 3822599030186411151900943 := by
  unfold tailWord_7444485
  simp only [CollatzResearch.WordTrace]
  refine ⟨271522674434909736660446909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181015116289939824440297939 271522674434909736660446909)
  ·
    refine ⟨101821002913091151247667591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271522674434909736660446909 101821002913091151247667591)
    ·
      refine ⟨152731504369636726871501387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101821002913091151247667591 152731504369636726871501387)
      ·
        refine ⟨229097256554455090307252081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152731504369636726871501387 229097256554455090307252081)
        ·
          refine ⟨171822942415841317730439061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229097256554455090307252081 171822942415841317730439061)
          ·
            refine ⟨8054200425742561768614331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171822942415841317730439061 8054200425742561768614331)
            ·
              refine ⟨12081300638613842652921497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8054200425742561768614331 12081300638613842652921497)
              ·
                refine ⟨9060975478960381989691123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12081300638613842652921497 9060975478960381989691123)
                ·
                  refine ⟨13591463218440572984536685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9060975478960381989691123 13591463218440572984536685)
                  ·
                    refine ⟨5096798706915214869201257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13591463218440572984536685 5096798706915214869201257)
                    ·
                      refine ⟨3822599030186411151900943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096798706915214869201257 3822599030186411151900943)
                      ·
                        rfl

theorem cell23_7444485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 3, 2].length) (baseStart_7444485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444485 prefixEnd_7444485 := by exact prefixLift 7444485
  have htrace : WordTrace (prefixWord ++ tailWord_7444485) baseStart_7444485 baseEnd_7444485 := by
    simpa [prefixWord, tailWord_7444485, baseEnd_7444485] using wordTrace_append hprefix tailTrace_7444485
  have hstable : (prefixWord ++ tailWord_7444485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444485).length < 2 ^ (prefixWord ++ tailWord_7444485).sum := by decide
  have hdescent : baseEnd_7444485 < baseStart_7444485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444515 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 2, 2, 2]
def baseStart_7444515 : Nat := 118140960795 + 7444515 * 2 ^ 59
def prefixEnd_7444515 : Nat := 4983230072969 + 3 ^ 40 * 7444515 * 2
def baseEnd_7444515 : Nat := 3822614434606046034525805

theorem tailTrace_7444515 : CollatzResearch.WordTrace tailWord_7444515 prefixEnd_7444515 3822614434606046034525805 := by
  unfold tailWord_7444515
  simp only [CollatzResearch.WordTrace]
  refine ⟨271523768624801051784038999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181015845749867367856025999 271523768624801051784038999)
  ·
    refine ⟨407285652937201577676058499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271523768624801051784038999 407285652937201577676058499)
    ·
      refine ⟨610928479405802366514087749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407285652937201577676058499 610928479405802366514087749)
      ·
        refine ⟨114549089888587943721391453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 610928479405802366514087749 114549089888587943721391453)
        ·
          refine ⟨42955908708220478895521795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114549089888587943721391453 42955908708220478895521795)
          ·
            refine ⟨64433863062330718343282693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42955908708220478895521795 64433863062330718343282693)
            ·
              refine ⟨12081349324187009689365505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64433863062330718343282693 12081349324187009689365505)
              ·
                refine ⟨9061011993140257267024129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12081349324187009689365505 9061011993140257267024129)
                ·
                  refine ⟨6795758994855192950268097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9061011993140257267024129 6795758994855192950268097)
                  ·
                    refine ⟨5096819246141394712701073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795758994855192950268097 5096819246141394712701073)
                    ·
                      refine ⟨3822614434606046034525805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096819246141394712701073 3822614434606046034525805)
                      ·
                        rfl

theorem cell23_7444515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_7444515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444515 prefixEnd_7444515 := by exact prefixLift 7444515
  have htrace : WordTrace (prefixWord ++ tailWord_7444515) baseStart_7444515 baseEnd_7444515 := by
    simpa [prefixWord, tailWord_7444515, baseEnd_7444515] using wordTrace_append hprefix tailTrace_7444515
  have hstable : (prefixWord ++ tailWord_7444515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444515).length < 2 ^ (prefixWord ++ tailWord_7444515).sum := by decide
  have hdescent : baseEnd_7444515 < baseStart_7444515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444532 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_7444532 : Nat := 118140960795 + 7444532 * 2 ^ 59
def prefixEnd_7444532 : Nat := 4983230072969 + 3 ^ 40 * 7444532 * 2
def baseEnd_7444532 : Nat := 3822623163777172468013227

theorem tailTrace_7444532 : CollatzResearch.WordTrace tailWord_7444532 prefixEnd_7444532 3822623163777172468013227 := by
  unfold tailWord_7444532
  simp only [CollatzResearch.WordTrace]
  refine ⟨135762194332869731843703925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181016259110492975791605233 135762194332869731843703925)
  ·
    refine ⟨12727705718706537360347243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135762194332869731843703925 12727705718706537360347243)
    ·
      refine ⟨19091558578059806040520865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12727705718706537360347243 19091558578059806040520865)
      ·
        refine ⟨14318668933544854530390649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19091558578059806040520865 14318668933544854530390649)
        ·
          refine ⟨10739001700158640897792987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14318668933544854530390649 10739001700158640897792987)
          ·
            refine ⟨16108502550237961346689481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10739001700158640897792987 16108502550237961346689481)
            ·
              refine ⟨12081376912678471010017111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16108502550237961346689481 12081376912678471010017111)
              ·
                refine ⟨18122065369017706515025667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12081376912678471010017111 18122065369017706515025667)
                ·
                  refine ⟨27183098053526559772538501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18122065369017706515025667 27183098053526559772538501)
                  ·
                    refine ⟨5096830885036229957350969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27183098053526559772538501 5096830885036229957350969)
                    ·
                      refine ⟨3822623163777172468013227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096830885036229957350969 3822623163777172468013227)
                      ·
                        rfl

theorem cell23_7444532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_7444532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444532 prefixEnd_7444532 := by exact prefixLift 7444532
  have htrace : WordTrace (prefixWord ++ tailWord_7444532) baseStart_7444532 baseEnd_7444532 := by
    simpa [prefixWord, tailWord_7444532, baseEnd_7444532] using wordTrace_append hprefix tailTrace_7444532
  have hstable : (prefixWord ++ tailWord_7444532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444532).length < 2 ^ (prefixWord ++ tailWord_7444532).sum := by decide
  have hdescent : baseEnd_7444532 < baseStart_7444532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444566 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_7444566 : Nat := 118140960795 + 7444566 * 2 ^ 59
def prefixEnd_7444566 : Nat := 4983230072969 + 3 ^ 40 * 7444566 * 2
def baseEnd_7444566 : Nat := 3822640622119425334988071

theorem tailTrace_7444566 : CollatzResearch.WordTrace tailWord_7444566 prefixEnd_7444566 3822640622119425334988071 := by
  unfold tailWord_7444566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16970351796726017968384097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181017085831744191662763701 16970351796726017968384097)
  ·
    refine ⟨12727763847544513476288073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16970351796726017968384097 12727763847544513476288073)
    ·
      refine ⟨9545822885658385107216055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12727763847544513476288073 9545822885658385107216055)
      ·
        refine ⟨14318734328487577660824083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9545822885658385107216055 14318734328487577660824083)
        ·
          refine ⟨21478101492731366491236125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14318734328487577660824083 21478101492731366491236125)
          ·
            refine ⟨8054288059774262434213547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21478101492731366491236125 8054288059774262434213547)
            ·
              refine ⟨12081432089661393651320321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8054288059774262434213547 12081432089661393651320321)
              ·
                refine ⟨9061074067246045238490241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12081432089661393651320321 9061074067246045238490241)
                ·
                  refine ⟨6795805550434533928867681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9061074067246045238490241 6795805550434533928867681)
                  ·
                    refine ⟨5096854162825900446650761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795805550434533928867681 5096854162825900446650761)
                    ·
                      refine ⟨3822640622119425334988071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096854162825900446650761 3822640622119425334988071)
                      ·
                        rfl

theorem cell23_7444566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_7444566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444566 prefixEnd_7444566 := by exact prefixLift 7444566
  have htrace : WordTrace (prefixWord ++ tailWord_7444566) baseStart_7444566 baseEnd_7444566 := by
    simpa [prefixWord, tailWord_7444566, baseEnd_7444566] using wordTrace_append hprefix tailTrace_7444566
  have hstable : (prefixWord ++ tailWord_7444566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444566).length < 2 ^ (prefixWord ++ tailWord_7444566).sum := by decide
  have hdescent : baseEnd_7444566 < baseStart_7444566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444588 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 2, 4, 2]
def baseStart_7444588 : Nat := 118140960795 + 7444588 * 2 ^ 59
def prefixEnd_7444588 : Nat := 4983230072969 + 3 ^ 40 * 7444588 * 2
def baseEnd_7444588 : Nat := 3822651918693824248912969

theorem tailTrace_7444588 : CollatzResearch.WordTrace tailWord_7444588 prefixEnd_7444588 3822651918693824248912969 := by
  unfold tailWord_7444588
  simp only [CollatzResearch.WordTrace]
  refine ⟨135763215576768292625723209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181017620769024390167630945 135763215576768292625723209)
  ·
    refine ⟨101822411682576219469292407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135763215576768292625723209 101822411682576219469292407)
    ·
      refine ⟨152733617523864329203938611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101822411682576219469292407 152733617523864329203938611)
      ·
        refine ⟨229100426285796493805907917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152733617523864329203938611 229100426285796493805907917)
        ·
          refine ⟨85912659857173685177215469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229100426285796493805907917 85912659857173685177215469)
          ·
            refine ⟨32217247446440131941455801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85912659857173685177215469 32217247446440131941455801)
            ·
              refine ⟨24162935584830098956091851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32217247446440131941455801 24162935584830098956091851)
              ·
                refine ⟨36244403377245148434137777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24162935584830098956091851 36244403377245148434137777)
                ·
                  refine ⟨27183302532933861325603333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36244403377245148434137777 27183302532933861325603333)
                  ·
                    refine ⟨5096869224925098998550625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27183302532933861325603333 5096869224925098998550625)
                    ·
                      refine ⟨3822651918693824248912969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096869224925098998550625 3822651918693824248912969)
                      ·
                        rfl

theorem cell23_7444588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 4, 2].length) (baseStart_7444588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444588 prefixEnd_7444588 := by exact prefixLift 7444588
  have htrace : WordTrace (prefixWord ++ tailWord_7444588) baseStart_7444588 baseEnd_7444588 := by
    simpa [prefixWord, tailWord_7444588, baseEnd_7444588] using wordTrace_append hprefix tailTrace_7444588
  have hstable : (prefixWord ++ tailWord_7444588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444588).length < 2 ^ (prefixWord ++ tailWord_7444588).sum := by decide
  have hdescent : baseEnd_7444588 < baseStart_7444588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444591 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 3]
def baseStart_7444591 : Nat := 118140960795 + 7444591 * 2 ^ 59
def prefixEnd_7444591 : Nat := 4983230072969 + 3 ^ 40 * 7444591 * 2
def baseEnd_7444591 : Nat := 3822653459135787737175455

theorem tailTrace_7444591 : CollatzResearch.WordTrace tailWord_7444591 prefixEnd_7444591 3822653459135787737175455 := by
  unfold tailWord_7444591
  simp only [CollatzResearch.WordTrace]
  refine ⟨271526540572525716763805627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181017693715017144509203751 271526540572525716763805627)
  ·
    refine ⟨407289810858788575145708441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271526540572525716763805627 407289810858788575145708441)
    ·
      refine ⟨305467358144091431359281331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407289810858788575145708441 305467358144091431359281331)
      ·
        refine ⟨458201037216137147038921997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305467358144091431359281331 458201037216137147038921997)
        ·
          refine ⟨171825388956051430139595749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458201037216137147038921997 171825388956051430139595749)
          ·
            refine ⟨32217260429259643151174203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171825388956051430139595749 32217260429259643151174203)
            ·
              refine ⟨48325890643889464726761305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32217260429259643151174203 48325890643889464726761305)
              ·
                refine ⟨36244417982917098545070979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48325890643889464726761305 36244417982917098545070979)
                ·
                  refine ⟨54366626974375647817606469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36244417982917098545070979 54366626974375647817606469)
                  ·
                    refine ⟨10193742557695433965801213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54366626974375647817606469 10193742557695433965801213)
                    ·
                      refine ⟨3822653459135787737175455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10193742557695433965801213 3822653459135787737175455)
                      ·
                        rfl

theorem cell23_7444591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 3].length) (baseStart_7444591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444591 prefixEnd_7444591 := by exact prefixLift 7444591
  have htrace : WordTrace (prefixWord ++ tailWord_7444591) baseStart_7444591 baseEnd_7444591 := by
    simpa [prefixWord, tailWord_7444591, baseEnd_7444591] using wordTrace_append hprefix tailTrace_7444591
  have hstable : (prefixWord ++ tailWord_7444591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444591).length < 2 ^ (prefixWord ++ tailWord_7444591).sum := by decide
  have hdescent : baseEnd_7444591 < baseStart_7444591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444615 : List Nat := [1, 1, 4, 2, 1, 1, 5, 3, 1, 4]
def baseStart_7444615 : Nat := 118140960795 + 7444615 * 2 ^ 59
def prefixEnd_7444615 : Nat := 4983230072969 + 3 ^ 40 * 7444615 * 2
def baseEnd_7444615 : Nat := 1274221927557165214425115

theorem tailTrace_7444615 : CollatzResearch.WordTrace tailWord_7444615 prefixEnd_7444615 1274221927557165214425115 := by
  unfold tailWord_7444615
  simp only [CollatzResearch.WordTrace]
  refine ⟨271527415924438768862679299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181018277282959179241786199 271527415924438768862679299)
  ·
    refine ⟨407291123886658153294018949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271527415924438768862679299 407291123886658153294018949)
    ·
      refine ⟨76367085728748403742628553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407291123886658153294018949 76367085728748403742628553)
      ·
        refine ⟨57275314296561302806971415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76367085728748403742628553 57275314296561302806971415)
        ·
          refine ⟨85912971444841954210457123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57275314296561302806971415 85912971444841954210457123)
          ·
            refine ⟨128869457167262931315685685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85912971444841954210457123 128869457167262931315685685)
            ·
              refine ⟨12081511609430899810845533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128869457167262931315685685 12081511609430899810845533)
              ·
                refine ⟨4530566853536587429067075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12081511609430899810845533 4530566853536587429067075)
                ·
                  refine ⟨6795850280304881143600613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530566853536587429067075 6795850280304881143600613)
                  ·
                    refine ⟨1274221927557165214425115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6795850280304881143600613 1274221927557165214425115)
                    ·
                      rfl

theorem cell23_7444615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_7444615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444615 prefixEnd_7444615 := by exact prefixLift 7444615
  have htrace : WordTrace (prefixWord ++ tailWord_7444615) baseStart_7444615 baseEnd_7444615 := by
    simpa [prefixWord, tailWord_7444615, baseEnd_7444615] using wordTrace_append hprefix tailTrace_7444615
  have hstable : (prefixWord ++ tailWord_7444615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444615).length < 2 ^ (prefixWord ++ tailWord_7444615).sum := by decide
  have hdescent : baseEnd_7444615 < baseStart_7444615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444632 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 3, 4]
def baseStart_7444632 : Nat := 118140960795 + 7444632 * 2 ^ 59
def prefixEnd_7444632 : Nat := 4983230072969 + 3 ^ 40 * 7444632 * 2
def baseEnd_7444632 : Nat := 1274224837280874025587589

theorem tailTrace_7444632 : CollatzResearch.WordTrace tailWord_7444632 prefixEnd_7444632 1274224837280874025587589 := by
  unfold tailWord_7444632
  simp only [CollatzResearch.WordTrace]
  refine ⟨135764017982688590383024075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181018690643584787177365433 135764017982688590383024075)
  ·
    refine ⟨203646026974032885574536113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135764017982688590383024075 203646026974032885574536113)
    ·
      refine ⟨152734520230524664180902085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203646026974032885574536113 152734520230524664180902085)
      ·
        refine ⟨28637722543223374533919141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152734520230524664180902085 28637722543223374533919141)
        ·
          refine ⟨5369572976854382725109839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28637722543223374533919141 5369572976854382725109839)
          ·
            refine ⟨8054359465281574087664759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5369572976854382725109839 8054359465281574087664759)
            ·
              refine ⟨12081539197922361131497139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8054359465281574087664759 12081539197922361131497139)
              ·
                refine ⟨18122308796883541697245709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12081539197922361131497139 18122308796883541697245709)
                ·
                  refine ⟨6795865798831328136467141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18122308796883541697245709 6795865798831328136467141)
                  ·
                    refine ⟨1274224837280874025587589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6795865798831328136467141 1274224837280874025587589)
                    ·
                      rfl

theorem cell23_7444632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_7444632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444632 prefixEnd_7444632 := by exact prefixLift 7444632
  have htrace : WordTrace (prefixWord ++ tailWord_7444632) baseStart_7444632 baseEnd_7444632 := by
    simpa [prefixWord, tailWord_7444632, baseEnd_7444632] using wordTrace_append hprefix tailTrace_7444632
  have hstable : (prefixWord ++ tailWord_7444632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444632).length < 2 ^ (prefixWord ++ tailWord_7444632).sum := by decide
  have hdescent : baseEnd_7444632 < baseStart_7444632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444665 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 2, 3, 2]
def baseStart_7444665 : Nat := 118140960795 + 7444665 * 2 ^ 59
def prefixEnd_7444665 : Nat := 4983230072969 + 3 ^ 40 * 7444665 * 2
def baseEnd_7444665 : Nat := 3822691456704220447650115

theorem tailTrace_7444665 : CollatzResearch.WordTrace tailWord_7444665 prefixEnd_7444665 3822691456704220447650115 := by
  unfold tailWord_7444665
  simp only [CollatzResearch.WordTrace]
  refine ⟨271529239574257627401999449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181019493049505084934666299 271529239574257627401999449)
  ·
    refine ⟨203646929680693220551499587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271529239574257627401999449 203646929680693220551499587)
    ·
      refine ⟨305470394521039830827249381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203646929680693220551499587 305470394521039830827249381)
      ·
        refine ⟨57275698972694968280109259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305470394521039830827249381 57275698972694968280109259)
        ·
          refine ⟨85913548459042452420163889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57275698972694968280109259 85913548459042452420163889)
          ·
            refine ⟨64435161344281839315122917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85913548459042452420163889 64435161344281839315122917)
            ·
              refine ⟨12081592752052844871585547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64435161344281839315122917 12081592752052844871585547)
              ·
                refine ⟨18122389128079267307378321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12081592752052844871585547 18122389128079267307378321)
                ·
                  refine ⟨13591791846059450480533741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18122389128079267307378321 13591791846059450480533741)
                  ·
                    refine ⟨5096921942272293930200153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13591791846059450480533741 5096921942272293930200153)
                    ·
                      refine ⟨3822691456704220447650115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096921942272293930200153 3822691456704220447650115)
                      ·
                        rfl

theorem cell23_7444665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_7444665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444665 prefixEnd_7444665 := by exact prefixLift 7444665
  have htrace : WordTrace (prefixWord ++ tailWord_7444665) baseStart_7444665 baseEnd_7444665 := by
    simpa [prefixWord, tailWord_7444665, baseEnd_7444665] using wordTrace_append hprefix tailTrace_7444665
  have hstable : (prefixWord ++ tailWord_7444665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444665).length < 2 ^ (prefixWord ++ tailWord_7444665).sum := by decide
  have hdescent : baseEnd_7444665 < baseStart_7444665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444681 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 5]
def baseStart_7444681 : Nat := 118140960795 + 7444681 * 2 ^ 59
def prefixEnd_7444681 : Nat := 4983230072969 + 3 ^ 40 * 7444681 * 2
def baseEnd_7444681 : Nat := 3822699672394692385050041

theorem tailTrace_7444681 : CollatzResearch.WordTrace tailWord_7444681 prefixEnd_7444681 3822699672394692385050041 := by
  unfold tailWord_7444681
  simp only [CollatzResearch.WordTrace]
  refine ⟨271529823142199662134581897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181019882094799774756387931 271529823142199662134581897)
  ·
    refine ⟨203647367356649746600936423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271529823142199662134581897 203647367356649746600936423)
    ·
      refine ⟨305471051034974619901404635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203647367356649746600936423 305471051034974619901404635)
      ·
        refine ⟨458206576552461929852106953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305471051034974619901404635 458206576552461929852106953)
        ·
          refine ⟨343654932414346447389080215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458206576552461929852106953 343654932414346447389080215)
          ·
            refine ⟨515482398621519671083620323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343654932414346447389080215 515482398621519671083620323)
            ·
              refine ⟨773223597932279506625430485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515482398621519671083620323 773223597932279506625430485)
              ·
                refine ⟨18122428076537800936533527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 773223597932279506625430485 18122428076537800936533527)
                ·
                  refine ⟨27183642114806701404800291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18122428076537800936533527 27183642114806701404800291)
                  ·
                    refine ⟨40775463172210052107200437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27183642114806701404800291 40775463172210052107200437)
                    ·
                      refine ⟨3822699672394692385050041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40775463172210052107200437 3822699672394692385050041)
                      ·
                        rfl

theorem cell23_7444681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_7444681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444681 prefixEnd_7444681 := by exact prefixLift 7444681
  have htrace : WordTrace (prefixWord ++ tailWord_7444681) baseStart_7444681 baseEnd_7444681 := by
    simpa [prefixWord, tailWord_7444681, baseEnd_7444681] using wordTrace_append hprefix tailTrace_7444681
  have hstable : (prefixWord ++ tailWord_7444681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444681).length < 2 ^ (prefixWord ++ tailWord_7444681).sum := by decide
  have hdescent : baseEnd_7444681 < baseStart_7444681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444695 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 3, 2, 2]
def baseStart_7444695 : Nat := 118140960795 + 7444695 * 2 ^ 59
def prefixEnd_7444695 : Nat := 4983230072969 + 3 ^ 40 * 7444695 * 2
def baseEnd_7444695 : Nat := 3822706861123855330274977

theorem tailTrace_7444695 : CollatzResearch.WordTrace tailWord_7444695 prefixEnd_7444695 3822706861123855330274977 := by
  unfold tailWord_7444695
  simp only [CollatzResearch.WordTrace]
  refine ⟨271530333764148942525591539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181020222509432628350394359 271530333764148942525591539)
  ·
    refine ⟨407295500646223413788387309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271530333764148942525591539 407295500646223413788387309)
    ·
      refine ⟨152735812742333780170645241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407295500646223413788387309 152735812742333780170645241)
      ·
        refine ⟨114551859556750335127983931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152735812742333780170645241 114551859556750335127983931)
        ·
          refine ⟨171827789335125502691975897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114551859556750335127983931 171827789335125502691975897)
          ·
            refine ⟨128870842001344127018981923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171827789335125502691975897 128870842001344127018981923)
            ·
              refine ⟨193306263002016190528472885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128870842001344127018981923 193306263002016190528472885)
              ·
                refine ⟨18122462156439017862044333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193306263002016190528472885 18122462156439017862044333)
                ·
                  refine ⟨6795923308664631698266625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18122462156439017862044333 6795923308664631698266625)
                  ·
                    refine ⟨5096942481498473773699969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795923308664631698266625 5096942481498473773699969)
                    ·
                      refine ⟨3822706861123855330274977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096942481498473773699969 3822706861123855330274977)
                      ·
                        rfl

theorem cell23_7444695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_7444695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444695 prefixEnd_7444695 := by exact prefixLift 7444695
  have htrace : WordTrace (prefixWord ++ tailWord_7444695) baseStart_7444695 baseEnd_7444695 := by
    simpa [prefixWord, tailWord_7444695, baseEnd_7444695] using wordTrace_append hprefix tailTrace_7444695
  have hstable : (prefixWord ++ tailWord_7444695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444695).length < 2 ^ (prefixWord ++ tailWord_7444695).sum := by decide
  have hdescent : baseEnd_7444695 < baseStart_7444695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444698 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3]
def baseStart_7444698 : Nat := 118140960795 + 7444698 * 2 ^ 59
def prefixEnd_7444698 : Nat := 4983230072969 + 3 ^ 40 * 7444698 * 2
def baseEnd_7444698 : Nat := 3822708401565818818537463

theorem tailTrace_7444698 : CollatzResearch.WordTrace tailWord_7444698 prefixEnd_7444698 3822708401565818818537463 := by
  unfold tailWord_7444698
  simp only [CollatzResearch.WordTrace]
  refine ⟨67882610795784518509487687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181020295455425382691967165 67882610795784518509487687)
  ·
    refine ⟨101823916193676777764231531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67882610795784518509487687 101823916193676777764231531)
    ·
      refine ⟨152735874290515166646347297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101823916193676777764231531 152735874290515166646347297)
      ·
        refine ⟨114551905717886374984760473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152735874290515166646347297 114551905717886374984760473)
        ·
          refine ⟨85913929288414781238570355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114551905717886374984760473 85913929288414781238570355)
          ·
            refine ⟨128870893932622171857855533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85913929288414781238570355 128870893932622171857855533)
            ·
              refine ⟨48326585224733314446695825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128870893932622171857855533 48326585224733314446695825)
              ·
                refine ⟨36244938918549985835021869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48326585224733314446695825 36244938918549985835021869)
                ·
                  refine ⟨13591852094456244688133201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36244938918549985835021869 13591852094456244688133201)
                  ·
                    refine ⟨10193889070842183516099901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13591852094456244688133201 10193889070842183516099901)
                    ·
                      refine ⟨3822708401565818818537463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10193889070842183516099901 3822708401565818818537463)
                      ·
                        rfl

theorem cell23_7444698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_7444698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444698 prefixEnd_7444698 := by exact prefixLift 7444698
  have htrace : WordTrace (prefixWord ++ tailWord_7444698) baseStart_7444698 baseEnd_7444698 := by
    simpa [prefixWord, tailWord_7444698, baseEnd_7444698] using wordTrace_append hprefix tailTrace_7444698
  have hstable : (prefixWord ++ tailWord_7444698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444698).length < 2 ^ (prefixWord ++ tailWord_7444698).sum := by decide
  have hdescent : baseEnd_7444698 < baseStart_7444698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444706 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7444706 : Nat := 118140960795 + 7444706 * 2 ^ 59
def prefixEnd_7444706 : Nat := 4983230072969 + 3 ^ 40 * 7444706 * 2
def baseEnd_7444706 : Nat := 3822712509411054787237427

theorem tailTrace_7444706 : CollatzResearch.WordTrace tailWord_7444706 prefixEnd_7444706 3822712509411054787237427 := by
  unfold tailWord_7444706
  simp only [CollatzResearch.WordTrace]
  refine ⟨67882683741777272851060493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181020489978072727602827981 67882683741777272851060493)
  ·
    refine ⟨25456006403166477319147685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67882683741777272851060493 25456006403166477319147685)
    ·
      refine ⟨4773001200593714497340191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25456006403166477319147685 4773001200593714497340191)
      ·
        refine ⟨7159501800890571746010287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4773001200593714497340191 7159501800890571746010287)
        ·
          refine ⟨10739252701335857619015431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7159501800890571746010287 10739252701335857619015431)
          ·
            refine ⟨16108879052003786428523147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10739252701335857619015431 16108879052003786428523147)
            ·
              refine ⟨24163318578005679642784721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16108879052003786428523147 24163318578005679642784721)
              ·
                refine ⟨18122488933504259732088541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24163318578005679642784721 18122488933504259732088541)
                ·
                  refine ⟨6795933350064097399533203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18122488933504259732088541 6795933350064097399533203)
                  ·
                    refine ⟨10193900025096146099299805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6795933350064097399533203 10193900025096146099299805)
                    ·
                      refine ⟨3822712509411054787237427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10193900025096146099299805 3822712509411054787237427)
                      ·
                        rfl

theorem cell23_7444706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7444706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444706 prefixEnd_7444706 := by exact prefixLift 7444706
  have htrace : WordTrace (prefixWord ++ tailWord_7444706) baseStart_7444706 baseEnd_7444706 := by
    simpa [prefixWord, tailWord_7444706, baseEnd_7444706] using wordTrace_append hprefix tailTrace_7444706
  have hstable : (prefixWord ++ tailWord_7444706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444706).length < 2 ^ (prefixWord ++ tailWord_7444706).sum := by decide
  have hdescent : baseEnd_7444706 < baseStart_7444706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444712 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_7444712 : Nat := 118140960795 + 7444712 * 2 ^ 59
def prefixEnd_7444712 : Nat := 4983230072969 + 3 ^ 40 * 7444712 * 2
def baseEnd_7444712 : Nat := 3822715590294981763762399

theorem tailTrace_7444712 : CollatzResearch.WordTrace tailWord_7444712 prefixEnd_7444712 3822715590294981763762399 := by
  unfold tailWord_7444712
  simp only [CollatzResearch.WordTrace]
  refine ⟨135765476902543677214480195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181020635870058236285973593 135765476902543677214480195)
  ·
    refine ⟨203648215353815515821720293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135765476902543677214480195 203648215353815515821720293)
    ·
      refine ⟨38184040378840409216572555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203648215353815515821720293 38184040378840409216572555)
      ·
        refine ⟨57276060568260613824858833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38184040378840409216572555 57276060568260613824858833)
        ·
          refine ⟨42957045426195460368644125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57276060568260613824858833 42957045426195460368644125)
          ·
            refine ⟨16108892034823297638241547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42957045426195460368644125 16108892034823297638241547)
            ·
              refine ⟨24163338052234946457362321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16108892034823297638241547 24163338052234946457362321)
              ·
                refine ⟨18122503539176209843021741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24163338052234946457362321 18122503539176209843021741)
                ·
                  refine ⟨6795938827191078691133153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18122503539176209843021741 6795938827191078691133153)
                  ·
                    refine ⟨5096954120393309018349865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795938827191078691133153 5096954120393309018349865)
                    ·
                      refine ⟨3822715590294981763762399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096954120393309018349865 3822715590294981763762399)
                      ·
                        rfl

theorem cell23_7444712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_7444712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444712 prefixEnd_7444712 := by exact prefixLift 7444712
  have htrace : WordTrace (prefixWord ++ tailWord_7444712) baseStart_7444712 baseEnd_7444712 := by
    simpa [prefixWord, tailWord_7444712, baseEnd_7444712] using wordTrace_append hprefix tailTrace_7444712
  have hstable : (prefixWord ++ tailWord_7444712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444712).length < 2 ^ (prefixWord ++ tailWord_7444712).sum := by decide
  have hdescent : baseEnd_7444712 < baseStart_7444712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444732 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 1, 2, 3]
def baseStart_7444732 : Nat := 118140960795 + 7444732 * 2 ^ 59
def prefixEnd_7444732 : Nat := 4983230072969 + 3 ^ 40 * 7444732 * 2
def baseEnd_7444732 : Nat := 3822725859908071685512307

theorem tailTrace_7444732 : CollatzResearch.WordTrace tailWord_7444732 prefixEnd_7444732 3822725859908071685512307 := by
  unfold tailWord_7444732
  simp only [CollatzResearch.WordTrace]
  refine ⟨135765841632507448922344225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181021122176676598563125633 135765841632507448922344225)
  ·
    refine ⟨101824381224380586691758169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135765841632507448922344225 101824381224380586691758169)
    ·
      refine ⟨76368285918285440018818627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101824381224380586691758169 76368285918285440018818627)
      ·
        refine ⟨114552428877428160028227941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76368285918285440018818627 114552428877428160028227941)
        ·
          refine ⟨21478580414517780005292739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114552428877428160028227941 21478580414517780005292739)
          ·
            refine ⟨32217870621776670007939109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21478580414517780005292739 32217870621776670007939109)
            ·
              refine ⟨6040850741583125626488583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32217870621776670007939109 6040850741583125626488583)
              ·
                refine ⟨9061276112374688439732875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040850741583125626488583 9061276112374688439732875)
                ·
                  refine ⟨13591914168562032659599313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9061276112374688439732875 13591914168562032659599313)
                  ·
                    refine ⟨10193935626421524494699485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13591914168562032659599313 10193935626421524494699485)
                    ·
                      refine ⟨3822725859908071685512307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10193935626421524494699485 3822725859908071685512307)
                      ·
                        rfl

theorem cell23_7444732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_7444732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444732 prefixEnd_7444732 := by exact prefixLift 7444732
  have htrace : WordTrace (prefixWord ++ tailWord_7444732) baseStart_7444732 baseEnd_7444732 := by
    simpa [prefixWord, tailWord_7444732, baseEnd_7444732] using wordTrace_append hprefix tailTrace_7444732
  have hstable : (prefixWord ++ tailWord_7444732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444732).length < 2 ^ (prefixWord ++ tailWord_7444732).sum := by decide
  have hdescent : baseEnd_7444732 < baseStart_7444732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444741 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_7444741 : Nat := 118140960795 + 7444741 * 2 ^ 59
def prefixEnd_7444741 : Nat := 4983230072969 + 3 ^ 40 * 7444741 * 2
def baseEnd_7444741 : Nat := 3822730481233962150299765

theorem tailTrace_7444741 : CollatzResearch.WordTrace tailWord_7444741 prefixEnd_7444741 3822730481233962150299765 := by
  unfold tailWord_7444741
  simp only [CollatzResearch.WordTrace]
  refine ⟨271532011521982292381766077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181021341014654861587844051 271532011521982292381766077)
  ·
    refine ⟨101824504320743359643162279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271532011521982292381766077 101824504320743359643162279)
    ·
      refine ⟨152736756481115039464743419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101824504320743359643162279 152736756481115039464743419)
      ·
        refine ⟨229105134721672559197115129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152736756481115039464743419 229105134721672559197115129)
        ·
          refine ⟨171828851041254419397836347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229105134721672559197115129 171828851041254419397836347)
          ·
            refine ⟨257743276561881629096754521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171828851041254419397836347 257743276561881629096754521)
            ·
              refine ⟨193307457421411221822565891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257743276561881629096754521 193307457421411221822565891)
              ·
                refine ⟨289961186132116832733848837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193307457421411221822565891 289961186132116832733848837)
                ·
                  refine ⟨54367722399771906137596657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289961186132116832733848837 54367722399771906137596657)
                  ·
                    refine ⟨40775791799828929603197493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54367722399771906137596657 40775791799828929603197493)
                    ·
                      refine ⟨3822730481233962150299765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40775791799828929603197493 3822730481233962150299765)
                      ·
                        rfl

theorem cell23_7444741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_7444741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444741 prefixEnd_7444741 := by exact prefixLift 7444741
  have htrace : WordTrace (prefixWord ++ tailWord_7444741) baseStart_7444741 baseEnd_7444741 := by
    simpa [prefixWord, tailWord_7444741, baseEnd_7444741] using wordTrace_append hprefix tailTrace_7444741
  have hstable : (prefixWord ++ tailWord_7444741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444741).length < 2 ^ (prefixWord ++ tailWord_7444741).sum := by decide
  have hdescent : baseEnd_7444741 < baseStart_7444741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444745 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 4, 1, 3]
def baseStart_7444745 : Nat := 118140960795 + 7444745 * 2 ^ 59
def prefixEnd_7444745 : Nat := 4983230072969 + 3 ^ 40 * 7444745 * 2
def baseEnd_7444745 : Nat := 3822732535156580134649747

theorem tailTrace_7444745 : CollatzResearch.WordTrace tailWord_7444745 prefixEnd_7444745 3822732535156580134649747 := by
  unfold tailWord_7444745
  simp only [CollatzResearch.WordTrace]
  refine ⟨271532157413967801064911689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181021438275978534043274459 271532157413967801064911689)
  ·
    refine ⟨203649118060475850798683767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271532157413967801064911689 203649118060475850798683767)
    ·
      refine ⟨305473677090713776198025651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203649118060475850798683767 305473677090713776198025651)
      ·
        refine ⟨458210515636070664297038477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305473677090713776198025651 458210515636070664297038477)
        ·
          refine ⟨171828943363526499111389429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458210515636070664297038477 171828943363526499111389429)
          ·
            refine ⟨16108963440330609291692759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171828943363526499111389429 16108963440330609291692759)
            ·
              refine ⟨24163445160495913937539139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16108963440330609291692759 24163445160495913937539139)
              ·
                refine ⟨36245167740743870906308709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24163445160495913937539139 36245167740743870906308709)
                ·
                  refine ⟨6795968951389475794932883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36245167740743870906308709 6795968951389475794932883)
                  ·
                    refine ⟨10193953427084213692399325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6795968951389475794932883 10193953427084213692399325)
                    ·
                      refine ⟨3822732535156580134649747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10193953427084213692399325 3822732535156580134649747)
                      ·
                        rfl

theorem cell23_7444745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 1, 3].length) (baseStart_7444745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444745 prefixEnd_7444745 := by exact prefixLift 7444745
  have htrace : WordTrace (prefixWord ++ tailWord_7444745) baseStart_7444745 baseEnd_7444745 := by
    simpa [prefixWord, tailWord_7444745, baseEnd_7444745] using wordTrace_append hprefix tailTrace_7444745
  have hstable : (prefixWord ++ tailWord_7444745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444745).length < 2 ^ (prefixWord ++ tailWord_7444745).sum := by decide
  have hdescent : baseEnd_7444745 < baseStart_7444745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444751 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 4]
def baseStart_7444751 : Nat := 118140960795 + 7444751 * 2 ^ 59
def prefixEnd_7444751 : Nat := 4983230072969 + 3 ^ 40 * 7444751 * 2
def baseEnd_7444751 : Nat := 3822735616040507111174719

theorem tailTrace_7444751 : CollatzResearch.WordTrace tailWord_7444751 prefixEnd_7444751 3822735616040507111174719 := by
  unfold tailWord_7444751
  simp only [CollatzResearch.WordTrace]
  refine ⟨271532376251946064089630107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181021584167964042726420071 271532376251946064089630107)
  ·
    refine ⟨407298564377919096134445161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271532376251946064089630107 407298564377919096134445161)
    ·
      refine ⟨305473923283439322100833871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407298564377919096134445161 305473923283439322100833871)
      ·
        refine ⟨458210884925158983151250807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305473923283439322100833871 458210884925158983151250807)
        ·
          refine ⟨687316327387738474726876211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458210884925158983151250807 687316327387738474726876211)
          ·
            refine ⟨1030974491081607712090314317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687316327387738474726876211 1030974491081607712090314317)
            ·
              refine ⟨386615434155602892033867869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1030974491081607712090314317 386615434155602892033867869)
              ·
                refine ⟨144980787808351084512700451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386615434155602892033867869 144980787808351084512700451)
                ·
                  refine ⟨217471181712526626769050677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144980787808351084512700451 217471181712526626769050677)
                  ·
                    refine ⟨20387923285549371259598501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 217471181712526626769050677 20387923285549371259598501)
                    ·
                      refine ⟨3822735616040507111174719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20387923285549371259598501 3822735616040507111174719)
                      ·
                        rfl

theorem cell23_7444751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_7444751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444751 prefixEnd_7444751 := by exact prefixLift 7444751
  have htrace : WordTrace (prefixWord ++ tailWord_7444751) baseStart_7444751 baseEnd_7444751 := by
    simpa [prefixWord, tailWord_7444751, baseEnd_7444751] using wordTrace_append hprefix tailTrace_7444751
  have hstable : (prefixWord ++ tailWord_7444751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444751).length < 2 ^ (prefixWord ++ tailWord_7444751).sum := by decide
  have hdescent : baseEnd_7444751 < baseStart_7444751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444762 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3]
def baseStart_7444762 : Nat := 118140960795 + 7444762 * 2 ^ 59
def prefixEnd_7444762 : Nat := 4983230072969 + 3 ^ 40 * 7444762 * 2
def baseEnd_7444762 : Nat := 3822741264327706568137169

theorem tailTrace_7444762 : CollatzResearch.WordTrace tailWord_7444762 prefixEnd_7444762 3822741264327706568137169 := by
  unfold tailWord_7444762
  simp only [CollatzResearch.WordTrace]
  refine ⟨67883194363726553242070135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181021851636604141978853693 67883194363726553242070135)
  ·
    refine ⟨101824791545589829863105203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67883194363726553242070135 101824791545589829863105203)
    ·
      refine ⟨152737187318384744794657805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101824791545589829863105203 152737187318384744794657805)
      ·
        refine ⟨57276445244394279297996677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152737187318384744794657805 57276445244394279297996677)
        ·
          refine ⟨10739333483323927368374377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57276445244394279297996677 10739333483323927368374377)
          ·
            refine ⟨8054500112492945526280783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10739333483323927368374377 8054500112492945526280783)
            ·
              refine ⟨12081750168739418289421175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8054500112492945526280783 12081750168739418289421175)
              ·
                refine ⟨18122625253109127434131763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12081750168739418289421175 18122625253109127434131763)
                ·
                  refine ⟨27183937879663691151197645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18122625253109127434131763 27183937879663691151197645)
                  ·
                    refine ⟨10193976704873884181699117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27183937879663691151197645 10193976704873884181699117)
                    ·
                      refine ⟨3822741264327706568137169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10193976704873884181699117 3822741264327706568137169)
                      ·
                        rfl

theorem cell23_7444762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_7444762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444762 prefixEnd_7444762 := by exact prefixLift 7444762
  have htrace : WordTrace (prefixWord ++ tailWord_7444762) baseStart_7444762 baseEnd_7444762 := by
    simpa [prefixWord, tailWord_7444762, baseEnd_7444762] using wordTrace_append hprefix tailTrace_7444762
  have hstable : (prefixWord ++ tailWord_7444762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444762).length < 2 ^ (prefixWord ++ tailWord_7444762).sum := by decide
  have hdescent : baseEnd_7444762 < baseStart_7444762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444772 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 1, 3, 2]
def baseStart_7444772 : Nat := 118140960795 + 7444772 * 2 ^ 59
def prefixEnd_7444772 : Nat := 4983230072969 + 3 ^ 40 * 7444772 * 2
def baseEnd_7444772 : Nat := 3822746399134251529012123

theorem tailTrace_7444772 : CollatzResearch.WordTrace tailWord_7444772 prefixEnd_7444772 3822746399134251529012123 := by
  unfold tailWord_7444772
  simp only [CollatzResearch.WordTrace]
  refine ⟨135766571092434992338072285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181022094789913323117429713 135766571092434992338072285)
  ·
    refine ⟨50912464159663122126777107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135766571092434992338072285 50912464159663122126777107)
    ·
      refine ⟨76368696239494683190165661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50912464159663122126777107 76368696239494683190165661)
      ·
        refine ⟨28638261089810506196312123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76368696239494683190165661 28638261089810506196312123)
        ·
          refine ⟨42957391634715759294468185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28638261089810506196312123 42957391634715759294468185)
          ·
            refine ⟨32218043726036819470851139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42957391634715759294468185 32218043726036819470851139)
            ·
              refine ⟨48327065589055229206276709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32218043726036819470851139 48327065589055229206276709)
              ·
                refine ⟨9061324797947855476176883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48327065589055229206276709 9061324797947855476176883)
                ·
                  refine ⟨13591987196921783214265325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9061324797947855476176883 13591987196921783214265325)
                  ·
                    refine ⟨5096995198845668705349497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13591987196921783214265325 5096995198845668705349497)
                    ·
                      refine ⟨3822746399134251529012123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5096995198845668705349497 3822746399134251529012123)
                      ·
                        rfl

theorem cell23_7444772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_7444772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444772 prefixEnd_7444772 := by exact prefixLift 7444772
  have htrace : WordTrace (prefixWord ++ tailWord_7444772) baseStart_7444772 baseEnd_7444772 := by
    simpa [prefixWord, tailWord_7444772, baseEnd_7444772] using wordTrace_append hprefix tailTrace_7444772
  have hstable : (prefixWord ++ tailWord_7444772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444772).length < 2 ^ (prefixWord ++ tailWord_7444772).sum := by decide
  have hdescent : baseEnd_7444772 < baseStart_7444772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444791 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 9]
def baseStart_7444791 : Nat := 118140960795 + 7444791 * 2 ^ 59
def prefixEnd_7444791 : Nat := 4983230072969 + 3 ^ 40 * 7444791 * 2
def baseEnd_7444791 : Nat := 424750683918520772741615

theorem tailTrace_7444791 : CollatzResearch.WordTrace tailWord_7444791 prefixEnd_7444791 424750683918520772741615 := by
  unfold tailWord_7444791
  simp only [CollatzResearch.WordTrace]
  refine ⟨271533835171801150921086227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181022556781200767280724151 271533835171801150921086227)
  ·
    refine ⟨407300752757701726381629341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271533835171801150921086227 407300752757701726381629341)
    ·
      refine ⟨152737782284138147393111003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407300752757701726381629341 152737782284138147393111003)
      ·
        refine ⟨229106673426207221089666505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152737782284138147393111003 229106673426207221089666505)
        ·
          refine ⟨171830005069655415817249879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229106673426207221089666505 171830005069655415817249879)
          ·
            refine ⟨257745007604483123725874819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171830005069655415817249879 257745007604483123725874819)
            ·
              refine ⟨386617511406724685588812229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257745007604483123725874819 386617511406724685588812229)
              ·
                refine ⟨72490783388760878547902293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 386617511406724685588812229 72490783388760878547902293)
                ·
                  refine ⟨424750683918520772741615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72490783388760878547902293 424750683918520772741615)
                  ·
                    rfl

theorem cell23_7444791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 9].length) (baseStart_7444791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444791 prefixEnd_7444791 := by exact prefixLift 7444791
  have htrace : WordTrace (prefixWord ++ tailWord_7444791) baseStart_7444791 baseEnd_7444791 := by
    simpa [prefixWord, tailWord_7444791, baseEnd_7444791] using wordTrace_append hprefix tailTrace_7444791
  have hstable : (prefixWord ++ tailWord_7444791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444791).length < 2 ^ (prefixWord ++ tailWord_7444791).sum := by decide
  have hdescent : baseEnd_7444791 < baseStart_7444791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444808 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 7]
def baseStart_7444808 : Nat := 118140960795 + 7444808 * 2 ^ 59
def prefixEnd_7444808 : Nat := 4983230072969 + 3 ^ 40 * 7444808 * 2
def baseEnd_7444808 : Nat := 424751653826423709795773

theorem tailTrace_7444808 : CollatzResearch.WordTrace tailWord_7444808 prefixEnd_7444808 424751653826423709795773 := by
  unfold tailWord_7444808
  simp only [CollatzResearch.WordTrace]
  refine ⟨135767227606369781412227539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181022970141826375216303385 135767227606369781412227539)
  ·
    refine ⟨203650841409554672118341309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135767227606369781412227539 203650841409554672118341309)
    ·
      refine ⟨76369065528583002044377991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203650841409554672118341309 76369065528583002044377991)
      ·
        refine ⟨114553598292874503066566987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76369065528583002044377991 114553598292874503066566987)
        ·
          refine ⟨171830397439311754599850481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114553598292874503066566987 171830397439311754599850481)
          ·
            refine ⟨128872798079483815949887861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171830397439311754599850481 128872798079483815949887861)
            ·
              refine ⟨12081824819951607745301987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128872798079483815949887861 12081824819951607745301987)
              ·
                refine ⟨18122737229927411617952981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12081824819951607745301987 18122737229927411617952981)
                ·
                  refine ⟨424751653826423709795773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18122737229927411617952981 424751653826423709795773)
                  ·
                    rfl

theorem cell23_7444808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 7].length) (baseStart_7444808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444808 prefixEnd_7444808 := by exact prefixLift 7444808
  have htrace : WordTrace (prefixWord ++ tailWord_7444808) baseStart_7444808 baseEnd_7444808 := by
    simpa [prefixWord, tailWord_7444808, baseEnd_7444808] using wordTrace_append hprefix tailTrace_7444808
  have hstable : (prefixWord ++ tailWord_7444808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444808).length < 2 ^ (prefixWord ++ tailWord_7444808).sum := by decide
  have hdescent : baseEnd_7444808 < baseStart_7444808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444811 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 8]
def baseStart_7444811 : Nat := 118140960795 + 7444811 * 2 ^ 59
def prefixEnd_7444811 : Nat := 4983230072969 + 3 ^ 40 * 7444811 * 2
def baseEnd_7444811 : Nat := 3822766424879776876424443

theorem tailTrace_7444811 : CollatzResearch.WordTrace tailWord_7444811 prefixEnd_7444811 3822766424879776876424443 := by
  unfold tailWord_7444811
  simp only [CollatzResearch.WordTrace]
  refine ⟨271534564631728694336814287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181023043087819129557876191 271534564631728694336814287)
  ·
    refine ⟨407301846947593041505221431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271534564631728694336814287 407301846947593041505221431)
    ·
      refine ⟨610952770421389562257832147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407301846947593041505221431 610952770421389562257832147)
      ·
        refine ⟨916429155632084343386748221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610952770421389562257832147 916429155632084343386748221)
        ·
          refine ⟨343660933362031628770030583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 916429155632084343386748221 343660933362031628770030583)
          ·
            refine ⟨515491400043047443155045875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343660933362031628770030583 515491400043047443155045875)
            ·
              refine ⟨773237100064571164732568813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515491400043047443155045875 773237100064571164732568813)
              ·
                refine ⟨289963912524214186774713305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 773237100064571164732568813 289963912524214186774713305)
                ·
                  refine ⟨217472934393160640081034979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289963912524214186774713305 217472934393160640081034979)
                  ·
                    refine ⟨326209401589740960121552469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217472934393160640081034979 326209401589740960121552469)
                    ·
                      refine ⟨3822766424879776876424443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 326209401589740960121552469 3822766424879776876424443)
                      ·
                        rfl

theorem cell23_7444811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_7444811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444811 prefixEnd_7444811 := by exact prefixLift 7444811
  have htrace : WordTrace (prefixWord ++ tailWord_7444811) baseStart_7444811 baseEnd_7444811 := by
    simpa [prefixWord, tailWord_7444811, baseEnd_7444811] using wordTrace_append hprefix tailTrace_7444811
  have hstable : (prefixWord ++ tailWord_7444811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444811).length < 2 ^ (prefixWord ++ tailWord_7444811).sum := by decide
  have hdescent : baseEnd_7444811 < baseStart_7444811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444848 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 5]
def baseStart_7444848 : Nat := 118140960795 + 7444848 * 2 ^ 59
def prefixEnd_7444848 : Nat := 4983230072969 + 3 ^ 40 * 7444848 * 2
def baseEnd_7444848 : Nat := 3822785423663993231661773

theorem tailTrace_7444848 : CollatzResearch.WordTrace tailWord_7444848 prefixEnd_7444848 3822785423663993231661773 := by
  unfold tailWord_7444848
  simp only [CollatzResearch.WordTrace]
  refine ⟨135767957066297324827955599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181023942755063099770607465 135767957066297324827955599)
  ·
    refine ⟨203651935599445987241933399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135767957066297324827955599 203651935599445987241933399)
    ·
      refine ⟨305477903399168980862900099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203651935599445987241933399 305477903399168980862900099)
      ·
        refine ⟨458216855098753471294350149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305477903399168980862900099 458216855098753471294350149)
        ·
          refine ⟨85915660331016275867690653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 458216855098753471294350149 85915660331016275867690653)
          ·
            refine ⟨32218372624131103450383995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85915660331016275867690653 32218372624131103450383995)
            ·
              refine ⟨48327558936196655175575993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32218372624131103450383995 48327558936196655175575993)
              ·
                refine ⟨36245669202147491381681995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48327558936196655175575993 36245669202147491381681995)
                ·
                  refine ⟨54368503803221237072522993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36245669202147491381681995 54368503803221237072522993)
                  ·
                    refine ⟨40776377852415927804392245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54368503803221237072522993 40776377852415927804392245)
                    ·
                      refine ⟨3822785423663993231661773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40776377852415927804392245 3822785423663993231661773)
                      ·
                        rfl

theorem cell23_7444848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_7444848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444848 prefixEnd_7444848 := by exact prefixLift 7444848
  have htrace : WordTrace (prefixWord ++ tailWord_7444848) baseStart_7444848 baseEnd_7444848 := by
    simpa [prefixWord, tailWord_7444848, baseEnd_7444848] using wordTrace_append hprefix tailTrace_7444848
  have hstable : (prefixWord ++ tailWord_7444848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444848).length < 2 ^ (prefixWord ++ tailWord_7444848).sum := by decide
  have hdescent : baseEnd_7444848 < baseStart_7444848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444865 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_7444865 : Nat := 118140960795 + 7444865 * 2 ^ 59
def prefixEnd_7444865 : Nat := 4983230072969 + 3 ^ 40 * 7444865 * 2
def baseEnd_7444865 : Nat := 3822794152835119665149195

theorem tailTrace_7444865 : CollatzResearch.WordTrace tailWord_7444865 prefixEnd_7444865 3822794152835119665149195 := by
  unfold tailWord_7444865
  simp only [CollatzResearch.WordTrace]
  refine ⟨271536534173533061559280049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181024356115688707706186699 271536534173533061559280049)
  ·
    refine ⟨203652400630149796169460037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271536534173533061559280049 203652400630149796169460037)
    ·
      refine ⟨38184825118153086781773757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203652400630149796169460037 38184825118153086781773757)
      ·
        refine ⟨14319309419307407543165159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38184825118153086781773757 14319309419307407543165159)
        ·
          refine ⟨21478964128961111314747739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14319309419307407543165159 21478964128961111314747739)
          ·
            refine ⟨32218446193441666972121609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21478964128961111314747739 32218446193441666972121609)
            ·
              refine ⟨24163834645081250229091207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32218446193441666972121609 24163834645081250229091207)
              ·
                refine ⟨36245751967621875343636811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24163834645081250229091207 36245751967621875343636811)
                ·
                  refine ⟨54368627951432813015455217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36245751967621875343636811 54368627951432813015455217)
                  ·
                    refine ⟨40776470963574609761591413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54368627951432813015455217 40776470963574609761591413)
                    ·
                      refine ⟨3822794152835119665149195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40776470963574609761591413 3822794152835119665149195)
                      ·
                        rfl

theorem cell23_7444865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_7444865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444865 prefixEnd_7444865 := by exact prefixLift 7444865
  have htrace : WordTrace (prefixWord ++ tailWord_7444865) baseStart_7444865 baseEnd_7444865 := by
    simpa [prefixWord, tailWord_7444865, baseEnd_7444865] using wordTrace_append hprefix tailTrace_7444865
  have hstable : (prefixWord ++ tailWord_7444865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444865).length < 2 ^ (prefixWord ++ tailWord_7444865).sum := by decide
  have hdescent : baseEnd_7444865 < baseStart_7444865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444875 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 1, 6, 2]
def baseStart_7444875 : Nat := 118140960795 + 7444875 * 2 ^ 59
def prefixEnd_7444875 : Nat := 4983230072969 + 3 ^ 40 * 7444875 * 2
def baseEnd_7444875 : Nat := 3822799287641664626024149

theorem tailTrace_7444875 : CollatzResearch.WordTrace tailWord_7444875 prefixEnd_7444875 3822799287641664626024149 := by
  unfold tailWord_7444875
  simp only [CollatzResearch.WordTrace]
  refine ⟨271536898903496833267144079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181024599268997888844762719 271536898903496833267144079)
  ·
    refine ⟨407305348355245249900716119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271536898903496833267144079 407305348355245249900716119)
    ·
      refine ⟨610958022532867874851074179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407305348355245249900716119 610958022532867874851074179)
      ·
        refine ⟨916437033799301812276611269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610958022532867874851074179 916437033799301812276611269)
        ·
          refine ⟨171831943837369089801864613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 916437033799301812276611269 171831943837369089801864613)
          ·
            refine ⟨32218489469506704337849615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171831943837369089801864613 32218489469506704337849615)
            ·
              refine ⟨48327734204260056506774423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32218489469506704337849615 48327734204260056506774423)
              ·
                refine ⟨72491601306390084760161635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48327734204260056506774423 72491601306390084760161635)
                ·
                  refine ⟨108737401959585127140242453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72491601306390084760161635 108737401959585127140242453)
                  ·
                    refine ⟨5097065716855552834698865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108737401959585127140242453 5097065716855552834698865)
                    ·
                      refine ⟨3822799287641664626024149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5097065716855552834698865 3822799287641664626024149)
                      ·
                        rfl

theorem cell23_7444875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 6, 2].length) (baseStart_7444875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444875 prefixEnd_7444875 := by exact prefixLift 7444875
  have htrace : WordTrace (prefixWord ++ tailWord_7444875) baseStart_7444875 baseEnd_7444875 := by
    simpa [prefixWord, tailWord_7444875, baseEnd_7444875] using wordTrace_append hprefix tailTrace_7444875
  have hstable : (prefixWord ++ tailWord_7444875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444875).length < 2 ^ (prefixWord ++ tailWord_7444875).sum := by decide
  have hdescent : baseEnd_7444875 < baseStart_7444875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444895 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 3]
def baseStart_7444895 : Nat := 118140960795 + 7444895 * 2 ^ 59
def prefixEnd_7444895 : Nat := 4983230072969 + 3 ^ 40 * 7444895 * 2
def baseEnd_7444895 : Nat := 3822809557254754547774057

theorem tailTrace_7444895 : CollatzResearch.WordTrace tailWord_7444895 prefixEnd_7444895 3822809557254754547774057 := by
  unfold tailWord_7444895
  simp only [CollatzResearch.WordTrace]
  refine ⟨271537628363424376682872139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181025085575616251121914759 271537628363424376682872139)
  ·
    refine ⟨407306442545136565024308209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271537628363424376682872139 407306442545136565024308209)
    ·
      refine ⟨305479831908852423768231157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407306442545136565024308209 305479831908852423768231157)
      ·
        refine ⟨28638734241454914728271671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 305479831908852423768231157 28638734241454914728271671)
        ·
          refine ⟨42958101362182372092407507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28638734241454914728271671 42958101362182372092407507)
          ·
            refine ⟨64437152043273558138611261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42958101362182372092407507 64437152043273558138611261)
            ·
              refine ⟨24163932016227584301979223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64437152043273558138611261 24163932016227584301979223)
              ·
                refine ⟨36245898024341376452968835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24163932016227584301979223 36245898024341376452968835)
                ·
                  refine ⟨54368847036512064679453253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36245898024341376452968835 54368847036512064679453253)
                  ·
                    refine ⟨10194158819346012127397485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54368847036512064679453253 10194158819346012127397485)
                    ·
                      refine ⟨3822809557254754547774057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10194158819346012127397485 3822809557254754547774057)
                      ·
                        rfl

theorem cell23_7444895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_7444895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444895 prefixEnd_7444895 := by exact prefixLift 7444895
  have htrace : WordTrace (prefixWord ++ tailWord_7444895) baseStart_7444895 baseEnd_7444895 := by
    simpa [prefixWord, tailWord_7444895, baseEnd_7444895] using wordTrace_append hprefix tailTrace_7444895
  have hstable : (prefixWord ++ tailWord_7444895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444895).length < 2 ^ (prefixWord ++ tailWord_7444895).sum := by decide
  have hdescent : baseEnd_7444895 < baseStart_7444895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444952 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 2, 3, 2]
def baseStart_7444952 : Nat := 118140960795 + 7444952 * 2 ^ 59
def prefixEnd_7444952 : Nat := 4983230072969 + 3 ^ 40 * 7444952 * 2
def baseEnd_7444952 : Nat := 3822838825652060824761295

theorem tailTrace_7444952 : CollatzResearch.WordTrace tailWord_7444952 prefixEnd_7444952 3822838825652060824761295 := by
  unfold tailWord_7444952
  simp only [CollatzResearch.WordTrace]
  refine ⟨135769853662108937708848555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181026471549478583611798073 135769853662108937708848555)
  ·
    refine ⟨203654780493163406563272833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135769853662108937708848555 203654780493163406563272833)
    ·
      refine ⟨152741085369872554922454625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203654780493163406563272833 152741085369872554922454625)
      ·
        refine ⟨114555814027404416191840969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152741085369872554922454625 114555814027404416191840969)
        ·
          refine ⟨85916860520553312143880727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114555814027404416191840969 85916860520553312143880727)
          ·
            refine ⟨128875290780829968215821091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85916860520553312143880727 128875290780829968215821091)
            ·
              refine ⟨193312936171244952323731637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128875290780829968215821091 193312936171244952323731637)
              ·
                refine ⟨18123087766054214280349841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193312936171244952323731637 18123087766054214280349841)
                ·
                  refine ⟨13592315824540660710262381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18123087766054214280349841 13592315824540660710262381)
                  ·
                    refine ⟨5097118434202747766348393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13592315824540660710262381 5097118434202747766348393)
                    ·
                      refine ⟨3822838825652060824761295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5097118434202747766348393 3822838825652060824761295)
                      ·
                        rfl

theorem cell23_7444952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_7444952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444952 prefixEnd_7444952 := by exact prefixLift 7444952
  have htrace : WordTrace (prefixWord ++ tailWord_7444952) baseStart_7444952 baseEnd_7444952 := by
    simpa [prefixWord, tailWord_7444952, baseEnd_7444952] using wordTrace_append hprefix tailTrace_7444952
  have hstable : (prefixWord ++ tailWord_7444952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444952).length < 2 ^ (prefixWord ++ tailWord_7444952).sum := by decide
  have hdescent : baseEnd_7444952 < baseStart_7444952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444976 : List Nat := [2, 1, 1, 1, 3, 3, 5, 2, 1, 1, 3]
def baseStart_7444976 : Nat := 118140960795 + 7444976 * 2 ^ 59
def prefixEnd_7444976 : Nat := 4983230072969 + 3 ^ 40 * 7444976 * 2
def baseEnd_7444976 : Nat := 3822851149187768730861185

theorem tailTrace_7444976 : CollatzResearch.WordTrace tailWord_7444976 prefixEnd_7444976 3822851149187768730861185 := by
  unfold tailWord_7444976
  simp only [CollatzResearch.WordTrace]
  refine ⟨135770291338065463758285391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181027055117420618344380521 135770291338065463758285391)
  ·
    refine ⟨203655437007098195637428087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135770291338065463758285391 203655437007098195637428087)
    ·
      refine ⟨305483155510647293456142131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203655437007098195637428087 305483155510647293456142131)
      ·
        refine ⟨458224733265970940184213197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305483155510647293456142131 458224733265970940184213197)
        ·
          refine ⟨171834274974739102569079949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458224733265970940184213197 171834274974739102569079949)
          ·
            refine ⟨64437853115527163463404981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171834274974739102569079949 64437853115527163463404981)
            ·
              refine ⟨6041048729580671574694217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64437853115527163463404981 6041048729580671574694217)
              ·
                refine ⟨4530786547185503681020663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6041048729580671574694217 4530786547185503681020663)
                ·
                  refine ⟨6796179820778255521530995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530786547185503681020663 6796179820778255521530995)
                  ·
                    refine ⟨10194269731167383282296493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6796179820778255521530995 10194269731167383282296493)
                    ·
                      refine ⟨3822851149187768730861185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10194269731167383282296493 3822851149187768730861185)
                      ·
                        rfl

theorem cell23_7444976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 1, 1, 3].length) (baseStart_7444976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444976 prefixEnd_7444976 := by exact prefixLift 7444976
  have htrace : WordTrace (prefixWord ++ tailWord_7444976) baseStart_7444976 baseEnd_7444976 := by
    simpa [prefixWord, tailWord_7444976, baseEnd_7444976] using wordTrace_append hprefix tailTrace_7444976
  have hstable : (prefixWord ++ tailWord_7444976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444976).length < 2 ^ (prefixWord ++ tailWord_7444976).sum := by decide
  have hdescent : baseEnd_7444976 < baseStart_7444976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444982 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_7444982 : Nat := 118140960795 + 7444982 * 2 ^ 59
def prefixEnd_7444982 : Nat := 4983230072969 + 3 ^ 40 * 7444982 * 2
def baseEnd_7444982 : Nat := 3822854230071695707386157

theorem tailTrace_7444982 : CollatzResearch.WordTrace tailWord_7444982 prefixEnd_7444982 3822854230071695707386157 := by
  unfold tailWord_7444982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16971300094631824408830575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181027201009406127027526133 16971300094631824408830575)
  ·
    refine ⟨25456950141947736613245863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16971300094631824408830575 25456950141947736613245863)
    ·
      refine ⟨38185425212921604919868795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25456950141947736613245863 38185425212921604919868795)
      ·
        refine ⟨57278137819382407379803193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38185425212921604919868795 57278137819382407379803193)
        ·
          refine ⟨42958603364536805534852395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57278137819382407379803193 42958603364536805534852395)
          ·
            refine ⟨64437905046805208302278593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42958603364536805534852395 64437905046805208302278593)
            ·
              refine ⟨48328428785103906226708945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64437905046805208302278593 48328428785103906226708945)
              ·
                refine ⟨36246321588827929670031709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48328428785103906226708945 36246321588827929670031709)
                ·
                  refine ⟨13592370595810473626261891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36246321588827929670031709 13592370595810473626261891)
                  ·
                    refine ⟨20388555893715710439392837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13592370595810473626261891 20388555893715710439392837)
                    ·
                      refine ⟨3822854230071695707386157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20388555893715710439392837 3822854230071695707386157)
                      ·
                        rfl

theorem cell23_7444982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_7444982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444982 prefixEnd_7444982 := by exact prefixLift 7444982
  have htrace : WordTrace (prefixWord ++ tailWord_7444982) baseStart_7444982 baseEnd_7444982 := by
    simpa [prefixWord, tailWord_7444982, baseEnd_7444982] using wordTrace_append hprefix tailTrace_7444982
  have hstable : (prefixWord ++ tailWord_7444982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444982).length < 2 ^ (prefixWord ++ tailWord_7444982).sum := by decide
  have hdescent : baseEnd_7444982 < baseStart_7444982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444985 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 5]
def baseStart_7444985 : Nat := 118140960795 + 7444985 * 2 ^ 59
def prefixEnd_7444985 : Nat := 4983230072969 + 3 ^ 40 * 7444985 * 2
def baseEnd_7444985 : Nat := 3822855770513659195648643

theorem tailTrace_7444985 : CollatzResearch.WordTrace tailWord_7444985 prefixEnd_7444985 3822855770513659195648643 := by
  unfold tailWord_7444985
  simp only [CollatzResearch.WordTrace]
  refine ⟨271540910933098322053648409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181027273955398881369098939 271540910933098322053648409)
  ·
    refine ⟨203655683199823741540236307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271540910933098322053648409 203655683199823741540236307)
    ·
      refine ⟨305483524799735612310354461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203655683199823741540236307 305483524799735612310354461)
      ·
        refine ⟨114556321799900854616382923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305483524799735612310354461 114556321799900854616382923)
        ·
          refine ⟨171834482699851281924574385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114556321799900854616382923 171834482699851281924574385)
          ·
            refine ⟨128875862024888461443430789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171834482699851281924574385 128875862024888461443430789)
            ·
              refine ⟨24164224129666586520643273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128875862024888461443430789 24164224129666586520643273)
              ·
                refine ⟨18123168097249939890482455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24164224129666586520643273 18123168097249939890482455)
                ·
                  refine ⟨27184752145874909835723683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18123168097249939890482455 27184752145874909835723683)
                  ·
                    refine ⟨40777128218812364753585525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27184752145874909835723683 40777128218812364753585525)
                    ·
                      refine ⟨3822855770513659195648643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40777128218812364753585525 3822855770513659195648643)
                      ·
                        rfl

theorem cell23_7444985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_7444985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444985 prefixEnd_7444985 := by exact prefixLift 7444985
  have htrace : WordTrace (prefixWord ++ tailWord_7444985) baseStart_7444985 baseEnd_7444985 := by
    simpa [prefixWord, tailWord_7444985, baseEnd_7444985] using wordTrace_append hprefix tailTrace_7444985
  have hstable : (prefixWord ++ tailWord_7444985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444985).length < 2 ^ (prefixWord ++ tailWord_7444985).sum := by decide
  have hdescent : baseEnd_7444985 < baseStart_7444985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7444995 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 4]
def baseStart_7444995 : Nat := 118140960795 + 7444995 * 2 ^ 59
def prefixEnd_7444995 : Nat := 4983230072969 + 3 ^ 40 * 7444995 * 2
def baseEnd_7444995 : Nat := 3822860905320204156523597

theorem tailTrace_7444995 : CollatzResearch.WordTrace tailWord_7444995 prefixEnd_7444995 3822860905320204156523597 := by
  unfold tailWord_7444995
  simp only [CollatzResearch.WordTrace]
  refine ⟨271541275663062093761512439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181027517108708062507674959 271541275663062093761512439)
  ·
    refine ⟨407311913494593140642268659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271541275663062093761512439 407311913494593140642268659)
    ·
      refine ⟨610967870241889710963402989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407311913494593140642268659 610967870241889710963402989)
      ·
        refine ⟨229112951340708641611276121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 610967870241889710963402989 229112951340708641611276121)
        ·
          refine ⟨171834713505531481208457091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229112951340708641611276121 171834713505531481208457091)
          ·
            refine ⟨257752070258297221812685637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171834713505531481208457091 257752070258297221812685637)
            ·
              refine ⟨48328513173430729089878557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257752070258297221812685637 48328513173430729089878557)
              ·
                refine ⟨18123192440036523408704459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48328513173430729089878557 18123192440036523408704459)
                ·
                  refine ⟨27184788660054785113056689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18123192440036523408704459 27184788660054785113056689)
                  ·
                    refine ⟨20388591495041088834792517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27184788660054785113056689 20388591495041088834792517)
                    ·
                      refine ⟨3822860905320204156523597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20388591495041088834792517 3822860905320204156523597)
                      ·
                        rfl

theorem cell23_7444995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_7444995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7444995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7444995 prefixEnd_7444995 := by exact prefixLift 7444995
  have htrace : WordTrace (prefixWord ++ tailWord_7444995) baseStart_7444995 baseEnd_7444995 := by
    simpa [prefixWord, tailWord_7444995, baseEnd_7444995] using wordTrace_append hprefix tailTrace_7444995
  have hstable : (prefixWord ++ tailWord_7444995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7444995).length < 2 ^ (prefixWord ++ tailWord_7444995).sum := by decide
  have hdescent : baseEnd_7444995 < baseStart_7444995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7444995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445002 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_7445002 : Nat := 118140960795 + 7445002 * 2 ^ 59
def prefixEnd_7445002 : Nat := 4983230072969 + 3 ^ 40 * 7445002 * 2
def baseEnd_7445002 : Nat := 3822864499684785629136065

theorem tailTrace_7445002 : CollatzResearch.WordTrace tailWord_7445002 prefixEnd_7445002 3822864499684785629136065 := by
  unfold tailWord_7445002
  simp only [CollatzResearch.WordTrace]
  refine ⟨67885382743509183489254315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181027687316024489304678173 67885382743509183489254315)
  ·
    refine ⟨101828074115263775233881473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67885382743509183489254315 101828074115263775233881473)
    ·
      refine ⟨76371055586447831425411105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101828074115263775233881473 76371055586447831425411105)
      ·
        refine ⟨57278291689835873569058329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76371055586447831425411105 57278291689835873569058329)
        ·
          refine ⟨42958718767376905176793747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57278291689835873569058329 42958718767376905176793747)
          ·
            refine ⟨64438078151065357765190621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42958718767376905176793747 64438078151065357765190621)
            ·
              refine ⟨24164279306649509161946483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64438078151065357765190621 24164279306649509161946483)
              ·
                refine ⟨36246418959974263742919725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24164279306649509161946483 36246418959974263742919725)
                ·
                  refine ⟨13592407109990348903594897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36246418959974263742919725 13592407109990348903594897)
                  ·
                    refine ⟨10194305332492761677696173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13592407109990348903594897 10194305332492761677696173)
                    ·
                      refine ⟨3822864499684785629136065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10194305332492761677696173 3822864499684785629136065)
                      ·
                        rfl

theorem cell23_7445002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_7445002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445002 prefixEnd_7445002 := by exact prefixLift 7445002
  have htrace : WordTrace (prefixWord ++ tailWord_7445002) baseStart_7445002 baseEnd_7445002 := by
    simpa [prefixWord, tailWord_7445002, baseEnd_7445002] using wordTrace_append hprefix tailTrace_7445002
  have hstable : (prefixWord ++ tailWord_7445002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445002).length < 2 ^ (prefixWord ++ tailWord_7445002).sum := by decide
  have hdescent : baseEnd_7445002 < baseStart_7445002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445022 : List Nat := [4, 3, 3, 13]
def baseStart_7445022 : Nat := 118140960795 + 7445022 * 2 ^ 59
def prefixEnd_7445022 : Nat := 4983230072969 + 3 ^ 40 * 7445022 * 2
def baseEnd_7445022 : Nat := 1747999437264689323679

theorem tailTrace_7445022 : CollatzResearch.WordTrace tailWord_7445022 prefixEnd_7445022 1747999437264689323679 := by
  unfold tailWord_7445022
  simp only [CollatzResearch.WordTrace]
  refine ⟨33942782554245534671593165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181028173622642851581830213 33942782554245534671593165)
  ·
    refine ⟨12728543457842075501847437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33942782554245534671593165 12728543457842075501847437)
    ·
      refine ⟨4773203796690778313192789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12728543457842075501847437 4773203796690778313192789)
      ·
        refine ⟨1747999437264689323679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4773203796690778313192789 1747999437264689323679)
        ·
          rfl

theorem cell23_7445022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 13].length) (baseStart_7445022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445022 prefixEnd_7445022 := by exact prefixLift 7445022
  have htrace : WordTrace (prefixWord ++ tailWord_7445022) baseStart_7445022 baseEnd_7445022 := by
    simpa [prefixWord, tailWord_7445022, baseEnd_7445022] using wordTrace_append hprefix tailTrace_7445022
  have hstable : (prefixWord ++ tailWord_7445022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445022).length < 2 ^ (prefixWord ++ tailWord_7445022).sum := by decide
  have hdescent : baseEnd_7445022 < baseStart_7445022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445049 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 2, 1, 3]
def baseStart_7445049 : Nat := 118140960795 + 7445049 * 2 ^ 59
def prefixEnd_7445049 : Nat := 4983230072969 + 3 ^ 40 * 7445049 * 2
def baseEnd_7445049 : Nat := 3822888633275546945248349

theorem tailTrace_7445049 : CollatzResearch.WordTrace tailWord_7445049 prefixEnd_7445049 3822888633275546945248349 := by
  unfold tailWord_7445049
  simp only [CollatzResearch.WordTrace]
  refine ⟨271543245204866460983978201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181028830136577640655985467 271543245204866460983978201)
  ·
    refine ⟨203657433903649845737983651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271543245204866460983978201 203657433903649845737983651)
    ·
      refine ⟨305486150855474768606975477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203657433903649845737983651 305486150855474768606975477)
      ·
        refine ⟨28639326642700759556903951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 305486150855474768606975477 28639326642700759556903951)
        ·
          refine ⟨42958989964051139335355927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28639326642700759556903951 42958989964051139335355927)
          ·
            refine ⟨64438484946076709003033891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42958989964051139335355927 64438484946076709003033891)
            ·
              refine ⟨96657727419115063504550837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64438484946076709003033891 96657727419115063504550837)
              ·
                refine ⟨9061661945542037203551641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96657727419115063504550837 9061661945542037203551641)
                ·
                  refine ⟨6796246459156527902663731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9061661945542037203551641 6796246459156527902663731)
                  ·
                    refine ⟨10194369688734791853995597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6796246459156527902663731 10194369688734791853995597)
                    ·
                      refine ⟨3822888633275546945248349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10194369688734791853995597 3822888633275546945248349)
                      ·
                        rfl

theorem cell23_7445049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_7445049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445049 prefixEnd_7445049 := by exact prefixLift 7445049
  have htrace : WordTrace (prefixWord ++ tailWord_7445049) baseStart_7445049 baseEnd_7445049 := by
    simpa [prefixWord, tailWord_7445049, baseEnd_7445049] using wordTrace_append hprefix tailTrace_7445049
  have hstable : (prefixWord ++ tailWord_7445049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445049).length < 2 ^ (prefixWord ++ tailWord_7445049).sum := by decide
  have hdescent : baseEnd_7445049 < baseStart_7445049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445055 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 4]
def baseStart_7445055 : Nat := 118140960795 + 7445055 * 2 ^ 59
def prefixEnd_7445055 : Nat := 4983230072969 + 3 ^ 40 * 7445055 * 2
def baseEnd_7445055 : Nat := 3822891714159473921773321

theorem tailTrace_7445055 : CollatzResearch.WordTrace tailWord_7445055 prefixEnd_7445055 3822891714159473921773321 := by
  unfold tailWord_7445055
  simp only [CollatzResearch.WordTrace]
  refine ⟨271543464042844724008696619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181028976028563149339131079 271543464042844724008696619)
  ·
    refine ⟨407315196064267086013044929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271543464042844724008696619 407315196064267086013044929)
    ·
      refine ⟨305486397048200314509783697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407315196064267086013044929 305486397048200314509783697)
      ·
        refine ⟨229114797786150235882337773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305486397048200314509783697 229114797786150235882337773)
        ·
          refine ⟨85918049169806338455876665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229114797786150235882337773 85918049169806338455876665)
          ·
            refine ⟨64438536877354753841907499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85918049169806338455876665 64438536877354753841907499)
            ·
              refine ⟨96657805316032130762861249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64438536877354753841907499 96657805316032130762861249)
              ·
                refine ⟨72493353987024098072145937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96657805316032130762861249 72493353987024098072145937)
                ·
                  refine ⟨54370015490268073554109453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72493353987024098072145937 54370015490268073554109453)
                  ·
                    refine ⟨20388755808850527582791045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54370015490268073554109453 20388755808850527582791045)
                    ·
                      refine ⟨3822891714159473921773321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20388755808850527582791045 3822891714159473921773321)
                      ·
                        rfl

theorem cell23_7445055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_7445055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445055 prefixEnd_7445055 := by exact prefixLift 7445055
  have htrace : WordTrace (prefixWord ++ tailWord_7445055) baseStart_7445055 baseEnd_7445055 := by
    simpa [prefixWord, tailWord_7445055, baseEnd_7445055] using wordTrace_append hprefix tailTrace_7445055
  have hstable : (prefixWord ++ tailWord_7445055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445055).length < 2 ^ (prefixWord ++ tailWord_7445055).sum := by decide
  have hdescent : baseEnd_7445055 < baseStart_7445055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445072 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 3, 4, 2]
def baseStart_7445072 : Nat := 118140960795 + 7445072 * 2 ^ 59
def prefixEnd_7445072 : Nat := 4983230072969 + 3 ^ 40 * 7445072 * 2
def baseEnd_7445072 : Nat := 3822900443330600355260743

theorem tailTrace_7445072 : CollatzResearch.WordTrace tailWord_7445072 prefixEnd_7445072 3822900443330600355260743 := by
  unfold tailWord_7445072
  simp only [CollatzResearch.WordTrace]
  refine ⟨135772042041891567956032735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181029389389188757274710313 135772042041891567956032735)
  ·
    refine ⟨203658063062837351934049103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135772042041891567956032735 203658063062837351934049103)
    ·
      refine ⟨305487094594256027901073655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203658063062837351934049103 305487094594256027901073655)
      ·
        refine ⟨458230641891384041851610483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305487094594256027901073655 458230641891384041851610483)
        ·
          refine ⟨687345962837076062777415725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458230641891384041851610483 687345962837076062777415725)
          ·
            refine ⟨257754736063903523541530897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 687345962837076062777415725 257754736063903523541530897)
            ·
              refine ⟨193316052047927642656148173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257754736063903523541530897 193316052047927642656148173)
              ·
                refine ⟨72493519517972865996055565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193316052047927642656148173 72493519517972865996055565)
                ·
                  refine ⟨27185069819239824748520837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72493519517972865996055565 27185069819239824748520837)
                  ·
                    refine ⟨5097200591107467140347657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27185069819239824748520837 5097200591107467140347657)
                    ·
                      refine ⟨3822900443330600355260743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5097200591107467140347657 3822900443330600355260743)
                      ·
                        rfl

theorem cell23_7445072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 4, 2].length) (baseStart_7445072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445072 prefixEnd_7445072 := by exact prefixLift 7445072
  have htrace : WordTrace (prefixWord ++ tailWord_7445072) baseStart_7445072 baseEnd_7445072 := by
    simpa [prefixWord, tailWord_7445072, baseEnd_7445072] using wordTrace_append hprefix tailTrace_7445072
  have hstable : (prefixWord ++ tailWord_7445072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445072).length < 2 ^ (prefixWord ++ tailWord_7445072).sum := by decide
  have hdescent : baseEnd_7445072 < baseStart_7445072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445076 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_7445076 : Nat := 118140960795 + 7445076 * 2 ^ 59
def prefixEnd_7445076 : Nat := 4983230072969 + 3 ^ 40 * 7445076 * 2
def baseEnd_7445076 : Nat := 3822902497253218339610725

theorem tailTrace_7445076 : CollatzResearch.WordTrace tailWord_7445076 prefixEnd_7445076 3822902497253218339610725 := by
  unfold tailWord_7445076
  simp only [CollatzResearch.WordTrace]
  refine ⟨135772114987884322297605541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181029486650512429730140721 135772114987884322297605541)
  ·
    refine ⟨25457271560228310430801039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135772114987884322297605541 25457271560228310430801039)
    ·
      refine ⟨38185907340342465646201559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25457271560228310430801039 38185907340342465646201559)
      ·
        refine ⟨57278861010513698469302339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38185907340342465646201559 57278861010513698469302339)
        ·
          refine ⟨85918291515770547703953509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57278861010513698469302339 85918291515770547703953509)
          ·
            refine ⟨16109679659206977694491283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85918291515770547703953509 16109679659206977694491283)
            ·
              refine ⟨24164519488810466541736925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16109679659206977694491283 24164519488810466541736925)
              ·
                refine ⟨9061694808303924953151347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24164519488810466541736925 9061694808303924953151347)
                ·
                  refine ⟨13592542212455887429727021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9061694808303924953151347 13592542212455887429727021)
                  ·
                    refine ⟨5097203329670957786147633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13592542212455887429727021 5097203329670957786147633)
                    ·
                      refine ⟨3822902497253218339610725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5097203329670957786147633 3822902497253218339610725)
                      ·
                        rfl

theorem cell23_7445076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_7445076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445076 prefixEnd_7445076 := by exact prefixLift 7445076
  have htrace : WordTrace (prefixWord ++ tailWord_7445076) baseStart_7445076 baseEnd_7445076 := by
    simpa [prefixWord, tailWord_7445076, baseEnd_7445076] using wordTrace_append hprefix tailTrace_7445076
  have hstable : (prefixWord ++ tailWord_7445076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445076).length < 2 ^ (prefixWord ++ tailWord_7445076).sum := by decide
  have hdescent : baseEnd_7445076 < baseStart_7445076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445135 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_7445135 : Nat := 118140960795 + 7445135 * 2 ^ 59
def prefixEnd_7445135 : Nat := 4983230072969 + 3 ^ 40 * 7445135 * 2
def baseEnd_7445135 : Nat := 3822932792611833608772953

theorem tailTrace_7445135 : CollatzResearch.WordTrace tailWord_7445135 prefixEnd_7445135 3822932792611833608772953 := by
  unfold tailWord_7445135
  simp only [CollatzResearch.WordTrace]
  refine ⟨271546381882554897671608859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181030921255036598447739239 271546381882554897671608859)
  ·
    refine ⟨407319572823832346507413289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271546381882554897671608859 407319572823832346507413289)
    ·
      refine ⟨305489679617874259880559967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407319572823832346507413289 305489679617874259880559967)
      ·
        refine ⟨458234519426811389820839951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305489679617874259880559967 458234519426811389820839951)
        ·
          refine ⟨687351779140217084731259927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458234519426811389820839951 687351779140217084731259927)
          ·
            refine ⟨1031027668710325627096889891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687351779140217084731259927 1031027668710325627096889891)
            ·
              refine ⟨1546541503065488440645334837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031027668710325627096889891 1546541503065488440645334837)
              ·
                refine ⟨144988265912389541310500141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1546541503065488440645334837 144988265912389541310500141)
                ·
                  refine ⟨54370599717146077991437553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144988265912389541310500141 54370599717146077991437553)
                  ·
                    refine ⟨40777949787859558493578165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54370599717146077991437553 40777949787859558493578165)
                    ·
                      refine ⟨3822932792611833608772953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40777949787859558493578165 3822932792611833608772953)
                      ·
                        rfl

theorem cell23_7445135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_7445135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445135 prefixEnd_7445135 := by exact prefixLift 7445135
  have htrace : WordTrace (prefixWord ++ tailWord_7445135) baseStart_7445135 baseEnd_7445135 := by
    simpa [prefixWord, tailWord_7445135, baseEnd_7445135] using wordTrace_append hprefix tailTrace_7445135
  have hstable : (prefixWord ++ tailWord_7445135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445135).length < 2 ^ (prefixWord ++ tailWord_7445135).sum := by decide
  have hdescent : baseEnd_7445135 < baseStart_7445135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445146 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 7]
def baseStart_7445146 : Nat := 118140960795 + 7445146 * 2 ^ 59
def prefixEnd_7445146 : Nat := 4983230072969 + 3 ^ 40 * 7445146 * 2
def baseEnd_7445146 : Nat := 424770937877670340637267

theorem tailTrace_7445146 : CollatzResearch.WordTrace tailWord_7445146 prefixEnd_7445146 424770937877670340637267 := by
  unfold tailWord_7445146
  simp only [CollatzResearch.WordTrace]
  refine ⟨67886695771378761637564823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181031188723676697700172861 67886695771378761637564823)
  ·
    refine ⟨101830043657068142456347235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67886695771378761637564823 101830043657068142456347235)
    ·
      refine ⟨152745065485602213684520853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101830043657068142456347235 152745065485602213684520853)
      ·
        refine ⟨7159924944637603766461915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152745065485602213684520853 7159924944637603766461915)
        ·
          refine ⟨10739887416956405649692873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7159924944637603766461915 10739887416956405649692873)
          ·
            refine ⟨8054915562717304237269655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10739887416956405649692873 8054915562717304237269655)
            ·
              refine ⟨12082373344075956355904483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8054915562717304237269655 12082373344075956355904483)
              ·
                refine ⟨18123560016113934533856725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12082373344075956355904483 18123560016113934533856725)
                ·
                  refine ⟨424770937877670340637267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18123560016113934533856725 424770937877670340637267)
                  ·
                    rfl

theorem cell23_7445146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_7445146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445146 prefixEnd_7445146 := by exact prefixLift 7445146
  have htrace : WordTrace (prefixWord ++ tailWord_7445146) baseStart_7445146 baseEnd_7445146 := by
    simpa [prefixWord, tailWord_7445146, baseEnd_7445146] using wordTrace_append hprefix tailTrace_7445146
  have hstable : (prefixWord ++ tailWord_7445146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445146).length < 2 ^ (prefixWord ++ tailWord_7445146).sum := by decide
  have hdescent : baseEnd_7445146 < baseStart_7445146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445155 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 2, 8]
def baseStart_7445155 : Nat := 118140960795 + 7445155 * 2 ^ 59
def prefixEnd_7445155 : Nat := 4983230072969 + 3 ^ 40 * 7445155 * 2
def baseEnd_7445155 : Nat := 1274314354074974510174287

theorem tailTrace_7445155 : CollatzResearch.WordTrace tailWord_7445155 prefixEnd_7445155 1274314354074974510174287 := by
  unfold tailWord_7445155
  simp only [CollatzResearch.WordTrace]
  refine ⟨271547111342482441087336919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181031407561654960724891279 271547111342482441087336919)
  ·
    refine ⟨407320667013723661631005379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271547111342482441087336919 407320667013723661631005379)
    ·
      refine ⟨610981000520585492446508069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407320667013723661631005379 610981000520585492446508069)
      ·
        refine ⟨114558937597609779833720263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 610981000520585492446508069 114558937597609779833720263)
        ·
          refine ⟨171838406396414669750580395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114558937597609779833720263 171838406396414669750580395)
          ·
            refine ⟨257757609594622004625870593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171838406396414669750580395 257757609594622004625870593)
            ·
              refine ⟨193318207195966503469402945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257757609594622004625870593 193318207195966503469402945)
              ·
                refine ⟨144988655396974877602052209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193318207195966503469402945 144988655396974877602052209)
                ·
                  refine ⟨108741491547731158201539157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144988655396974877602052209 108741491547731158201539157)
                  ·
                    refine ⟨1274314354074974510174287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108741491547731158201539157 1274314354074974510174287)
                    ·
                      rfl

theorem cell23_7445155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 8].length) (baseStart_7445155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445155 prefixEnd_7445155 := by exact prefixLift 7445155
  have htrace : WordTrace (prefixWord ++ tailWord_7445155) baseStart_7445155 baseEnd_7445155 := by
    simpa [prefixWord, tailWord_7445155, baseEnd_7445155] using wordTrace_append hprefix tailTrace_7445155
  have hstable : (prefixWord ++ tailWord_7445155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445155).length < 2 ^ (prefixWord ++ tailWord_7445155).sum := by decide
  have hdescent : baseEnd_7445155 < baseStart_7445155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445197 : List Nat := [1, 6, 2, 1, 3, 1, 2, 2, 5]
def baseStart_7445197 : Nat := 118140960795 + 7445197 * 2 ^ 59
def prefixEnd_7445197 : Nat := 4983230072969 + 3 ^ 40 * 7445197 * 2
def baseEnd_7445197 : Nat := 424773847601379151799741

theorem tailTrace_7445197 : CollatzResearch.WordTrace tailWord_7445197 prefixEnd_7445197 424773847601379151799741 := by
  unfold tailWord_7445197
  simp only [CollatzResearch.WordTrace]
  refine ⟨271548643208330282260365845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181032428805553521506910563 271548643208330282260365845)
  ·
    refine ⟨12728842650390481980954649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 271548643208330282260365845 12728842650390481980954649)
    ·
      refine ⟨9546631987792861485715987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12728842650390481980954649 9546631987792861485715987)
      ·
        refine ⟨14319947981689292228573981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9546631987792861485715987 14319947981689292228573981)
        ·
          refine ⟨5369980493133484585715243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14319947981689292228573981 5369980493133484585715243)
          ·
            refine ⟨8054970739700226878572865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5369980493133484585715243 8054970739700226878572865)
            ·
              refine ⟨6041228054775170158929649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8054970739700226878572865 6041228054775170158929649)
              ·
                refine ⟨4530921041081377619197237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6041228054775170158929649 4530921041081377619197237)
                ·
                  refine ⟨424773847601379151799741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4530921041081377619197237 424773847601379151799741)
                  ·
                    rfl

theorem cell23_7445197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_7445197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445197 prefixEnd_7445197 := by exact prefixLift 7445197
  have htrace : WordTrace (prefixWord ++ tailWord_7445197) baseStart_7445197 baseEnd_7445197 := by
    simpa [prefixWord, tailWord_7445197, baseEnd_7445197] using wordTrace_append hprefix tailTrace_7445197
  have hstable : (prefixWord ++ tailWord_7445197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445197).length < 2 ^ (prefixWord ++ tailWord_7445197).sum := by decide
  have hdescent : baseEnd_7445197 < baseStart_7445197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445219 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 6]
def baseStart_7445219 : Nat := 118140960795 + 7445219 * 2 ^ 59
def prefixEnd_7445219 : Nat := 4983230072969 + 3 ^ 40 * 7445219 * 2
def baseEnd_7445219 : Nat := 424775102776312364458063

theorem tailTrace_7445219 : CollatzResearch.WordTrace tailWord_7445219 prefixEnd_7445219 424775102776312364458063 := by
  unfold tailWord_7445219
  simp only [CollatzResearch.WordTrace]
  refine ⟨271549445614250580017666711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181032963742833720011777807 271549445614250580017666711)
  ·
    refine ⟨407324168421375870026500067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271549445614250580017666711 407324168421375870026500067)
    ·
      refine ⟨610986252632063805039750101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407324168421375870026500067 610986252632063805039750101)
      ·
        refine ⟨14319990296063995430619143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 610986252632063805039750101 14319990296063995430619143)
        ·
          refine ⟨21479985444095993145928715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14319990296063995430619143 21479985444095993145928715)
          ·
            refine ⟨32219978166143989718893073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21479985444095993145928715 32219978166143989718893073)
            ·
              refine ⟨24164983624607992289169805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32219978166143989718893073 24164983624607992289169805)
              ·
                refine ⟨9061868859227997108438677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24164983624607992289169805 9061868859227997108438677)
                ·
                  refine ⟨424775102776312364458063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9061868859227997108438677 424775102776312364458063)
                  ·
                    rfl

theorem cell23_7445219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 6].length) (baseStart_7445219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445219 prefixEnd_7445219 := by exact prefixLift 7445219
  have htrace : WordTrace (prefixWord ++ tailWord_7445219) baseStart_7445219 baseEnd_7445219 := by
    simpa [prefixWord, tailWord_7445219, baseEnd_7445219] using wordTrace_append hprefix tailTrace_7445219
  have hstable : (prefixWord ++ tailWord_7445219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445219).length < 2 ^ (prefixWord ++ tailWord_7445219).sum := by decide
  have hdescent : baseEnd_7445219 < baseStart_7445219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445232 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 3, 5]
def baseStart_7445232 : Nat := 118140960795 + 7445232 * 2 ^ 59
def prefixEnd_7445232 : Nat := 4983230072969 + 3 ^ 40 * 7445232 * 2
def baseEnd_7445232 : Nat := 1274327533411773243086669

theorem tailTrace_7445232 : CollatzResearch.WordTrace tailWord_7445232 prefixEnd_7445232 1274327533411773243086669 := by
  unfold tailWord_7445232
  simp only [CollatzResearch.WordTrace]
  refine ⟨135774959881601741618944975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181033279842135655491926633 135774959881601741618944975)
  ·
    refine ⟨203662439822402612428417463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135774959881601741618944975 203662439822402612428417463)
    ·
      refine ⟨305493659733603918642626195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203662439822402612428417463 305493659733603918642626195)
      ·
        refine ⟨458240489600405877963939293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305493659733603918642626195 458240489600405877963939293)
        ·
          refine ⟨171840183600152204236477235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458240489600405877963939293 171840183600152204236477235)
          ·
            refine ⟨257760275400228306354715853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171840183600152204236477235 257760275400228306354715853)
            ·
              refine ⟨96660103275085614883018445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257760275400228306354715853 96660103275085614883018445)
              ·
                refine ⟨36247538728157105581131917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96660103275085614883018445 36247538728157105581131917)
                ·
                  refine ⟨13592827023058914592924469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36247538728157105581131917 13592827023058914592924469)
                  ·
                    refine ⟨1274327533411773243086669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13592827023058914592924469 1274327533411773243086669)
                    ·
                      rfl

theorem cell23_7445232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_7445232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445232 prefixEnd_7445232 := by exact prefixLift 7445232
  have htrace : WordTrace (prefixWord ++ tailWord_7445232) baseStart_7445232 baseEnd_7445232 := by
    simpa [prefixWord, tailWord_7445232, baseEnd_7445232] using wordTrace_append hprefix tailTrace_7445232
  have hstable : (prefixWord ++ tailWord_7445232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445232).length < 2 ^ (prefixWord ++ tailWord_7445232).sum := by decide
  have hdescent : baseEnd_7445232 < baseStart_7445232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445279 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 1, 6]
def baseStart_7445279 : Nat := 118140960795 + 7445279 * 2 ^ 59
def prefixEnd_7445279 : Nat := 4983230072969 + 3 ^ 40 * 7445279 * 2
def baseEnd_7445279 : Nat := 1274335577942027015124097

theorem tailTrace_7445279 : CollatzResearch.WordTrace tailWord_7445279 prefixEnd_7445279 1274335577942027015124097 := by
  unfold tailWord_7445279
  simp only [CollatzResearch.WordTrace]
  refine ⟨271551633994033210264850891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181034422662688806843233927 271551633994033210264850891)
  ·
    refine ⟨407327450991049815397276337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271551633994033210264850891 407327450991049815397276337)
    ·
      refine ⟨305495588243287361547957253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407327450991049815397276337 305495588243287361547957253)
      ·
        refine ⟨57280422795616380290241985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305495588243287361547957253 57280422795616380290241985)
        ·
          refine ⟨42960317096712285217681489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57280422795616380290241985 42960317096712285217681489)
          ·
            refine ⟨32220237822534213913261117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42960317096712285217681489 32220237822534213913261117)
            ·
              refine ⟨12082589183450330217472919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32220237822534213913261117 12082589183450330217472919)
              ·
                refine ⟨18123883775175495326209379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12082589183450330217472919 18123883775175495326209379)
                ·
                  refine ⟨27185825662763242989314069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18123883775175495326209379 27185825662763242989314069)
                  ·
                    refine ⟨1274335577942027015124097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27185825662763242989314069 1274335577942027015124097)
                    ·
                      rfl

theorem cell23_7445279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 6].length) (baseStart_7445279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445279 prefixEnd_7445279 := by exact prefixLift 7445279
  have htrace : WordTrace (prefixWord ++ tailWord_7445279) baseStart_7445279 baseEnd_7445279 := by
    simpa [prefixWord, tailWord_7445279, baseEnd_7445279] using wordTrace_append hprefix tailTrace_7445279
  have hstable : (prefixWord ++ tailWord_7445279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445279).length < 2 ^ (prefixWord ++ tailWord_7445279).sum := by decide
  have hdescent : baseEnd_7445279 < baseStart_7445279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445292 : List Nat := [2, 2, 1, 1, 1, 4, 3, 9]
def baseStart_7445292 : Nat := 118140960795 + 7445292 * 2 ^ 59
def prefixEnd_7445292 : Nat := 4983230072969 + 3 ^ 40 * 7445292 * 2
def baseEnd_7445292 : Nat := 141593089224984796092953

theorem tailTrace_7445292 : CollatzResearch.WordTrace tailWord_7445292 prefixEnd_7445292 141593089224984796092953 := by
  unfold tailWord_7445292
  simp only [CollatzResearch.WordTrace]
  refine ⟨135776054071493056742537065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181034738761990742323382753 135776054071493056742537065)
  ·
    refine ⟨101832040553619792556902799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135776054071493056742537065 101832040553619792556902799)
    ·
      refine ⟨152748060830429688835354199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101832040553619792556902799 152748060830429688835354199)
      ·
        refine ⟨229122091245644533253031299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152748060830429688835354199 229122091245644533253031299)
        ·
          refine ⟨343683136868466799879546949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229122091245644533253031299 343683136868466799879546949)
          ·
            refine ⟨64440588162837524977415053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343683136868466799879546949 64440588162837524977415053)
            ·
              refine ⟨24165220561064071866530645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64440588162837524977415053 24165220561064071866530645)
              ·
                refine ⟨141593089224984796092953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24165220561064071866530645 141593089224984796092953)
                ·
                  rfl

theorem cell23_7445292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 9].length) (baseStart_7445292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445292 prefixEnd_7445292 := by exact prefixLift 7445292
  have htrace : WordTrace (prefixWord ++ tailWord_7445292) baseStart_7445292 baseEnd_7445292 := by
    simpa [prefixWord, tailWord_7445292, baseEnd_7445292] using wordTrace_append hprefix tailTrace_7445292
  have hstable : (prefixWord ++ tailWord_7445292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445292).length < 2 ^ (prefixWord ++ tailWord_7445292).sum := by decide
  have hdescent : baseEnd_7445292 < baseStart_7445292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445306 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5]
def baseStart_7445306 : Nat := 118140960795 + 7445306 * 2 ^ 59
def prefixEnd_7445306 : Nat := 4983230072969 + 3 ^ 40 * 7445306 * 2
def baseEnd_7445306 : Nat := 3823020597803752439734667

theorem tailTrace_7445306 : CollatzResearch.WordTrace tailWord_7445306 prefixEnd_7445306 3823020597803752439734667 := by
  unfold tailWord_7445306
  simp only [CollatzResearch.WordTrace]
  refine ⟨67888154691233848469020943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181035079176623595917389181 67888154691233848469020943)
  ·
    refine ⟨101832232036850772703531415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67888154691233848469020943 101832232036850772703531415)
    ·
      refine ⟨152748348055276159055297123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101832232036850772703531415 152748348055276159055297123)
      ·
        refine ⟨229122522082914238582945685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152748348055276159055297123 229122522082914238582945685)
        ·
          refine ⟨10740118222636604933575579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 229122522082914238582945685 10740118222636604933575579)
          ·
            refine ⟨16110177333954907400363369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10740118222636604933575579 16110177333954907400363369)
            ·
              refine ⟨12082633000466180550272527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16110177333954907400363369 12082633000466180550272527)
              ·
                refine ⟨18123949500699270825408791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12082633000466180550272527 18123949500699270825408791)
                ·
                  refine ⟨27185924251048906238113187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18123949500699270825408791 27185924251048906238113187)
                  ·
                    refine ⟨40778886376573359357169781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27185924251048906238113187 40778886376573359357169781)
                    ·
                      refine ⟨3823020597803752439734667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40778886376573359357169781 3823020597803752439734667)
                      ·
                        rfl

theorem cell23_7445306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_7445306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445306 prefixEnd_7445306 := by exact prefixLift 7445306
  have htrace : WordTrace (prefixWord ++ tailWord_7445306) baseStart_7445306 baseEnd_7445306 := by
    simpa [prefixWord, tailWord_7445306, baseEnd_7445306] using wordTrace_append hprefix tailTrace_7445306
  have hstable : (prefixWord ++ tailWord_7445306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445306).length < 2 ^ (prefixWord ++ tailWord_7445306).sum := by decide
  have hdescent : baseEnd_7445306 < baseStart_7445306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445340 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_7445340 : Nat := 118140960795 + 7445340 * 2 ^ 59
def prefixEnd_7445340 : Nat := 4983230072969 + 3 ^ 40 * 7445340 * 2
def baseEnd_7445340 : Nat := 3823038056146005306709511

theorem tailTrace_7445340 : CollatzResearch.WordTrace tailWord_7445340 prefixEnd_7445340 3823038056146005306709511 := by
  unfold tailWord_7445340
  simp only [CollatzResearch.WordTrace]
  refine ⟨135776929423406108841410737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181035905897874811788547649 135776929423406108841410737)
  ·
    refine ⟨101832697067554581631058053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135776929423406108841410737 101832697067554581631058053)
    ·
      refine ⟨19093630700166484055823385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101832697067554581631058053 19093630700166484055823385)
      ·
        refine ⟨14320223025124863041867539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19093630700166484055823385 14320223025124863041867539)
        ·
          refine ⟨21480334537687294562801309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14320223025124863041867539 21480334537687294562801309)
          ·
            refine ⟨8055125451632735461050491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21480334537687294562801309 8055125451632735461050491)
            ·
              refine ⟨12082688177449103191575737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8055125451632735461050491 12082688177449103191575737)
              ·
                refine ⟨9062016133086827393681803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12082688177449103191575737 9062016133086827393681803)
                ·
                  refine ⟨13593024199630241090522705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9062016133086827393681803 13593024199630241090522705)
                  ·
                    refine ⟨10194768149722680817892029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13593024199630241090522705 10194768149722680817892029)
                    ·
                      refine ⟨3823038056146005306709511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10194768149722680817892029 3823038056146005306709511)
                      ·
                        rfl

theorem cell23_7445340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_7445340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445340 prefixEnd_7445340 := by exact prefixLift 7445340
  have htrace : WordTrace (prefixWord ++ tailWord_7445340) baseStart_7445340 baseEnd_7445340 := by
    simpa [prefixWord, tailWord_7445340, baseEnd_7445340] using wordTrace_append hprefix tailTrace_7445340
  have hstable : (prefixWord ++ tailWord_7445340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445340).length < 2 ^ (prefixWord ++ tailWord_7445340).sum := by decide
  have hdescent : baseEnd_7445340 < baseStart_7445340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445379 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 3]
def baseStart_7445379 : Nat := 118140960795 + 7445379 * 2 ^ 59
def prefixEnd_7445379 : Nat := 4983230072969 + 3 ^ 40 * 7445379 * 2
def baseEnd_7445379 : Nat := 3823058081891530654121831

theorem tailTrace_7445379 : CollatzResearch.WordTrace tailWord_7445379 prefixEnd_7445379 3823058081891530654121831 := by
  unfold tailWord_7445379
  simp only [CollatzResearch.WordTrace]
  refine ⟨271555281293670927343491191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181036854195780618228994127 271555281293670927343491191)
  ·
    refine ⟨407332921940506391015236787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271555281293670927343491191 407332921940506391015236787)
    ·
      refine ⟨610999382910759586522855181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407332921940506391015236787 610999382910759586522855181)
      ·
        refine ⟨229124768591534844946070693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 610999382910759586522855181 229124768591534844946070693)
        ·
          refine ⟨42960894110912783427388255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229124768591534844946070693 42960894110912783427388255)
          ·
            refine ⟨64441341166369175141082383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42960894110912783427388255 64441341166369175141082383)
            ·
              refine ⟨96662011749553762711623575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64441341166369175141082383 96662011749553762711623575)
              ·
                refine ⟨144993017624330644067435363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96662011749553762711623575 144993017624330644067435363)
                ·
                  refine ⟨217489526436495966101153045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144993017624330644067435363 217489526436495966101153045)
                  ·
                    refine ⟨10194821551710748410991549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 217489526436495966101153045 10194821551710748410991549)
                    ·
                      refine ⟨3823058081891530654121831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10194821551710748410991549 3823058081891530654121831)
                      ·
                        rfl

theorem cell23_7445379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_7445379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445379 prefixEnd_7445379 := by exact prefixLift 7445379
  have htrace : WordTrace (prefixWord ++ tailWord_7445379) baseStart_7445379 baseEnd_7445379 := by
    simpa [prefixWord, tailWord_7445379, baseEnd_7445379] using wordTrace_append hprefix tailTrace_7445379
  have hstable : (prefixWord ++ tailWord_7445379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445379).length < 2 ^ (prefixWord ++ tailWord_7445379).sum := by decide
  have hdescent : baseEnd_7445379 < baseStart_7445379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445386 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_7445386 : Nat := 118140960795 + 7445386 * 2 ^ 59
def prefixEnd_7445386 : Nat := 4983230072969 + 3 ^ 40 * 7445386 * 2
def baseEnd_7445386 : Nat := 1274353892085370708911433

theorem tailTrace_7445386 : CollatzResearch.WordTrace tailWord_7445386 prefixEnd_7445386 1274353892085370708911433 := by
  unfold tailWord_7445386
  simp only [CollatzResearch.WordTrace]
  refine ⟨67888884151161391884749003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181037024403097045025997341 67888884151161391884749003)
  ·
    refine ⟨101833326226742087827123505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67888884151161391884749003 101833326226742087827123505)
    ·
      refine ⟨76374994670056565870342629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101833326226742087827123505 76374994670056565870342629)
      ·
        refine ⟨14320311500635606100689243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76374994670056565870342629 14320311500635606100689243)
        ·
          refine ⟨21480467250953409151033865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14320311500635606100689243 21480467250953409151033865)
          ·
            refine ⟨16110350438215056863275399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21480467250953409151033865 16110350438215056863275399)
            ·
              refine ⟨24165525657322585294913099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16110350438215056863275399 24165525657322585294913099)
              ·
                refine ⟨36248288485983877942369649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24165525657322585294913099 36248288485983877942369649)
                ·
                  refine ⟨27186216364487908456777237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36248288485983877942369649 27186216364487908456777237)
                  ·
                    refine ⟨1274353892085370708911433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27186216364487908456777237 1274353892085370708911433)
                    ·
                      rfl

theorem cell23_7445386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_7445386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445386 prefixEnd_7445386 := by exact prefixLift 7445386
  have htrace : WordTrace (prefixWord ++ tailWord_7445386) baseStart_7445386 baseEnd_7445386 := by
    simpa [prefixWord, tailWord_7445386, baseEnd_7445386] using wordTrace_append hprefix tailTrace_7445386
  have hstable : (prefixWord ++ tailWord_7445386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445386).length < 2 ^ (prefixWord ++ tailWord_7445386).sum := by decide
  have hdescent : baseEnd_7445386 < baseStart_7445386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445396 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_7445396 : Nat := 118140960795 + 7445396 * 2 ^ 59
def prefixEnd_7445396 : Nat := 4983230072969 + 3 ^ 40 * 7445396 * 2
def baseEnd_7445396 : Nat := 3823066811062657087609253

theorem tailTrace_7445396 : CollatzResearch.WordTrace tailWord_7445396 prefixEnd_7445396 3823066811062657087609253 := by
  unfold tailWord_7445396
  simp only [CollatzResearch.WordTrace]
  refine ⟨135777950667304669623430021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181037267556406226164573361 135777950667304669623430021)
  ·
    refine ⟨25458365750119625554393129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135777950667304669623430021 25458365750119625554393129)
    ·
      refine ⟨19093774312589719165794847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25458365750119625554393129 19093774312589719165794847)
      ·
        refine ⟨28640661468884578748692271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19093774312589719165794847 28640661468884578748692271)
        ·
          refine ⟨42960992203326868123038407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28640661468884578748692271 42960992203326868123038407)
          ·
            refine ⟨64441488304990302184557611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42960992203326868123038407 64441488304990302184557611)
            ·
              refine ⟨96662232457485453276836417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64441488304990302184557611 96662232457485453276836417)
              ·
                refine ⟨72496674343114089957627313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96662232457485453276836417 72496674343114089957627313)
                ·
                  refine ⟨54372505757335567468220485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72496674343114089957627313 54372505757335567468220485)
                  ·
                    refine ⟨10194844829500418900291341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54372505757335567468220485 10194844829500418900291341)
                    ·
                      refine ⟨3823066811062657087609253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10194844829500418900291341 3823066811062657087609253)
                      ·
                        rfl

theorem cell23_7445396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_7445396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445396 prefixEnd_7445396 := by exact prefixLift 7445396
  have htrace : WordTrace (prefixWord ++ tailWord_7445396) baseStart_7445396 baseEnd_7445396 := by
    simpa [prefixWord, tailWord_7445396, baseEnd_7445396] using wordTrace_append hprefix tailTrace_7445396
  have hstable : (prefixWord ++ tailWord_7445396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445396).length < 2 ^ (prefixWord ++ tailWord_7445396).sum := by decide
  have hdescent : baseEnd_7445396 < baseStart_7445396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445399 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 7]
def baseStart_7445399 : Nat := 118140960795 + 7445399 * 2 ^ 59
def prefixEnd_7445399 : Nat := 4983230072969 + 3 ^ 40 * 7445399 * 2
def baseEnd_7445399 : Nat := 424785372389402286207971

theorem tailTrace_7445399 : CollatzResearch.WordTrace tailWord_7445399 prefixEnd_7445399 424785372389402286207971 := by
  unfold tailWord_7445399
  simp only [CollatzResearch.WordTrace]
  refine ⟨271556010753598470759219251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181037340502398980506146167 271556010753598470759219251)
  ·
    refine ⟨407334016130397706138828877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271556010753598470759219251 407334016130397706138828877)
    ·
      refine ⟨152750256048899139802060829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407334016130397706138828877 152750256048899139802060829)
      ·
        refine ⟨57281346018337177425772811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152750256048899139802060829 57281346018337177425772811)
        ·
          refine ⟨85922019027505766138659217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57281346018337177425772811 85922019027505766138659217)
          ·
            refine ⟨64441514270629324603994413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85922019027505766138659217 64441514270629324603994413)
            ·
              refine ⟨24165567851485996726497905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64441514270629324603994413 24165567851485996726497905)
              ·
                refine ⟨18124175888614497544873429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24165567851485996726497905 18124175888614497544873429)
                ·
                  refine ⟨424785372389402286207971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18124175888614497544873429 424785372389402286207971)
                  ·
                    rfl

theorem cell23_7445399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 7].length) (baseStart_7445399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445399 prefixEnd_7445399 := by exact prefixLift 7445399
  have htrace : WordTrace (prefixWord ++ tailWord_7445399) baseStart_7445399 baseEnd_7445399 := by
    simpa [prefixWord, tailWord_7445399, baseEnd_7445399] using wordTrace_append hprefix tailTrace_7445399
  have hstable : (prefixWord ++ tailWord_7445399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445399).length < 2 ^ (prefixWord ++ tailWord_7445399).sum := by decide
  have hdescent : baseEnd_7445399 < baseStart_7445399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445444 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_7445444 : Nat := 118140960795 + 7445444 * 2 ^ 59
def prefixEnd_7445444 : Nat := 4983230072969 + 3 ^ 40 * 7445444 * 2
def baseEnd_7445444 : Nat := 3823091458134072899809033

theorem tailTrace_7445444 : CollatzResearch.WordTrace tailWord_7445444 prefixEnd_7445444 3823091458134072899809033 := by
  unfold tailWord_7445444
  simp only [CollatzResearch.WordTrace]
  refine ⟨135778826019217721722303693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181038434692290295629738257 135778826019217721722303693)
  ·
    refine ⟨50917059757206645645863885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135778826019217721722303693 50917059757206645645863885)
    ·
      refine ⟨19093897408952492117198957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50917059757206645645863885 19093897408952492117198957)
      ·
        refine ⟨7160211528357184543949609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19093897408952492117198957 7160211528357184543949609)
        ·
          refine ⟨5370158646267888407962207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7160211528357184543949609 5370158646267888407962207)
          ·
            refine ⟨8055237969401832611943311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5370158646267888407962207 8055237969401832611943311)
            ·
              refine ⟨12082856954102748917914967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8055237969401832611943311 12082856954102748917914967)
              ·
                refine ⟨18124285431154123376872451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12082856954102748917914967 18124285431154123376872451)
                ·
                  refine ⟨27186428146731185065308677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18124285431154123376872451 27186428146731185065308677)
                  ·
                    refine ⟨5097455277512097199745377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27186428146731185065308677 5097455277512097199745377)
                    ·
                      refine ⟨3823091458134072899809033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5097455277512097199745377 3823091458134072899809033)
                      ·
                        rfl

theorem cell23_7445444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_7445444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445444 prefixEnd_7445444 := by exact prefixLift 7445444
  have htrace : WordTrace (prefixWord ++ tailWord_7445444) baseStart_7445444 baseEnd_7445444 := by
    simpa [prefixWord, tailWord_7445444, baseEnd_7445444] using wordTrace_append hprefix tailTrace_7445444
  have hstable : (prefixWord ++ tailWord_7445444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445444).length < 2 ^ (prefixWord ++ tailWord_7445444).sum := by decide
  have hdescent : baseEnd_7445444 < baseStart_7445444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445466 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_7445466 : Nat := 118140960795 + 7445466 * 2 ^ 59
def prefixEnd_7445466 : Nat := 4983230072969 + 3 ^ 40 * 7445466 * 2
def baseEnd_7445466 : Nat := 3823102754708471813733931

theorem tailTrace_7445466 : CollatzResearch.WordTrace tailWord_7445466 prefixEnd_7445466 3823102754708471813733931 := by
  unfold tailWord_7445466
  simp only [CollatzResearch.WordTrace]
  refine ⟨67889613611088935300477063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181038969629570494134605501 67889613611088935300477063)
  ·
    refine ⟨101834420416633402950715595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67889613611088935300477063 101834420416633402950715595)
    ·
      refine ⟨152751630624950104426073393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101834420416633402950715595 152751630624950104426073393)
      ·
        refine ⟨114563722968712578319555045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152751630624950104426073393 114563722968712578319555045)
        ·
          refine ⟨21480698056633608434916571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114563722968712578319555045 21480698056633608434916571)
          ·
            refine ⟨32221047084950412652374857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21480698056633608434916571 32221047084950412652374857)
            ·
              refine ⟨24165785313712809489281143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32221047084950412652374857 24165785313712809489281143)
              ·
                refine ⟨36248677970569214233921715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24165785313712809489281143 36248677970569214233921715)
                ·
                  refine ⟨54373016955853821350882573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36248677970569214233921715 54373016955853821350882573)
                  ·
                    refine ⟨20389881358445183006580965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54373016955853821350882573 20389881358445183006580965)
                    ·
                      refine ⟨3823102754708471813733931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20389881358445183006580965 3823102754708471813733931)
                      ·
                        rfl

theorem cell23_7445466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_7445466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445466 prefixEnd_7445466 := by exact prefixLift 7445466
  have htrace : WordTrace (prefixWord ++ tailWord_7445466) baseStart_7445466 baseEnd_7445466 := by
    simpa [prefixWord, tailWord_7445466, baseEnd_7445466] using wordTrace_append hprefix tailTrace_7445466
  have hstable : (prefixWord ++ tailWord_7445466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445466).length < 2 ^ (prefixWord ++ tailWord_7445466).sum := by decide
  have hdescent : baseEnd_7445466 < baseStart_7445466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445550 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_7445550 : Nat := 118140960795 + 7445550 * 2 ^ 59
def prefixEnd_7445550 : Nat := 4983230072969 + 3 ^ 40 * 7445550 * 2
def baseEnd_7445550 : Nat := 3823145887083449485083545

theorem tailTrace_7445550 : CollatzResearch.WordTrace tailWord_7445550 prefixEnd_7445550 3823145887083449485083545 := by
  unfold tailWord_7445550
  simp only [CollatzResearch.WordTrace]
  refine ⟨33945189772006427943495763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181041012117367615698644069 33945189772006427943495763)
  ·
    refine ⟨50917784658009641915243645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33945189772006427943495763 50917784658009641915243645)
    ·
      refine ⟨19094169246753615718216367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50917784658009641915243645 19094169246753615718216367)
      ·
        refine ⟨28641253870130423577324551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19094169246753615718216367 28641253870130423577324551)
        ·
          refine ⟨42961880805195635365986827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28641253870130423577324551 42961880805195635365986827)
          ·
            refine ⟨64442821207793453048980241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42961880805195635365986827 64442821207793453048980241)
            ·
              refine ⟨48332115905845089786735181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64442821207793453048980241 48332115905845089786735181)
              ·
                refine ⟨18124543464691908670025693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48332115905845089786735181 18124543464691908670025693)
                ·
                  refine ⟨6796703799259465751259635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18124543464691908670025693 6796703799259465751259635)
                  ·
                    refine ⟨10195055698889198626889453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6796703799259465751259635 10195055698889198626889453)
                    ·
                      refine ⟨3823145887083449485083545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10195055698889198626889453 3823145887083449485083545)
                      ·
                        rfl

theorem cell23_7445550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_7445550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445550 prefixEnd_7445550 := by exact prefixLift 7445550
  have htrace : WordTrace (prefixWord ++ tailWord_7445550) baseStart_7445550 baseEnd_7445550 := by
    simpa [prefixWord, tailWord_7445550, baseEnd_7445550] using wordTrace_append hprefix tailTrace_7445550
  have hstable : (prefixWord ++ tailWord_7445550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445550).length < 2 ^ (prefixWord ++ tailWord_7445550).sum := by decide
  have hdescent : baseEnd_7445550 < baseStart_7445550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445596 : List Nat := [2, 2, 4, 1, 1, 1, 12]
def baseStart_7445596 : Nat := 118140960795 + 7445596 * 2 ^ 59
def prefixEnd_7445596 : Nat := 4983230072969 + 3 ^ 40 * 7445596 * 2
def baseEnd_7445596 : Nat := 47199623545599460556893

theorem tailTrace_7445596 : CollatzResearch.WordTrace tailWord_7445596 prefixEnd_7445596 47199623545599460556893 := by
  unfold tailWord_7445596
  simp only [CollatzResearch.WordTrace]
  refine ⟨135781597966942386702070321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181042130622589848936093761 135781597966942386702070321)
  ·
    refine ⟨101836198475206790026552741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135781597966942386702070321 101836198475206790026552741)
    ·
      refine ⟨19094287214101273129978639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101836198475206790026552741 19094287214101273129978639)
      ·
        refine ⟨28641430821151909694967959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19094287214101273129978639 28641430821151909694967959)
        ·
          refine ⟨42962146231727864542451939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28641430821151909694967959 42962146231727864542451939)
          ·
            refine ⟨64443219347591796813677909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42962146231727864542451939 64443219347591796813677909)
            ·
              refine ⟨47199623545599460556893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 64443219347591796813677909 47199623545599460556893)
              ·
                rfl

theorem cell23_7445596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 12].length) (baseStart_7445596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445596 prefixEnd_7445596 := by exact prefixLift 7445596
  have htrace : WordTrace (prefixWord ++ tailWord_7445596) baseStart_7445596 baseEnd_7445596 := by
    simpa [prefixWord, tailWord_7445596, baseEnd_7445596] using wordTrace_append hprefix tailTrace_7445596
  have hstable : (prefixWord ++ tailWord_7445596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445596).length < 2 ^ (prefixWord ++ tailWord_7445596).sum := by decide
  have hdescent : baseEnd_7445596 < baseStart_7445596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445607 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_7445607 : Nat := 118140960795 + 7445607 * 2 ^ 59
def prefixEnd_7445607 : Nat := 4983230072969 + 3 ^ 40 * 7445607 * 2
def baseEnd_7445607 : Nat := 3823175155480755762070783

theorem tailTrace_7445607 : CollatzResearch.WordTrace tailWord_7445607 prefixEnd_7445607 3823175155480755762070783 := by
  unfold tailWord_7445607
  simp only [CollatzResearch.WordTrace]
  refine ⟨271563597136844922282791075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181042398091229948188527383 271563597136844922282791075)
  ·
    refine ⟨407345395705267383424186613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271563597136844922282791075 407345395705267383424186613)
    ·
      refine ⟨38188630847368817196017495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 407345395705267383424186613 38188630847368817196017495)
      ·
        refine ⟨57282946271053225794026243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38188630847368817196017495 57282946271053225794026243)
        ·
          refine ⟨85924419406579838691039365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57282946271053225794026243 85924419406579838691039365)
          ·
            refine ⟨16110828638733719754569881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85924419406579838691039365 16110828638733719754569881)
            ·
              refine ⟨12083121479050289815927411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16110828638733719754569881 12083121479050289815927411)
              ·
                refine ⟨18124682218575434723891117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12083121479050289815927411 18124682218575434723891117)
                ·
                  refine ⟨6796755831965788021459169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18124682218575434723891117 6796755831965788021459169)
                  ·
                    refine ⟨5097566873974341016094377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6796755831965788021459169 5097566873974341016094377)
                    ·
                      refine ⟨3823175155480755762070783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5097566873974341016094377 3823175155480755762070783)
                      ·
                        rfl

theorem cell23_7445607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_7445607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445607 prefixEnd_7445607 := by exact prefixLift 7445607
  have htrace : WordTrace (prefixWord ++ tailWord_7445607) baseStart_7445607 baseEnd_7445607 := by
    simpa [prefixWord, tailWord_7445607, baseEnd_7445607] using wordTrace_append hprefix tailTrace_7445607
  have hstable : (prefixWord ++ tailWord_7445607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445607).length < 2 ^ (prefixWord ++ tailWord_7445607).sum := by decide
  have hdescent : baseEnd_7445607 < baseStart_7445607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445674 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7445674 : Nat := 118140960795 + 7445674 * 2 ^ 59
def prefixEnd_7445674 : Nat := 4983230072969 + 3 ^ 40 * 7445674 * 2
def baseEnd_7445674 : Nat := 3823209558684606999932975

theorem tailTrace_7445674 : CollatzResearch.WordTrace tailWord_7445674 prefixEnd_7445674 3823209558684606999932975 := by
  unfold tailWord_7445674
  simp only [CollatzResearch.WordTrace]
  refine ⟨67891510206900548181370019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181044027218401461816986717 67891510206900548181370019)
  ·
    refine ⟨101837265310350822272055029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67891510206900548181370019 101837265310350822272055029)
    ·
      refine ⟨9547243622845389588005159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101837265310350822272055029 9547243622845389588005159)
      ·
        refine ⟨14320865434268084382007739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9547243622845389588005159 14320865434268084382007739)
        ·
          refine ⟨21481298151402126573011609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14320865434268084382007739 21481298151402126573011609)
          ·
            refine ⟨16110973613551594929758707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21481298151402126573011609 16110973613551594929758707)
            ·
              refine ⟨24166460420327392394638061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16110973613551594929758707 24166460420327392394638061)
              ·
                refine ⟨9062422657622772147989273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24166460420327392394638061 9062422657622772147989273)
                ·
                  refine ⟨6796816993217079110991955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9062422657622772147989273 6796816993217079110991955)
                  ·
                    refine ⟨10195225489825618666487933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6796816993217079110991955 10195225489825618666487933)
                    ·
                      refine ⟨3823209558684606999932975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10195225489825618666487933 3823209558684606999932975)
                      ·
                        rfl

theorem cell23_7445674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7445674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445674 prefixEnd_7445674 := by exact prefixLift 7445674
  have htrace : WordTrace (prefixWord ++ tailWord_7445674) baseStart_7445674 baseEnd_7445674 := by
    simpa [prefixWord, tailWord_7445674, baseEnd_7445674] using wordTrace_append hprefix tailTrace_7445674
  have hstable : (prefixWord ++ tailWord_7445674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445674).length < 2 ^ (prefixWord ++ tailWord_7445674).sum := by decide
  have hdescent : baseEnd_7445674 < baseStart_7445674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
